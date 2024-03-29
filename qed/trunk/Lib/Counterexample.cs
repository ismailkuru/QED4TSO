/*

****************************************************************************

QED: A Calculator for Atomic Actions
Copyright (C) 2008  Koç University, İstanbul, Turkey

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

****************************************************************************

*/

namespace QED
{

    using System;
    using System.IO;
    using System.Collections;
    using System.Collections.Generic;
    using Microsoft.Boogie;
    using BoogiePL;
    using System.Diagnostics;
    using Microsoft.Boogie.AbstractInterpretation;
    using AI = Microsoft.AbstractInterpretationFramework;
    using Microsoft.Contracts;
    using Type = Microsoft.Boogie.Type;
    using System.Text;
    using Microsoft.Boogie.Z3;
    using System.Text.RegularExpressions;
    using PureCollections;


    public class QEDCounterexample
    {
        internal enum TypeKind { Bool, Int, Record, RecordT, FieldMap, Map, UserDef, UserDefT, TypeParam }

        internal class TypeInfo
        {
            internal int Pid;
            internal string Name;
            internal TypeKind Kind;
            internal Record Record;
            internal TypeInfo[] Args;
            internal TypeInfo Return;

            internal TypeInfo(int pid)
            {
                this.Pid = pid;
            }
        } // end class TypeInfo

        internal class ObjectInfo
        {
            internal int Pid;
            internal string Name;
            internal TypeInfo Type;
            internal int intValue;
            internal bool boolValue;

            internal ObjectInfo(int pid)
            {
                this.Pid = pid;
            }
        } // end class ObjectInfo

        public class myErrorModel : ErrorModel
        {
            internal ErrorModel m;
            internal int pSize;
            internal int[] objectToType;
            internal TypeInfo[] partitionToType;
            internal List<ObjectInfo>[] partitionToObject;
            internal Hashtable nameToObject;
            internal TypeInfo boolTypeInfo;
            internal TypeInfo intTypeInfo;
            internal List<ObjectInfo[]> selectTuples;

            public myErrorModel(ErrorModel emodel) :
                base(emodel.identifierToPartition, emodel.partitionToIdentifiers, emodel.partitionToValue, emodel.valueToPartition, emodel.definedFunctions)
            {
                Debug.Assert(emodel != null);
                this.m = emodel;
                this.pSize = emodel.partitionToIdentifiers.Count;
                CollectData();
            }

            private void CollectData()
            {
                // partition to type
                partitionToType = new TypeInfo[pSize];
                objectToType = new int[pSize];
                for (int i = 0; i < pSize; ++i)
                    objectToType[i] = -1;
                List<List<int>> func = definedFunctions["type"];
                foreach (List<int> args in func)
                {
                    if (args.Count == 1) continue;
                    int pid_type = args[1];
                    objectToType[args[0]] = pid_type;
                    partitionToType[pid_type] = CollectType(pid_type);
                    Debug.Assert(partitionToType[pid_type] != null);
                }

                // get other types not referred to by "type()"
                // check maptype functions and types in the program
                for (int i = 0; i < pSize; ++i)
                {
                    // if not a type
                    if (partitionToType[i] == null)
                    {
                        List<string> idents = partitionToIdentifiers[i];
                        if (idents != null && idents.Count == 1)
                        {
                            if (idents[0].EndsWith("Type"))
                            {
                                partitionToType[i] = CollectType(i);
                                Debug.Assert(partitionToType[i] != null);
                            }
                        }
                    }
                }

                // partition to object
                partitionToObject = new List<ObjectInfo>[pSize];
                nameToObject = new Hashtable();
                for (int i = 0; i < pSize; ++i)
                {
                    // if not a type
                    if (partitionToType[i] == null)
                    {
                        partitionToObject[i] = CollectObject(i);
                        Debug.Assert(partitionToObject[i] != null);
                        foreach (ObjectInfo oinfo in partitionToObject[i])
                        {
                            nameToObject[oinfo.Name] = oinfo;
                        }
                    }
                }

                CollectSelectTuples();
            }

            private void CollectSelectTuples()
            {
                selectTuples = new List<ObjectInfo[]>();
                foreach (string funcName in definedFunctions.Keys)
                {
                    if (Regex.IsMatch(funcName, "^MapType[0-9]+Select$"))
                    {
                        // map type
                        List<List<int>> func = definedFunctions[funcName];
                        foreach (List<int> args in func)
                        {
                            // get the oinfo for the first argument, index
                            ObjectInfo oinfo = partitionToObject[args[1]][0];
                            Debug.Assert(oinfo != null && oinfo.Type != null);
                            if (oinfo.Type.Kind == TypeKind.Record || oinfo.Type.Kind == TypeKind.RecordT)
                            {
                                Debug.Assert(func.Count == 3);
                                foreach (ObjectInfo from in partitionToObject[args[1]])
                                {
                                    foreach (ObjectInfo to in partitionToObject[args[2]])
                                    {
                                        foreach (ObjectInfo via in partitionToObject[args[0]])
                                        {
                                            Debug.Assert(via.Type != null && via.Type.Kind == TypeKind.FieldMap);

                                            selectTuples.Add(new ObjectInfo[] { from, to, via });
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            private List<ObjectInfo> CollectObject(int pid_val)
            {
                List<ObjectInfo> oinfos = partitionToObject[pid_val];
                if (oinfos != null)
                {
                    return oinfos;
                }

                List<string> objectNames = partitionToIdentifiers[pid_val];
                if (objectNames == null || objectNames.Count == 0)
                {
                    return new List<ObjectInfo>(); // return a non-null but empty list
                }

                oinfos = new List<ObjectInfo>(objectNames.Count);

                bool isBool = objectNames[0] == "@true" || objectNames[0] == "@false";
                foreach (string objectName in objectNames)
                {
                    ObjectInfo oinfo = new ObjectInfo(pid_val);
                    oinfo.Name = objectName;
                    TypeInfo tinfo = null;

                    if (isBool)
                    {
                        // this is of bool type and the type info is assigned here
                        Debug.Assert(boolTypeInfo != null);
                        tinfo = boolTypeInfo;
                        objectToType[pid_val] = tinfo.Pid;
                        oinfo.boolValue = objectNames[0] == "@true" ? true : false;
                    }
                    else
                    {
                        int pid_type = objectToType[pid_val];
                        if (pid_type < 0)
                        {
                            // if no type has been assigned, then it must be an int constant
                            //int intVal = int.Parse(partitionToValue[pid_val].ToString());
                            tinfo = intTypeInfo;
                            objectToType[pid_val] = tinfo.Pid;
                            oinfo.intValue = GetIntValue(pid_val);
                        }
                        else
                        {
                            tinfo = partitionToType[pid_type];
                            Debug.Assert(tinfo != null && tinfo.Pid == pid_type);

                            if (tinfo.Kind == TypeKind.Int)
                            {
                                // get the int value
                                Debug.Assert(intTypeInfo != null && tinfo == intTypeInfo);
                                oinfo.intValue = GetIntValue(pid_val);
                            }
                        }
                    }
                    // set the type info object and add the object to the list
                    oinfo.Type = tinfo;
                    oinfos.Add(oinfo);
                }
                return oinfos;
            }

            private int GetIntValue(int pid)
            {
                List<List<int>> fun = definedFunctions["U_2_int"];
                foreach (List<int> args in fun)
                {
                    if (args.Count == 1) continue;
                    if (args[0] == pid)
                    {
                        return int.Parse(partitionToValue[args[1]].ToString());
                    }
                }
                // not found a corresponding entry in U_2_int, then return the value as int
                return int.Parse(partitionToValue[pid].ToString());
            }

            private TypeInfo CollectType(int pid_type)
            {
                TypeInfo tinfo = partitionToType[pid_type];
                if (tinfo != null)
                {
                    return tinfo;
                }

                tinfo = new TypeInfo(pid_type);

                // find out the information

                List<string> pti = partitionToIdentifiers[pid_type];
                if (pti != null && pti.Count > 0)
                {
                    Debug.Assert(pti.Count == 1);
                    string ident = pti[0];
                    // parse the type
                    if (ident == "intType")
                    {
                        tinfo.Name = "int";
                        tinfo.Kind = TypeKind.Int;
                        intTypeInfo = tinfo;
                    }
                    else if (ident == "boolType" || ident == "booleanType")
                    {
                        tinfo.Name = "bool";
                        tinfo.Kind = TypeKind.Bool;
                        boolTypeInfo = tinfo;
                    }
                    else
                    {
                        if (ident.EndsWith("Type"))
                        {
                            tinfo.Name = ident.Substring(0, ident.LastIndexOf("Type"));

                            // check if record type
                            tinfo.Record = ProofState.GetInstance().GetRecord(tinfo.Name);
                            if (tinfo.Record != null)
                            {
                                tinfo.Kind = TypeKind.Record;
                            }
                            else
                            {
                                tinfo.Kind = TypeKind.UserDef;
                            }
                        }
                        else
                        {
                            // type parameter, no Type at the end of the name
                            tinfo.Kind = TypeKind.TypeParam;
                        }
                    }
                }
                else
                {
                    // no identifier is associated, so either map or constructed type
                    // go over the functions that construct types
                    bool found = false;
                    foreach (string funcName in definedFunctions.Keys)
                    {
                        if (found) break;
                        if (Regex.IsMatch(funcName, "^MapType[0-9]+Type$"))
                        {
                            // map type
                            List<List<int>> func = definedFunctions[funcName];
                            foreach (List<int> args in func)
                            {
                                if (found) break;
                                if (args.Count == 1) continue;
                                if (args[args.Count - 1] != pid_type) continue;

                                found = true;
                                tinfo.Kind = TypeKind.Map;
                                if (args.Count >= 3)
                                {
                                    tinfo.Name = "[";
                                    tinfo.Args = new TypeInfo[args.Count - 1];
                                    for (int i = 0; i < args.Count - 2; ++i)
                                    {
                                        if (i != 0) tinfo.Name += ",";
                                        tinfo.Args[i] = CollectType(args[i]);
                                        Debug.Assert(tinfo.Args[i] != null);
                                        tinfo.Name += tinfo.Args[i].Name;
                                    }
                                    tinfo.Name += "]";
                                    tinfo.Return = CollectType(args[args.Count - 2]);
                                    Debug.Assert(tinfo.Return != null);
                                    tinfo.Name += tinfo.Return.Name;

                                    // check the first parameter, it can be a record
                                    TypeInfo arg0info = tinfo.Args[0];
                                    if (arg0info.Kind == TypeKind.Record || arg0info.Kind == TypeKind.RecordT)
                                    {
                                        GetFieldMapType(tinfo);
                                    }
                                }
                                else // count is 2
                                {
                                    Debug.Assert(args.Count == 2);
                                    // missing arguments, this is due to parameterized types
                                    // find out the arguments using the identifiers
                                    GetFieldMapType(tinfo);
                                }
                            }
                        }
                        else if (Regex.IsMatch(funcName, "Type$")) // try to find type constructors, e.g., Queue T
                        {
                            string tname = funcName.Substring(0, funcName.LastIndexOf("Type"));
                            Debug.Assert(!tname.StartsWith("MapType"));
                            // recordt or userdeft
                            // try to find a matching record
                            Record record = ProofState.GetInstance().GetRecord(tname);

                            List<List<int>> func = definedFunctions[funcName];
                            foreach (List<int> args in func)
                            {
                                if (found) break;
                                if (args.Count == 1) continue;
                                if (args[args.Count - 1] != pid_type) continue;

                                found = true;
                                tinfo.Name = tname;
                                if (record == null)
                                {
                                    tinfo.Kind = TypeKind.UserDefT;
                                }
                                else
                                {
                                    tinfo.Kind = TypeKind.RecordT;
                                }
                                tinfo.Args = new TypeInfo[args.Count];
                                for (int i = 0; i < args.Count - 1; ++i)
                                {
                                    tinfo.Args[i] = CollectType(args[i]);
                                    Debug.Assert(tinfo.Args[i] != null);
                                }

                            }
                        }
                    }
                    Debug.Assert(found);
                }
                return tinfo;
            }

            // fill in tinfo as fieldmap using the identifiers
            private void GetFieldMapType(TypeInfo tinfo)
            {
                List<List<int>> instances = definedFunctions["type"];
                foreach (List<int> targs in instances)
                {
                    if (targs.Count == 1) continue;
                    if (targs[1] != tinfo.Pid) continue;

                    int pid_val = targs[0];
                    List<string> idents = partitionToIdentifiers[pid_val];
                    if (idents != null && idents.Count > 0)
                    {
                        // find one
                        string ident = idents[0];
                        if (ident.EndsWith("_prime"))
                        {
                            ident = ident.Substring(0, ident.LastIndexOf("_prime"));
                        }
                        int idx = ident.IndexOf("_");
                        Debug.Assert(idx >= 0);
                        string recordname = ident.Substring(0, idx);
                        string fieldname = ident.Substring(idx + 1);

                        // check records
                        foreach (Record record in ProofState.GetInstance().Records)
                        {
                            if (record.Name == recordname)
                            {
                                Variable fieldMap = record.GetFieldMap(fieldname);
                                if (fieldMap != null)
                                {
                                    // got it
                                    tinfo.Kind = TypeKind.FieldMap;
                                    tinfo.Name = fieldMap.TypedIdent.Type.ToString();
                                    tinfo.Record = record;
                                    //tinfo.Field = fieldname;
                                    break;
                                }
                            }
                        }
                    }
                }

                // we should have found it!
                Debug.Assert(tinfo.Kind == TypeKind.FieldMap);
            }

            public override string ToString()
            {
                StringWriter sw = new StringWriter();
                this.m.Print(sw);
                return sw.ToString();
            }
        }

        static public myGraph Extract(InvariantCheck invCheck)
        {
            AtomicBlock atomicBlock = invCheck.atomicBlock;
            ProcedureState procState = atomicBlock.procState;

            // get all the variables
            ProofState proofState = ProofState.GetInstance();

            myErrorModel model = new myErrorModel(invCheck.errModel);

            Output.AddLine(model.ToString());
            // parse the counterexample
            myGraph G = new myGraph("Counterexample");

            // collect the program variables
            Set<Variable> vars = new Set<Variable>();
            foreach (Variable v in proofState.globalVars.Values)
            {
                vars.Add(v);
            }

            foreach (Variable v in procState.localVars.Values)
            {
                vars.Add(v);
            }

            foreach (Constant v in proofState.Constants)
            {
                vars.Add(v);
            }

            // create nodes
            foreach (Variable v in vars)
            {
                // get the value from the model
                if (model.nameToObject.ContainsKey(v.Name))
                {
                    ObjectInfo oinfo = model.nameToObject[v.Name] as ObjectInfo;
                    TypeInfo tinfo = oinfo.Type;
                    if (tinfo.Kind == TypeKind.Bool)
                    {
                        Debug.Assert(oinfo.Name == v.Name);
                        string label = oinfo.Name + ":bool = " + oinfo.boolValue;
                        myNode node = new myNode(oinfo.Pid.ToString(), label, oinfo, myColor.Yellow, myColor.Black, myColor.Black, myShape.Circle);
                        if (G.ContainsNode(oinfo.Pid.ToString())) node.Id += "_" + v.Name;
                        G.Add(node);

                    }
                    else if (tinfo.Kind == TypeKind.Int)
                    {
                        Debug.Assert(oinfo.Name == v.Name);
                        string label = oinfo.Name + ":int = " + oinfo.intValue;
                        myNode node = new myNode(oinfo.Pid.ToString(), label, oinfo, myColor.Yellow, myColor.Black, myColor.Black, myShape.Circle);
                        if (G.ContainsNode(oinfo.Pid.ToString())) node.Id += "_" + v.Name;
                        G.Add(node);

                    }
                    else if (tinfo.Kind == TypeKind.UserDef || tinfo.Kind == TypeKind.UserDefT)
                    {
                        Debug.Assert(oinfo.Name == v.Name);
                        string label = oinfo.Name + ":" + tinfo.Name;
                        myNode node = new myNode(oinfo.Pid.ToString(), label, oinfo, myColor.Yellow, myColor.Black, myColor.Black, myShape.Circle);
                        if (G.ContainsNode(oinfo.Pid.ToString())) node.Id += "_" + v.Name;
                        G.Add(node);
                    }
                    else if (tinfo.Kind == TypeKind.Record || tinfo.Kind == TypeKind.RecordT)
                    {
                        Debug.Assert(oinfo.Name == v.Name);
                        string label = oinfo.Name + ":" + tinfo.Name;
                        myNode node = new myNode(oinfo.Pid.ToString(), label, oinfo, myColor.Yellow, myColor.Black, myColor.Black, myShape.Circle);
                        if (G.ContainsNode(oinfo.Pid.ToString())) node.Id += "_" + v.Name;
                        G.Add(node);
                    }
                    else if (tinfo.Kind == TypeKind.Map)
                    {
                        Debug.Assert(oinfo.Name == v.Name);
                        string label = oinfo.Name + ":" + tinfo.Name;
                        myNode node = new myNode(oinfo.Pid.ToString(), label, oinfo, myColor.Yellow, myColor.Black, myColor.Black, myShape.Circle);
                        if (G.ContainsNode(oinfo.Pid.ToString())) node.Id += "_" + v.Name;
                        G.Add(node);
                    }
                }
            }

            // add edges for fields and map indices
            foreach (ObjectInfo[] edges in model.selectTuples)
            {
                // from: 0, to: 1, via: 2
                ObjectInfo from = edges[0];
                ObjectInfo to = edges[1];
                ObjectInfo via = edges[2];

                if (G.ContainsNode(from.Pid.ToString()) && G.ContainsNode(to.Pid.ToString()))
                {
                    //G.AddEdge(from.Pid.ToString(), to.Pid.ToString(), via.Type.Field);
                }
            }

            return G;
        }

    } // end class Counterexample


}// end namespace QED
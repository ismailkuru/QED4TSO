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

namespace QED {

using System;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using Microsoft.Boogie;
using BoogiePL;
using System.Diagnostics;


    public abstract class Annotation
    {
        public string UniqueId;
        public bool IsEnabled;
        public Expr Assertion;
        public Cmd Command;
        public AtomicBlock Block;
        public Expr AnnotAssert;
        public Expr AnnotTrans;
        public Expr Error;
        public Expr PError;

        public Annotation(string i, Expr a, Cmd c, AtomicBlock b, Expr err, Expr perr)
        {
            this.IsEnabled = true;
            this.UniqueId = i;
            this.Assertion = a;
            this.Command = c;
            this.Block = b;
            this.AnnotAssert = null;
            this.AnnotTrans = null;
            this.Error = err;
            this.PError = perr;
        }

        public abstract void AnnotatePred();

        public abstract void AnnotateCode();
        
        virtual public void Disable()
        {
            Output.AddLine("Disabling " + this.Block.Label);

            Debug.Assert(this.IsEnabled);
            this.IsEnabled = false;

            AnnotatePred();
        }

        virtual protected void RemoveAnnotation()
        {
            if (this.AnnotAssert != null)
            {
                Expr annotExpr = this.Block.PopAssertion();
                Debug.Assert(annotExpr == this.AnnotAssert);
            }

            if (this.AnnotTrans != null)
            {
                Expr annotExpr = this.Block.PopTransition();
                Debug.Assert(annotExpr == this.AnnotTrans);
            }
        }

    }


public class EntryAnnotation : Annotation
{
    public EntryAnnotation(string i, Expr a, Cmd c, AtomicBlock b, Expr err, Expr perr)
        : base(i, a, c, b, err, perr)
    {
        
	}
	
	public override void AnnotatePred() {

        RemoveAnnotation();

        if (IsEnabled)
        {
            this.AnnotAssert = LabeledExprHelper.AuxAssert(UniqueId, Block, Assertion);
            Block.PushAssertion(this.AnnotAssert);            
        }
        else
        {
            this.AnnotAssert = null;
        }

        this.AnnotTrans = Expr.Eq(this.Error, this.PError);
        Block.PushTransition(this.AnnotTrans);
	}
	
	public override void AnnotateCode() {

        RemoveAnnotation();
        
        if(this.IsEnabled) {
			Output.LogLine("Annotating atomic block " + Block.Label);
            
            Debug.Assert(this.Command != null);
            this.Block.InstrumentEntry(new CmdSeq(this.Command));
		}
	}
}

public class ExitAnnotation : Annotation
{
    public ExitAnnotation(string i, Expr a, Cmd c, AtomicBlock b, Expr err, Expr perr)
        : base(i, a, c, b, err, perr)
    {

    }

    public override void AnnotatePred()
    {

        RemoveAnnotation();

        Expr preservesError = Expr.Eq(this.Error, this.PError);
        Expr setsError = Expr.Eq(this.PError, Expr.True);

        if (IsEnabled)
        {
            Expr labeledAssert = LabeledExprHelper.NegAuxAssert(UniqueId, Block, Assertion);
            this.AnnotTrans = Expr.Or(Expr.And(Assertion, preservesError),
                                      Expr.And(labeledAssert, setsError));            
        }
        else
        {
            this.AnnotTrans = preservesError;
        }
        Block.PushTransition(this.AnnotTrans);

        this.AnnotAssert = null;
    }

    public override void AnnotateCode()
    {

        RemoveAnnotation();

        if (this.IsEnabled)
        {
            Output.LogLine("Annotating atomic block " + Block.Label);

            Debug.Assert(this.Command != null);
            this.Block.InstrumentExit(new CmdSeq(this.Command));
        }
    }
}


public class AnnotationSet {
	private Dictionary<string,Annotation> map;
	private int nextId;
    private Expr errExpr;
    private Expr perrExpr;
	
	public AnnotationSet(Expr err, Expr perr) {
		this.nextId = 0;
		this.map = new Dictionary<string,Annotation>();
        this.errExpr = err;
        this.perrExpr = perr;
	}

    public void Clear()
    {
        this.map.Clear();
    }
	
	public void AddForEntry(Expr a, Cmd c, AtomicBlock b) {
        string id = "Annot" + nextId.ToString();
        map.Add(id, new EntryAnnotation(id, a, c, b, this.errExpr, this.perrExpr));
        ++nextId;
	}

    public void AddForExit(Expr a, Cmd c, AtomicBlock b)
    {
        string id = "Annot" + nextId.ToString();
        map.Add(id, new ExitAnnotation(id, a, c, b, this.errExpr, this.perrExpr));
        ++nextId;
	}

    //public void AddForTransition(Expr a, AtomicBlock b)
    //{
    //    Add(a, null, b, true);
    //}
		
	public void Disable(Set<string> idset) {
		foreach(string id in idset) {
            if (map.ContainsKey(id))
            {
                Annotation annot = map[id];
                annot.Disable();
            }
		}
	}
	
    //public void Disable(Set<AtomicBlock> blocks) {
    //    foreach(Annotation annot in map.Values) {
    //        if(blocks.Contains(annot.Block)) {
    //            annot.Disable();
    //        }
    //    }
    //}
	
	public void AnnotateCodes() {
		foreach(Annotation annot in map.Values) {
			annot.AnnotateCode();
		}
	}
	
	public void AnnotatePreds() {
		foreach(Annotation annot in map.Values) {
			annot.AnnotatePred();
		}
	}
	
	public VariableSeq GetModifiedVars() {
        VariableSeq modVars = new VariableSeq();
		
		foreach(Annotation annot in map.Values) {
			if(annot.IsEnabled) {
                Debug.Assert(annot.Command != null);
                annot.Command.AddAssignedVariables(modVars);
			}
		}
		
		return modVars;
	}

    public Set<AtomicBlock> GetAnnotatedBlocks()
    {
        Set<AtomicBlock> blocks = new Set<AtomicBlock>();
		
		foreach(Annotation annot in map.Values) {
			if(annot.IsEnabled) {
				blocks.Add(annot.Block);
			}
		}
		
		return blocks;
	}



    internal void Init(List<AtomicBlock> atomicBlocks, Expr assertion, Cmd cmd, bool isForEntry)
    {
        StmtDuplicator duplicator = new StmtDuplicator();

        foreach (AtomicBlock atomicBlock in atomicBlocks)
        {
            if (isForEntry)
            {
                AddForEntry(assertion, duplicator.Visit(cmd) as Cmd, atomicBlock);
            }
            else
            {
                AddForExit(assertion, duplicator.Visit(cmd) as Cmd, atomicBlock);
            }
        }
    }

    internal void Init(List<AtomicBlock> atomicBlocks, Set<AtomicBlock> disabledBlocks, Expr assertion, Cmd cmd, bool isForEntry)
    {
        Init(atomicBlocks, assertion, cmd, isForEntry);

        // do not call Disable
        foreach (AtomicBlock atomicBlock in disabledBlocks)
        {
            foreach (Annotation annot in map.Values)
            {
                if (annot.Block.Label == atomicBlock.Label)
                {
                    annot.IsEnabled = false;
                }
            }
        }
    }
}


} // end namespace QED
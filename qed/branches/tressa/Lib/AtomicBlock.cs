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
using System.Text;

    public abstract class APLBlock : Absy
    {
        //protected int pc;

        public APLStmt parentApl;

        public ProcedureState procState;

        public Dictionary<string, Block> blocks;

        public Block startBlock;

        public Stack<Expr> transitions;
        public Stack<Expr> assertions;

        //protected Expr transitionPredicate = null;

        public abstract MoverType Mover { get; set; }

        public abstract string Label { get; }

        public abstract myNode GraphView { get; }

        public abstract string DotView { get; }

        public string UniqueLabel { get { return Label + "@" + procState.Name; } }

        public List<Block> Blocks
        {
            get
            {
                List<Block> blks = new List<Block>();
                foreach (Block b in blocks.Values)
                {
                    blks.Add(b);
                }
                return blks;
            }
        }

        public virtual string BlockStr
        {
            get
            {
                StringWriter strw = new StringWriter();

                using (TokenTextWriter writer = new TokenTextWriter(strw))
                {
                    foreach (Block block in blocks.Values)
                    {
                        block.Emit(writer, 0);
                    }
                }
                strw.Flush();

                return strw.ToString();
            }
        }

        public APLBlock(ProcedureState pstate, List<Block> blks, Block sblock, APLStmt parent)
            : base(blks[0].tok)
        {
            //this.pc = this.UniqueId;

            this.parentApl = parent;

            this.procState = pstate;

            this.startBlock = sblock;

            this.blocks = new Dictionary<string,Block>();
            foreach (Block b in blks)
            {
                this.blocks.Add(b.Label, b);
            }

            this.transitions = new Stack<Expr>();
            this.assertions = new Stack<Expr>();
        }

        //public int Pc
        //{
        //    get
        //    {
        //        return this.pc;
        //    }
        //    set
        //    {
        //        this.pc = value;
        //    }
        //}


        public void InstrumentEntry(CmdSeq cmds)
        {
            CmdSeq newCmds = new CmdSeq();
            newCmds.AddRange(cmds);
            newCmds.AddRange(startBlock.Cmds);
            startBlock.Cmds = newCmds;

            // instrument parent
            CodeTransformations.InstrumentEntry(parentApl.body, cmds, true);

            this.MarkAsTransformed();
        }

        public void InstrumentExit(CmdSeq cmds)
        {
            foreach (Block block in ExitBlocks)
            {
                //Debug.Assert(block.Cmds.Length > 0); // TODO: why did I put this?
                block.Cmds.AddRange(cmds);
            }

            // instrument parent
            CodeTransformations.InstrumentExit(parentApl.body, cmds, true, null);

            this.MarkAsTransformed();
        }

        public void AbstractRead(Variable absVar, Expr expr)
        {
            BeginAbstractCmd abstractCmd = new BeginAbstractCmd(Token.NoToken, absVar, true, expr);

            InstrumentEntry(new CmdSeq(abstractCmd));

            EndAbstractCmd endabstractCmd = new EndAbstractCmd(Token.NoToken, absVar);

            InstrumentExit(new CmdSeq(endabstractCmd));
        }

        public void AbstractWrite(Variable absVar, Expr expr)
        {
            BeginAbstractCmd abstractCmd = new BeginAbstractCmd(Token.NoToken, absVar, false, expr);

            InstrumentExit(new CmdSeq(abstractCmd));
        }

        public Set<APLBlock> Successors
        {
            get
            {
                Set<APLBlock> successors = new Set<APLBlock>();

                Set<Block> exitBlocks = ExitBlocks;

                foreach (Block block in exitBlocks)
                {
                    GotoCmd gotoCmd = block.TransferCmd as GotoCmd;
                    if (gotoCmd != null)
                    {
                        foreach (Block nextBlock in gotoCmd.labelTargets)
                        {
                            APLBlock successor = procState.LookupAPLBlockStarts(nextBlock);
                            successors.Add(successor);
                        }
                    }
                    else
                    {
                        ThrowCmd thrw = block.TransferCmd as ThrowCmd;
                        if (thrw != null && thrw.catchStmt != null)
                        {
                            APLBlock successor = procState.LookupAPLBlockStarts(thrw.catchStmt.GotoBlock);
                            successors.Add(successor);
                        }
                    }
                }
                return successors;
            }
        }

        public Set<APLBlock> Predecessors
        {
            get
            {
                Set<APLBlock> predecessors = new Set<APLBlock>();
                foreach (Block block in startBlock.Predecessors)
                {
                    APLBlock aplBlock = procState.LookupAPLBlockContains(block);
                    if (!predecessors.Contains(aplBlock))
                    {
                        predecessors.Add(aplBlock);
                    }
                }
                return predecessors;
            }
        }

        public Set<Block> ExitBlocks
        {
            get
            {
                Set<Block> exitBlocks = new Set<Block>();
                foreach (Block block in blocks.Values)
                {
                    GotoCmd gotoCmd = block.TransferCmd as GotoCmd;
                    if (gotoCmd != null)
                    {
                        int numExists = 0;
                        foreach (Block successor in gotoCmd.labelTargets)
                        {
                            if (!this.Contains(successor))
                            {
                                exitBlocks.Add(block);
                                numExists += 1;
                            }
                        }
                        Debug.Assert(numExists == 0 || numExists == gotoCmd.labelTargets.Length);
                    }
                    else
                    {
                        ThrowCmd thrw = block.TransferCmd as ThrowCmd;
                        if (thrw != null)
                        {
                            if (thrw.catchStmt == null || !this.Contains(thrw.catchStmt.GotoBlock))
                            {
                                exitBlocks.Add(block);
                            }
                        }
                        else
                        {
                            exitBlocks.Add(block);
                        }
                    }
                }

                return exitBlocks;
            }
        }
    
        public bool Contains(Block block)
        {
            return blocks.ContainsKey(block.Label);
        }

        virtual public Expr TransitionPredicate
        {
            get
            {
                //if (transitionPredicate == null)
                //{
                    return ComputeTransitionPredicate(TPGenOptions.ComputeTPred);
                //}
                //return transitionPredicate;
            }
            //set
            //{
            //    transitionPredicate = value;
            //}
        }


        //virtual public Expr TransitionPredicateSeq
        //{
        //    get
        //    {
        //        return TransitionPredicate;
        //    }
        //}

        virtual public Expr GatePredicate(Expr P)
        {

            return ComputeGatePredicate(TPGenOptions.ComputeWPre(P));

        }

        // for tressa
        virtual public Expr ExitPredicate(Expr P)
        {
         
            return ComputeExitPredicate(TPGenOptions.ComputeSPost(P));
        
        }

        //virtual public Expr GatePredicateSeq(Expr P)
        //{
        //    return GatePredicate(P);
        //}

        public void MarkAsTransformed()
        {
            // this.TransitionPredicate = null;
        }

        virtual public Expr ComputeTransitionPredicate(TPGenOptions options)
        {
            Expr trp = new TPGenerator(this).Compute(options);

            // add transitions if exist
            if (this.transitions.Count > 0)
            {
                foreach (Expr annot in this.transitions)
                {
                    trp = Expr.And(trp, annot);
                }
            }

            return trp;
        }

        virtual public Expr ComputeGatePredicate(TPGenOptions options)
        {
            Expr wp = new TPGenerator(this).Compute(options);

            // add transitions if exist
            if (this.assertions.Count > 0)
            {
                foreach (Expr annot in this.assertions)
                {
                    wp = Expr.And(wp, annot);
                }
            }

            return wp;
        }

        // for tressa; copied from ComputeGatePredicate
        virtual public Expr ComputeExitPredicate(TPGenOptions options)
        {
            Expr sp = new TPGenerator(this).ComputeSP(options, options.preCondforSP);

/* i am not sure about the following part
            // add transitions if exist
            if (this.assertions.Count > 0)
            {
                foreach (Expr annot in this.assertions)
                {
                    sp = Expr.And(sp, annot);
                }
            }
*/

            return sp;
        }

        //public Expr AnnotateTransitionPredicate(Expr annotExpr)
        //{
        //    this.transitionPredicate = Expr.And(this.TransitionPredicate, annotExpr);

        //    return this.transitionPredicate;
        //}

        public Set<Variable> ComputeWriteSet()
        {
            TPGenerator tpgen = new TPGenerator(this);
            tpgen.Compute(TPGenOptions.ComputeRWSets);
            return tpgen.WriteSet;
        }

        public Set<Variable> ComputeReadSet()
        {
            TPGenerator tpgen = new TPGenerator(this);
            tpgen.Compute(TPGenOptions.ComputeRWSets);
            return tpgen.ReadSet;
        }

        public bool ReadsFromVar(Variable var)
        {
            return ComputeReadSet().Contains(var);
        }

        public bool WritesToVar(Variable var)
        {
            return ComputeWriteSet().Contains(var);
        }

        // TODO: handle while loops, have this method for statements not for blocks
        virtual public MoverType ComputeComposedMover()
        {
            MoverType nextMover = null;
            MoverType succMover = null;

            if (Successors.Count == 0)
            {
                return this.Mover;
            }

            foreach (AtomicBlock successor in Successors)
            {
                nextMover = successor.ComputeComposedMover();
                if (nextMover == null)
                {
                    succMover = null;
                    break;
                }
                if (succMover != null)
                {
                    succMover = MoverType.ComposeCho(succMover, nextMover);
                }
                else
                {
                    succMover = nextMover;
                }
            }

            return MoverType.ComposeSeq(this.Mover, succMover);
        }

        public void PushTransition(Expr expr)
        {
            MarkAsTransformed();
            this.transitions.Push(expr);
        }

        public Expr PopTransition()
        {
            MarkAsTransformed();
            return this.transitions.Pop();
        }

        public void PushAssertion(Expr expr)
        {
            MarkAsTransformed();
            this.assertions.Push(expr);
        }

        public Expr PopAssertion()
        {
            MarkAsTransformed();
            return this.assertions.Pop();
        }

        public Expr AnnotAssertions
        {
            get
            {
                Expr annot = Expr.True;
                if (this.assertions.Count > 0)
                {
                    foreach (Expr assertion in this.assertions)
                    {
                        annot = Expr.And(annot, assertion);
                    }
                }
                return annot;
            }
        }

        public void InheritAnnotations(AtomicBlock atomicBlock)
        {
            if (this.transitions.Count > 0)
            {
                foreach (Expr annotExpr in this.transitions)
                {
                    PushTransition(annotExpr);
                }
            }
        }


        public override void Resolve(ResolutionContext rc)
        {
            // no need for now
            /*
            foreach(Block! block in blocks) {
                block.Resolve(rc);	
            } 
            */
        }

        public override void Typecheck(TypecheckingContext tc)
        {
            // no need for now
            /*
            foreach(Block! block in blocks) {
                block.Typecheck(tc);	
            } 
            */
        }

    }

    public class AtomicBlock : APLBlock
    {

    public AtomicStmt parent;

    protected MoverType mover;

	//---------------------------------------------
    // constranint partitioning
    public Expr TrapPredicate
    {
        get
        {
            return parent.trapPredicate;
        }

        set
        {
            parent.trapPredicate = value;
        }
    }
    //---------------------------------------------


    public AtomicBlock(ProcedureState pstate, List<Block> blks, Block sblock, AtomicStmt stmt)
        : base(pstate, blks, sblock, stmt)
    {
        this.parent = stmt as AtomicStmt;

        this.mover = MoverType.FromEnum(parent.mover);
    }

    public override string Label
    {
        get { return parent.label; }
    }

    public override MoverType Mover
    {
        get
        {
            return this.mover;
        }
        set
        {
            this.mover = value;
            parent.mover = value.ToEnum();
        }
    }
    
    //virtual public bool IsClonable {
    //    get {
    //        // do not clone Enter and Exit Blocks
    //        return parent.isClonable && (this.Successors.Count > 0) && (this.startBlock.Predecessors.Length > 0);
    //    }
    //    set {
    //        parent.isClonable = value;
    //    }
    //}
    
    //virtual public bool CanMerge {
    //    get {
    //        return parent.canMerge;
    //    }
    //    set {
    //        parent.canMerge = value;
    //    }
    //}

    override public Absy Clone()
    {
        return Clone(new Dictionary<Block, Block>());
    }
    
    virtual public AtomicBlock Clone(Dictionary<Block, Block> map) {
		
		int c = parent.nextCloneId++;
		
		List<Block> newBlocks = new List<Block>();
		
		foreach(Block block in blocks.Values) {
			Block newblock = new Block(Token.NoToken, block.Label + "_" + c.ToString(), new CmdSeq(block.Cmds), block.TransferCmd); 
			newBlocks.Add(newblock);
			map.Add(block, newblock);
		}
		
		foreach(Block newblock in newBlocks) {
			TransferCmd newTransferCmd;
			GotoCmd gotoCmd = newblock.TransferCmd as GotoCmd;
			if(gotoCmd != null) {
				BlockSeq newTargets = new BlockSeq();
				foreach(Block succ in gotoCmd.labelTargets) {
					if(this.Contains(succ)) {
						Debug.Assert(map.ContainsKey(succ));
						newTargets.Add((Block)map[succ]);
					} else {
						newTargets.Add(succ);
					}
				}
				newTransferCmd = new GotoCmd(Token.NoToken, newTargets);
			} else {
				newTransferCmd = new ReturnCmd(Token.NoToken);
			}
			newblock.TransferCmd = newTransferCmd;
		}
		
		return new AtomicBlock(procState, newBlocks, (Block)map[this.startBlock], this.parent);
    }

    
    public override myNode GraphView
    {
		get {
		
			StringBuilder strb = new StringBuilder();

			strb.Append(Label).Append(" : ").Append(Mover == null ? "?" : Mover.ToString()).Append("\\n");
            strb.Append(BlockStr);
			
			myNode node = new myNode(Label, strb.ToString(), this, myColor.Yellow, myColor.Black, myColor.Blue, myShape.Box);

            foreach (APLBlock aplblock in this.Successors)
            {
                node.Edges.Add(aplblock.Label);
            }
			
			return node;
		}
	}

    public override string DotView
    {
		get {
			string label = "AtomicBlock: " + Label + " : " + mover.ToString() + "\\n";
			
			label += this.BlockStr;
			
			label = label.ToString().Replace("\r\n", "\\n").Replace("\t", " ");
			
			string output = this.Label + " [shape=box,label=\"" + label + "\"];";
			// Output.LogLine("Output: " + output);
			return output;
		}
    }

    //public bool IsReflexive(Expr inv)
    //{
    //    Expr gate = this.GatePredicate(Expr.True);
    //    Expr trans = this.TransitionPredicate;

    //    return GatedActionHelper.IsReflexive(this.procState, inv, gate, trans);
    //}

    public bool IsReflexive()
    {
        Expr inv = ProofState.GetInstance().InvariantForProc(procState);

        //--------------------------------------------------
        // create the skip statement
        StmtList skipStmt = Qoogie.SkipStmt;

        //--------------------------------------------------
        BigBlock parentBB = Qoogie.GetParentBigBlock(this.parent);

        AtomicStmt skipAtom;
        IdentifierExprSeq origModifies;
        CodeTransformations.MakeBranch(procState, parentBB, skipStmt, new VariableSeq(), out skipAtom, out origModifies);

        //--------------------------------------------------
        AtomicBlock skipBlock = procState.GetAtomicBlock(skipAtom.label);
        bool result = skipBlock.IsAbstractedBy(inv, this, new VariableSeq());

        CodeTransformations.UndoMakeBranch(procState, parentBB, false, new VariableSeq(), origModifies);
        
        procState.MarkAsTransformed();

        return result;
    }



    public bool IsInvariant(Expr inv)
    {
        Expr gate = this.GatePredicate(Expr.True);
        Expr trans = this.TransitionPredicate;

        Set<Expr> failed = GatedActionHelper.IsInvariant(inv, gate, trans);
        if (failed == null)
        {
            return true;
        }

        StringBuilder strb = new StringBuilder();
        strb.AppendLine(">> Begin failed invariants");
        foreach(Expr e in failed) {
            strb.AppendLine(Output.ToString(e));
        }
        strb.AppendLine(">> End failed invariants");
        Output.AddLine(strb.ToString());

        return false;
    }    

    public bool IsAbstractedBy(Expr inv, AtomicBlock abstBlock, VariableSeq auxVars)
    {
        // set the label of abstBlock to the label of this block
        //int tmpId = abstBlock.Pc;
        //abstBlock.Pc = this.Pc;

        TPGenerator thisTPGen = new TPGenerator(this, false);
        TPGenerator thatTPGen = new TPGenerator(abstBlock, false);

        bool result = Logic.CheckSimulation(inv, thisTPGen, thatTPGen, auxVars);

        //abstBlock.Pc = tmpId;

        return result;
    }


    public void Relax(CmdSeq assertions, bool makeAssume)
    {
        // remove discharged assertions from the atomic block
        // remove failed commands
        foreach (Block b in this.Blocks)
        {
            b.Cmds = CodeTransformations.RelaxCmdSeq(b.Cmds, assertions, makeAssume);
        }

        // now remove the assertions from the statement
        CodeTransformations.RelaxStmt(parent.body, assertions, makeAssume);
        MarkAsTransformed();
    }

    // for tressa
    public void RelaxTressa()
    {
        // remove discharged tressa claims from the atomic block
        // remove failed commands
        foreach (Block b in this.Blocks)
        {
            b.Cmds = CodeTransformations.RelaxCmdSeqForTressa(b.Cmds);
        }

        // now remove the assertions from the statement
        CodeTransformations.RelaxStmtForTressa(parent.body);
        MarkAsTransformed();
    }

}

    public class CallBlock : APLBlock
    {

        protected CallStmt parent;

        public string CalleeName
        {
            get
            {
                return CallCmd.Proc.Name;
            }
        }

        public CallCmd CallCmd
        {
            get
            {
                return parent.cmd;
            }
        }

        public ProcedureState Callee
        {
            get
            {
                return ProofState.GetInstance().GetProcedureState(CalleeName);
            }
        }

        public CallBlock(ProcedureState pstate, List<Block> blocks, Block sblock, CallStmt stmt)
            : base(pstate, blocks, sblock, stmt)
        {

            this.parent = stmt;
        }

        //public AtomicBlock GetVerifiedBlock()
        //{

        //    Debug.Assert(this.blocks.Count == 1);

        //    // replace call command with the gated action
        //    CmdSeq cmds = this.startBlock.Cmds;
        //    CmdSeq newCmds = new CmdSeq();

        //    for (int i = 0, n = cmds.Length; i < n; ++i)
        //    {
        //        CallCmd callCmd = cmds[i] as CallCmd;
        //        if (callCmd != null)
        //        {
        //            GatedAction gact = this.callee.SpecAtCall(this.procState, callCmd);
        //            newCmds.Add(gact);
        //        }
        //        else
        //        {
        //            newCmds.Add(cmds[i]);
        //        }
        //    }
        //    this.startBlock.Cmds = newCmds;

        //    return new AtomicBlock(procState, this.startBlock);
        //}

        override public MoverType Mover
        {
            get
            {
                return Callee.Mover;
            }
            set
            {
                Debug.Assert(false, "Mover type of the call block will be taken from the procedure specification!");
            }
        }


        //#region Transition predicates
        //override public Expr TransitionPredicate
        //{
        //    get
        //    {
        //        Debug.Assert(false, "This should not be used !");
        //        return Expr.True;
        //    }
        //}

        //override public Expr GatePredicate(Expr P)
        //{
        //    Debug.Assert(false, "This should not be used !");
        //    return Expr.True;
        //}
        //#endregion Transition predicates


        override public myNode GraphView
        {
            get
            {
                StringBuilder strb = new StringBuilder();

                strb.Append(Label + " : " + (Mover == null ? "-" : Mover.ToString()) + "\\n");
                strb.Append(BlockStr);

                myNode node = new myNode(Label, strb.ToString(), this.BlockStr, myColor.Black, myColor.White, myColor.Blue, myShape.Box);

                foreach (APLBlock aplblock in this.Successors)
                {
                    node.Edges.Add(aplblock.Label);
                }

                return node;
            }
        }


        public override string Label
        {
            get { return parent.label; }
        }

        public override string DotView
        {
            get { throw new NotImplementedException(); }
        }
    }


    public class ControlBlock : APLBlock
    {
        public ControlBlock(ProcedureState pstate, List<Block> blks, Block sblock)
            : base(pstate, blks, sblock, null)
        {
        }

        public override string Label
        {
            get { return startBlock.Label; }
        }

        public override MoverType Mover
        {
            get
            {
                return MoverType.BothMover;
            }
            set
            {
                Debug.Assert(false, "Should not be called!");
            }
        }

        public override myNode GraphView
        {
            get
            {
                StringBuilder strb = new StringBuilder();

                strb.Append(Label).Append(" : ").Append(Mover == null ? "?" : Mover.ToString()).Append("\\n");
                strb.Append(BlockStr);

                myNode node = new myNode(Label, strb.ToString(), this, myColor.Blue, myColor.White, myColor.Blue, myShape.Box);

                foreach (APLBlock aplblock in this.Successors)
                {
                    node.Edges.Add(aplblock.Label);
                }

                return node;
            }
        }

        public override string DotView
        {
            get
            {
                string label = "IfBlock: " + Label + "\\n";

                label += this.BlockStr;

                label = label.ToString().Replace("\r\n", "\\n").Replace("\t", " ");

                string output = this.Label + " [shape=box,label=\"" + label + "\"];";
                // Output.LogLine("Output: " + output);
                return output;
            }
        }
    }

    public class ForkBlock : ControlBlock
    {
        public StructuredCmd parent;

        public ForkBlock(ProcedureState pstate, List<Block> blks, Block sblock, StructuredCmd par)
            : base(pstate, blks, sblock)
        {
            this.parent = par;
        }
    }

    public class JoinBlock : ControlBlock
    {
        public StructuredCmd parent;

        public JoinBlock(ProcedureState pstate, List<Block> blks, Block sblock, StructuredCmd par)
            : base(pstate, blks, sblock)
        {
            this.parent = par;
        }
    }

    public class CmdBlock : APLBlock
    {
        public CmdBlock(ProcedureState pstate, List<Block> blks, Block sblock)
            : base(pstate, blks, sblock, null)
        {
        }

        static public CmdBlock Create(ProcedureState procState, CmdSeq cmds)
        {
            Block block = new Block(Token.NoToken, "temp_cmd_block", cmds, new ReturnCmd(Token.NoToken));

            List<Block> blocks = new List<Block>();
            blocks.Add(block);

            CmdBlock cmdBlock = new CmdBlock(procState, blocks, block);

            return cmdBlock;
        }


        public override string BlockStr
        {
            get
            {
                Debug.Assert(false);
                return null;
            }
        }

        public override myNode GraphView
        {
            get
            {
                Debug.Assert(false);
                return null;
            }
        }

        public override string DotView
        {
            get
            {
                Debug.Assert(false);
                return null;
            }
        }



        public override MoverType Mover
        {
            get
            {
                return MoverType.NonMover;
            }
            set
            {
                
            }
        }

        public override string Label
        {
            get { return startBlock.Label; }
        }
    } // end CmdBlock


    public class RelabelCommand : ProofCommand
    {
        public string newlabel;
        public string label;

        public RelabelCommand(string b, string l)
            : base("relabel")
        {
            this.label = b;
            this.newlabel = l;

            desc = "relabel " + label + " " + newlabel;
        }

        public static string Usage()
        {
            return "relabel atomicBlockLabel newLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("relabel"))
            {
                string label = parser.NextAsString();
                if (label != null)
                {
                    string newlabel = parser.NextAsString();
                    if (newlabel != null)
                    {
                        return new RelabelCommand(label, newlabel);
                    }
                }
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {
            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(label);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + label);
                return false;
            }
            
            CodeTransformations.RelabelAtomicStmt(atomicBlock.parent, newlabel);

            atomicBlock.procState.MarkAsTransformed();

            return false;
        }

    } // end class RelabelCommand





} // end namespace QED
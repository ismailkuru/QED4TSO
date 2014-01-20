type nextType = [Node]Node;
type keyType = [Node]int;
type markedType = [Node]boolean;
type verType = [int]int;

//---------------------------------
// abstract set
var AbsSet: [int]bool; // set of ints AbsSet[e]==true means e is in the set.
//---------------------------------

//---------------------------------
// History
var Hnext: [int]nextType;
//var Hkey: [int]keyType;
var Hmarked: [int]markedType;
var Hver: [int]verType;
var Hcount: int; // length of the history
invariant (0 <= Hcount);
//---------------------------------




//-------------for induction (only for ReachBetween(Hnext[.],.,.,.)
//axiom (forall m,n,o : Node :: (forall i,j : int :: j<i && ReachBetween(Hnext[i-1],m,n,o) && ReachBetween(Hnext[i],m,n,o)


record Node { next: Node; key: int; marked: boolean; mutex: Mutex; }

const unique null : Node;

const Head: Node;
axiom IsAlloc(Head.alloc);


procedure Contains(e : int) returns (res: bool)
{
 var pred: Node, curr: Node;
 var guard, marked: bool;
 var qseq: [int]int;
 var qcount: int;
 var cseq: [int]Node;
 var m1,m2,m3: Node;

 atomic {
  assume (qseq[0] <= Hcount);
  cseq[0] := Head;
  qcount := 1;
  curr := Head;

  guard := (curr.key < e);
 }
 while(guard) {
  atomic {

    // invariants
    assume	IsNull(null.alloc) && (forall n: Node :: IsNull(n.alloc) <==> n == null);

    assume 	null.next == null;
    assume	(forall i : int :: {Hnext[i]} ReachBetween(Hnext[i], Head, null, null));

    assume	(forall i : int, n: Node :: {ReachBetween(Hnext[i], n, null, null)} IsAlloc(n.alloc) ==> ReachBetween(Hnext[i], n, null, null));
    assume	(forall i : int, n: Node :: {ReachBetween(Hnext[i], n, null, null)} ReachBetween(Hnext[i], n, null, null) && n != null ==> IsAlloc(n.alloc));
    assume 	(forall i : int, n: Node :: {Hnext[i][n]} IsAlloc(n.alloc) <==> Hnext[i][n] != n);
    assume	(forall i : int, n: Node :: {Hnext[i][n]} IsAlloc(n.alloc) ==> !ReachBetween(Hnext[i], Hnext[i][n], n, n));

    assume	(forall i : int, n: Node :: {ReachBetween(Hnext[i], Head, n, null)} ReachBetween(Hnext[i], Head, n, null) <==> Hmarked[i][n] == False);
    assume	(forall i : int, n: Node :: {ReachBetween(Hnext[i], Head, n, n)} IsAlloc(n.alloc) && !ReachBetween(Hnext[i], Head, n, n) ==> Hmarked[i][n] == True);

    assume 	(forall i : int, n: Node :: {Hnext[i][n]} IsAlloc(n.alloc) && Hnext[i][n] != null ==> n.key < Hnext[i][n].key);
    assume	(forall i : int, n,f: Node :: {ReachBetween(Hnext[i], n, f, f)} IsAlloc(n.alloc) && IsAlloc(f.alloc) && n != f && ReachBetween(Hnext[i], n, f, f) ==> n.key < f.key);

    assume 	(forall i : int, n: Node :: {Hnext[i][n]} IsDealloc(n.alloc) ==> Hnext[i][n] == n);
    assume 	(forall i : int, n: Node :: {ReachBetween(Hnext[i], Head, n, n)} IsDealloc(n.alloc) ==> !ReachBetween(Hnext[i], Head, n, n));

    assume (forall i : int :: ReachBetween(Hnext[i], Head, null, null));
    assume (forall i : int :: (forall n: Node :: IsAlloc(n.alloc) ==> ReachBetween(Hnext[i], n, null, null)));
    assume (forall i : int :: (forall n: Node :: ReachBetween(Hnext[i], n, null, null) && n != null ==> IsAlloc(n.alloc)));
    assume (forall i : int :: (forall n: Node :: IsAlloc(n.alloc) <==> Hnext[i][n] != n));
    assume (forall i : int :: (forall n: Node :: IsAlloc(n.alloc) ==> !ReachBetween(Hnext[i], Hnext[i][n], n, n)));

    assume (forall i : int :: (forall n: Node :: ReachBetween(Hnext[i], Head, n, null) <==> Hmarked[i][n] == False));
    assume (forall i : int :: (forall n: Node :: IsAlloc(n.alloc) && !ReachBetween(Hnext[i], Head, n, n) ==> Hmarked[i][n] == True));

    assume (forall i : int :: (forall n: Node :: IsAlloc(n.alloc) && Hnext[i][n] != null ==> n.key < Hnext[i][n].key));
    assume (forall i : int :: (forall n, f: Node :: IsAlloc(n.alloc) && IsAlloc(f.alloc) && n != f && ReachBetween(Hnext[i], n, f, f) ==> n.key < f.key));

    assume (forall i : int :: (forall n: Node :: IsDealloc(n.alloc) ==> Hnext[i][n] == n));
    assume (forall i : int :: (forall n: Node :: IsDealloc(n.alloc) ==> !ReachBetween(Hnext[i], Head, n, n)));


   //*************************************
   //*************************************

   // this is the split invariant (an abstract version)
   // assume (exists m : Node :: (forall i : int :: {ReachBetween(Hnext[i],Head,m,null)} Hmarked[i][m]==False && m.key==e && ReachBetween(Hnext[i],Head,m,null)));
   // rewritten
   havoc m1;
   // assume  m1.key==e && (forall i : int :: {Hnext[i]}{Hmarked[i]} Hmarked[i][m1]==False && ReachBetween(Hnext[i],Head,m1,null));
   assume m1.key==e && (forall i : int :: {ReachBetween(Hnext[i],Head,m1,null)} Hmarked[i][m1]==False && ReachBetween(Hnext[i],Head,m1,null));

   // this is the loop entrance condition
   assume curr.key<e;

   // this is to be discharged; it trivially holds in the first iteration.
   // see whether replacing the assertion with an assumption discharges the main assertion
   // assume (exists m: Node :: Hmarked[qseq[qcount-1]][m]==False && m.key==e && ReachBetween(Hnext[qseq[qcount-1]],curr,m,null));
   // rewritten
   // havoc m2;
   // assume Hmarked[qseq[qcount-1]][m2]==False && m2.key==e && ReachBetween(Hnext[qseq[qcount-1]],curr,m2,null);
   assume ReachBetween(Hnext[qseq[qcount-1]],curr,m1,null);

   // this is for the annotation
   assume (qseq[qcount-1] <= qseq[qcount] && qseq[qcount] <= Hcount);
   curr := Hnext[qseq[qcount]][curr];

   // this is the global invariant that has to be proved inductively an abstract version)
   // currently, (in v4), this inductive version using i and i-1 causes QED to crash (probably due to some Z3 related issue).
   // assume (forall n,m : Node :: (forall i : int :: ReachBetween(Hnext[i],Head,n,null) && ReachBetween(Hnext[i-1],m,n,null) ==> ReachBetween(Hnext[i],m,n,null)));
   // the following, which uses a more general expression in terms of all i and j, discharges the assertion below (v4).
   // assume (forall n,m : Node :: (forall i,j : int :: j<=i && ReachBetween(Hnext[i],Head,n,null) && ReachBetween(Hnext[j],m,n,null) ==> ReachBetween(Hnext[i],m,n,null)));
   // the following also crashes Z3
   assume (forall m: Node, i : int :: {ReachBetween(Hnext[i-1],m,m1,null)}{ReachBetween(Hnext[i],m,m1,null)} ReachBetween(Hnext[i],Head,m1,null) && ReachBetween(Hnext[i-1],m,m1,null) ==> ReachBetween(Hnext[i],m,m1,null));

   // this is the main assertion for this loop; it needs a global invariant.
   // the first two conjuncts follow from the split invariant.
   // the last conjunct should be discharged by
   // a) Head-->*m@(qcount-1) && Head-->*m@(qcount) (the split invariant)
   // b) curr-->*m@(qcount-1) (loop invariant; previous assertion)
   // c) curr-->*m@(qcount-1) && Head-->*m@(qcount) ==> curr-->*m@(qcount) (global invariant)
   // assert (exists m: Node :: m.key==e && Hmarked[qseq[qcount]][m]==False && ReachBetween(Hnext[qseq[qcount]],curr,m,null));
   assert (exists m: Node :: m.key==e && Hmarked[qseq[qcount]][m]==False && ReachBetween(Hnext[qseq[qcount]],curr,m,null));
   //assert ReachBetween(Hnext[qseq[qcount]],curr,m1,null);
   //assert false;
   cseq[qcount] := curr;

   qcount := qcount + 1;
   guard := (curr.key < e);
  }
 } 

 atomic {
  assume (qseq[qcount-1] <= qseq[qcount] && qseq[qcount] <= Hcount);
  marked := (Hmarked[qseq[qcount]][curr] == True);		       


  qcount := qcount + 1;
  if(marked) {
   res := false;
  } else {
   res := (curr.key == e);
  }
	//assert lin_Contains;
/* 	assert ((forall i:int :: 0 <= i && i <= qseq[qcount-1] ==> IsIn(Head, Hnext[i], Hmarked[i], Node_key, e)) ==> res)
	       &&
	       ((forall i:int :: 0 <= i && i <= qseq[qcount-1] ==> IsOut(Head, Hnext[i], Hmarked[i], Node_key, e)) ==> !res);
*/
 }
}

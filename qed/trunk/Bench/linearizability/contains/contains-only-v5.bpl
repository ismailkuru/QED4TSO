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
//invariant (0 <= Hcount);
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

   havoc m1;
   assume m1.key==e && (forall i : int :: {ReachBetween(Hnext[i],Head,m1,null)} Hmarked[i][m1]==False && ReachBetween(Hnext[i],Head,m1,null));
   
   // this is the loop entrance condition
   assume curr.key<e;

   //havoc m2;
   //assume Hmarked[qseq[qcount-1]][m2]==False && m2.key==e && ReachBetween(Hnext[qseq[qcount-1]],curr,m2,null);
   assume ReachBetween(Hnext[qseq[qcount-1]],curr,m1,null);
   
   assume (qseq[qcount-1] <= qseq[qcount] && qseq[qcount] <= Hcount);
   curr := Hnext[qseq[qcount]][curr];

   assume (forall n,m : Node, i,j : int :: {ReachBetween(Hnext[i],Head,n,null),ReachBetween(Hnext[j],m,n,null)} j<=i && ReachBetween(Hnext[i],Head,n,null) && ReachBetween(Hnext[j],m,n,null) ==> ReachBetween(Hnext[i],m,n,null));

   assert (exists m: Node :: m.key==e && Hmarked[qseq[qcount]][m]==False && ReachBetween(Hnext[qseq[qcount]],curr,m,null));
   //assert ReachBetween(Hnext[qseq[qcount]],curr,m1,null);
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

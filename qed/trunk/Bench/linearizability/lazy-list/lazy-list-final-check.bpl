
type nextType = [Node]Node;
type valType = [Node]int;
type markedType = [Node]boolean;
type verType = [int]int;

//---------------------------------
// abstract set
var AbsSet: [int]bool; // set of ints AbsSet[e]==true means e is in the set.
//---------------------------------

//---------------------------------
// History
var Hnext: [int]nextType;
//var Hval: [int]valType;
var Hmarked: [int]markedType;
var Hver: [int]verType;
var Hcount: int; // length of the history
invariant (0 <= Hcount);
//---------------------------------


//---------------------------------
// IsIn and IsOut functions: requires the values of the global variables at a given state

// is k in the set at a given state
function IsIn(head: Node, next: nextType, marked: markedType, val: valType, k: int) returns (res: bool);
axiom (forall head: Node, next: nextType, marked: markedType, val: valType, k: int :: {IsIn(head, next, marked, val, k)} IsIn(head, next, marked, val, k) <==> (exists n:Node :: n != null && marked[n] == False && val[n] == k && ReachBetween(next, head, n, n)));

// is k NOT in the set at a given state
function IsOut(head: Node, next: nextType, marked: markedType, val: valType, k: int) returns (res: bool);
axiom (forall head: Node, next: nextType, marked: markedType, val: valType, k: int :: {IsOut(head, next, marked, val, k)} IsOut(head, next, marked, val, k) <==> (forall n:Node :: n != null && val[n] == k && ReachBetween(next, head, n, n) ==> marked[n] == True));
//---------------------------------


//---------------------------------
// invariants in the CAV paper

invariant (forall n: Node :: IsDealloc(n.alloc) ==> !ReachBetween(Node_next, Head, n, n));

invariant (forall n: Node :: IsDealloc(n.alloc) ==> n.next == n);

invariant (forall m,n: Node :: IsDealloc(n.alloc) && m.next == n ==> m == n);

invariant ReachBetween(Node_next, Head, null, null) && null.next == null;

invariant (forall n: Node :: ReachBetween(Node_next, Head, n, n) && n != null ==> IsAlloc(n.alloc));

//---------------------------------


record Node { next: Node; val: int; marked: boolean; mutex: Mutex; }

const unique null : Node;
invariant IsNull(null.alloc);

const Head: Node;
axiom IsAlloc(Head.alloc);
const Tail: Node;
axiom IsAlloc(Tail.alloc);
//axiom (forall i: int :: i<=Tail.val);
//axiom (forall i: int :: i>=Head.val);
invariant (forall s: int :: s>=0 ==> ReachBetween(Hnext[s],Head,Tail,Tail));


procedure {:isatomic true} Contains(e : int) returns (res: bool)
{
    var pred: Node, curr: Node;
    var guard, marked: bool;
    var qseq: [int]int;
    var qcount: int;
    //var cseq: [int]Node;
    
    /************* invariants ******************/
	assume (forall m,n: Node :: ReachBetween(Node_next, m, n, Tail) && n != null && m != null && m != n ==> m.val < n.val);

	assume (forall k,s,t: int :: s <= t  && t <= Hcount ==> Hver[s][k] <= Hver[t][k]);

	assume (forall s,t,k: int, m, n: Node :: {ReachBetween(Hnext[s], m, n, n), Hver[s][k], Hver[t][k]} s <= t && t <= Hcount && Hver[s][k] == Hver[t][k]
                              && ReachBetween(Hnext[s], Head, n, n) && n.val == k
                          && ReachBetween(Hnext[s], m, n, n)
                          ==> ReachBetween(Hnext[t], m, n, n));

	assume (forall s,k: int, m, n: Node :: s < Hcount && Hver[s][k] == Hver[s+1][k] && m != null && n != null
                              && IsOut(Head, Hnext[s], Hmarked[s], Node_val, k) && ReachBetween(Hnext[s+1], m, n, n)
                          && ReachBetween(Hnext[s], Head, m, m)
                          ==> n.val != k || n.marked == True);

	assume (forall s,t,k: int, m, n: Node :: s <= t && t <= Hcount && Hver[s][k] == Hver[t][k]
                              && IsOut(Head, Hnext[s], Hmarked[s], Node_val, k) && ReachBetween(Hnext[t], m, n, n)
                          && ReachBetween(Hnext[s], Head, m, m)
                          ==> n.val != k || n.marked == True);

    
    /************* invariants ******************/
    
    assume (forall i,j: int :: i<j ==> qseq[i]< qseq[j]);
    assume (qseq[0] <= Hcount);
    //cseq[0] := Head;
    curr := Head;

    guard := (curr.val < e);

    /*
    while(guard) {
      assume (qseq[qcount-1] <= qseq[qcount] && qseq[qcount] <= Hcount);
      curr := Hnext[qseq[qcount]][curr];
      cseq[qcount] := curr;
      qcount := qcount + 1;
      guard := (curr.val < e);
    }*/ // end while
    havoc curr, qcount; assume (exists i:int :: 0 <= i && i<qcount && ReachBetween(Hnext[i],Head,curr,curr)) &&
                               (curr.val>=e ==> (forall n: Node :: (ReachBetween(Hnext[qcount-1],n,curr,curr) ==> n.val<e)));

    assume qseq[qcount] <= Hcount;
    marked := (Hmarked[qseq[qcount]][curr] == True);               
    
    if(marked) { res := false; } 
    else { res := (curr.val == e); }

    assert ((forall i:int :: 0 <= i && i <= qseq[qcount] ==> IsIn(Head, Hnext[i], Hmarked[i], Node_val, e)) ==> res)
           &&
           ((forall i:int :: 0 <= i && i <= qseq[qcount] ==> IsOut(Head, Hnext[i], Hmarked[i], Node_val, e)) ==> !res);
}




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

//invariant (forall n: Node :: IsDealloc(n.alloc) ==> !ReachBetween(Node_next, Head, n, n));

invariant (forall n: Node :: IsDealloc(n.alloc) ==> n.next == n);

invariant (forall m,n: Node :: IsDealloc(n.alloc) && m.next == n ==> m == n);

invariant ReachBetween(Node_next, Head, null, null) && null.next == null;

invariant (forall n: Node :: ReachBetween(Node_next, Head, n, n) && n != null ==> IsAlloc(n.alloc));

invariant (forall m,n: Node :: ReachBetween(Node_next, Head, m, n) && n != null && m != null && m != n ==> m.val < n.val);

invariant (forall k,s,t: int :: s <= t  && t <= Hcount ==> Hver[s][k] <= Hver[t][k]);

invariant (forall s,t,k: int, m, n: Node :: {ReachBetween(Hnext[s], m, n, n), Hver[s][k], Hver[t][k]} s <= t && t <= Hcount && Hver[s][k] == Hver[t][k]
	  	  	   	      	      && ReachBetween(Hnext[s], Head, n, n) && n.val == k
					      && ReachBetween(Hnext[s], m, n, n)
					      ==> ReachBetween(Hnext[t], m, n, n));

invariant (forall s,k: int, m, n: Node :: s < Hcount && Hver[s][k] == Hver[s+1][k] && m != null && n != null
	  	  	   	      	      && IsOut(Head, Hnext[s], Hmarked[s], Node_val, k) && ReachBetween(Hnext[s+1], m, n, n)
					      && ReachBetween(Hnext[s], Head, m, m)
					      ==> n.val != k || n.marked == True);
/*
invariant (forall s,t,k: int, m, n: Node :: s <= t && t <= Hcount && Hver[s][k] == Hver[t][k]
	  	  	   	      	      && IsOut(Head, Hnext[s], Hmarked[s], Node_val, k) && ReachBetween(Hnext[t], m, n, n)
					      && ReachBetween(Hnext[s], Head, m, m)
					      ==> n.val != k || n.marked == True);
*/
//---------------------------------


record Node { next: Node; val: int; marked: boolean; mutex: Mutex; }

const unique null : Node;
invariant IsNull(null.alloc);

const Head: Node;
axiom IsAlloc(Head.alloc);

procedure {:ispublic false} locate(e : int) returns (pred: Node, curr: Node)
{
	var guard, valid: bool;
	
	while(true) {
		    pred := Head;
		    curr := pred.next;
		    guard := (curr.val < e);
		    while(guard) {
		    		 pred := curr;
				 curr := curr.next;
				 guard := (curr.val < e);
		    } // end while
		    call lock(pred.mutex);
		    call lock(curr.mutex);
		    call valid := validate(pred, curr);
		    if(valid) {
		    	      return;
		    }
		    call unlock(pred.mutex);
		    call unlock(curr.mutex);
	} //end while	
}

procedure {:ispublic false} validate(pred: Node, curr: Node) returns (res: bool)
{
	res := (pred.marked == False);
	if(res) {
		res := (curr.marked == False);
		if(res) {
			res := (pred.next == curr);
			return;
		}
	}
}

procedure Contains(e : int) returns (res: bool)
{
	var pred: Node, curr: Node;
	var guard, marked: bool;
	var qseq: [int]int;
	var qcount: int;
	var cseq: [int]Node;

	// guess qseq
	atomic {
	       assume (qseq[0] <= Hcount);
	       cseq[0] := Head;
	       qcount := 1;
	       curr := Head;
	}

	guard := (curr.val < e);
	while(guard) {
		atomic {
		       // guess qseq
		       assume (qseq[qcount-1] <= qseq[qcount] && qseq[qcount] <= Hcount);
		       
		       // eval(curr := curr.next)
		       curr := Hnext[qseq[qcount]][curr];
		       cseq[qcount] := curr;

		       qcount := qcount + 1;
		}
		guard := (curr.val < e);
	} // end while

	atomic {
	       // guess qseq
	       assume (qseq[qcount-1] <= qseq[qcount] && qseq[qcount] <= Hcount);
		       
	       // eval(marked := (curr.marked == True);)
	       marked := (Hmarked[qseq[qcount]][curr] == True);		       

	       qcount := qcount + 1;
	}
	atomic {
	if(marked) {
		   res := false;
	} else {
		   res := (curr.val == e);
	}
	//assert lin_Contains;
	assert ((forall i:int :: 0 <= i && i <= qseq[qcount-1] ==> IsIn(Head, Hnext[i], Hmarked[i], Node_val, e)) ==> res)
	       &&
	       ((forall i:int :: 0 <= i && i <= qseq[qcount-1] ==> IsOut(Head, Hnext[i], Hmarked[i], Node_val, e)) ==> !res);
	}//end atomic
}


/*********************
procedure Contains_original(e : int) returns (res: bool)
{
	var pred: Node, curr: Node;
	var guard, marked: bool;
	
	curr := Head;
	guard := (curr.val < e);
	while(guard) {
		curr := curr.next;
		guard := (curr.val < e);
	} // end while
	marked := (curr.marked == True);
	if(marked) {
		   res := false;
	} else {
		   res := (curr.val == e);
	}
}
*********************/

procedure Add(e : int) returns (res: bool)
{
	var n1, n2, n3: Node;
	var guard: bool;

	call n1,n3 := locate(e);
	guard := (n3.val != e);
	if(guard) {
		  atomic {
		  	 assume Hnext[Hcount] == Node_next;
			 assume Hmarked[Hcount] == Node_marked; 

		  	 assert IsAlloc(n1.alloc);
		  	 assert IsAlloc(n3.alloc) || n3 == null;
			 assert n1.val < e;
			 assert n3 != null ==> e < n3.val;
			 assert n1.next == n3;

		  	 n2 := New Node;
		  	 assume n2.marked == False; ////// n2.marked := False;
			 assume n2.val == e; ////// n2.val := e;
		  	 n2.next := n3;

		  	 n1.next := n2;
			 
			 // abstract operation
			 assert AbsSet[e] == false;
			 AbsSet[e] := true;

			 // record history
			 Hcount := Hcount + 1;
			 Hnext[Hcount] := Node_next;
			 //Hnext[Hcount][n1] := n2;
			 //Hval[Hcount] := Node_val;
			 Hmarked[Hcount] := Hmarked[Hcount-1];

			 // update Hver
			 Hver[Hcount] := Hver[Hcount-1];
			 Hver[Hcount][e] := Hver[Hcount][e] + 1;
		  }
		  res := true;
	} else {
	          atomic {
		  	 // abstract operation
		  	 res := false;
			 assert AbsSet[e] == true;
		  }
	}
	call unlock(n1.mutex);
	call unlock(n3.mutex);
}

procedure Remove(e : int) returns (res: bool)
{
	var n1, n2, n3: Node;
	var guard: bool;

	call n1,n2 := locate(e);
	guard := (n2.val == e);
	if(guard) {
		  atomic {
		  	 assume Hnext[Hcount] == Node_next;
			 assume Hmarked[Hcount] == Node_marked;
			 assert IsAlloc(n1.alloc);
			 assert IsAlloc(n2.alloc);
			 assert n1.val < e && e == n2.val;
			 assert n1.next == n2;
		  
		  	 n2.marked := True;

			 // abstract operation
			 assert AbsSet[e] == true;
			 AbsSet[e] := false;

			 // record history
			 Hcount := Hcount + 1;
			 Hnext[Hcount] := Node_next;
			 //Hval[Hcount] := Node_val;
			 Hmarked[Hcount] := Node_marked;

			 // update Hver
			 Hver[Hcount] := Hver[Hcount-1];
			 Hver[Hcount][e] := Hver[Hcount][e] + 1;
		  }
		  n3 := n2.next;
		  atomic {
		  	 assume Hnext[Hcount] == Node_next;
			 assume Hmarked[Hcount] == Node_marked;
			 assert IsAlloc(n1.alloc);
			 assert IsAlloc(n3.alloc) || n3 == null;
			 assert IsAlloc(n2.alloc);
			 assert n1.val < e && e == n2.val;
			 assert n1.next == n2 && n2.next == n3;
		  	 assert n3 != null ==> e < n3.val;

		  	 n1.next := n3;

			 // record history
			 Hcount := Hcount + 1;
			 Hnext[Hcount] := Node_next;
			 //Hval[Hcount] := Node_val;
			 Hmarked[Hcount] := Node_marked;

			 // update Hver
			 Hver[Hcount] := Hver[Hcount-1];
			 Hver[Hcount][e] := Hver[Hcount][e] + 1;
		  }
		  res := true;
	} else {
		  atomic {
		  	 // abstract operation
		  	 res := false;
			 assert AbsSet[e] == false;
		  }
	}
	call unlock(n1.mutex);
	call unlock(n2.mutex);
}

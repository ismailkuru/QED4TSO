
record Entry 
{
       int key;
       Entry next;
       boolean marked;
       Mutex mutex;
}

type nextType = [Entry]Entry;
type keyType = [Entry]int;
type markedType = [Entry]boolean;
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

const unique null: Entry;

const unique Head: Entry;
const unique Tail: Entry;

procedure contains(e : int) returns (res: bool)
{
	var pred: Entry, curr: Entry;
	var guard, marked: bool;
	var qseq: [int]int;
	var qcount: int;
	var cseq: [int]Entry;

	// guess qseq
	atomic {
	       assume (qseq[0] <= Hcount);
	       cseq[0] := Head;
	       qcount := 1;
	       curr := Head;
	}

	guard := (curr.key < e);
	while(guard) {
		atomic {
		       // guess qseq
		       assume (qseq[qcount-1] <= qseq[qcount] && qseq[qcount] <= Hcount);
		       
		       // ekey(curr := curr.next)
		       curr := Hnext[qseq[qcount]][curr];
		       cseq[qcount] := curr;

		       qcount := qcount + 1;
		}
		guard := (curr.key < e);
	} // end while

	atomic {
	       // guess qseq
	       assume (qseq[qcount-1] <= qseq[qcount] && qseq[qcount] <= Hcount);
		       
	       // ekey(marked := (curr.marked == True);)
	       marked := (Hmarked[qseq[qcount]][curr] == True);		       

	       qcount := qcount + 1;
	}
	atomic {
	if(marked) {
		   res := false;
	} else {
		   res := (curr.key == e);
	}
	//assert lin_Contains;
	assert ((forall i:int :: 0 <= i && i <= qseq[qcount-1] ==> IsIn(Head, Hnext[i], Hmarked[i], Entry_key, e)) ==> res)
	       &&
	       ((forall i:int :: 0 <= i && i <= qseq[qcount-1] ==> IsOut(Head, Hnext[i], Hmarked[i], Entry_key, e)) ==> !res);
	}//end atomic
}

procedure add(e : int) returns (res: bool)
{
	var n1, n2, n3: Entry;

	if(*) {
		  atomic {
		  	 assume Hnext[Hcount] == Entry_next;
			 assume Hmarked[Hcount] == Entry_marked; 

			 assume ReachBetween(Head, n1, Tail);
			 assume ReachBetween(Head, n3, Tail);
			 assume n1.next == n3;
			 assume n1.marked == False;
			 assume n3.marked == False;
			 assume n1.key < e && e < n3.key;

		  	 n2 := New Entry;
		  	 n2.marked := False;
			 n2.key := e;
		  	 n2.next := n3;

		  	 n1.next := n2;
			 
			 // abstract operation
			 assert AbsSet[e] == false;
			 AbsSet[e] := true;

			 // record history
			 Hcount := Hcount + 1;
			 Hnext[Hcount] := Entry_next;
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
}

procedure remove(e : int) returns (res: bool)
{
	var n1, n2, n3: Entry;

	if(*) {
		  atomic {
		  	 assume Hnext[Hcount] == Entry_next;
			 assume Hmarked[Hcount] == Entry_marked;
			 
			 assume ReachBetween(Head, n1, Tail);
			 assume ReachBetween(Head, n2, Tail);
			 assume n1.next == n2;
			 assume n1.marked == False;
			 assume n2.marked == False;
			 assume n1.key < e && e == n2.key;
		  
		  	 n2.marked := True;

			 // abstract operation
			 assert AbsSet[e] == true;
			 AbsSet[e] := false;

			 // record history
			 Hcount := Hcount + 1;
			 Hnext[Hcount] := Entry_next;
			 Hmarked[Hcount] := Entry_marked;

			 // update Hver
			 Hver[Hcount] := Hver[Hcount-1];
			 Hver[Hcount][e] := Hver[Hcount][e] + 1;
		  }
		  n3 := n2.next;
		  atomic {
		  	 assume Hnext[Hcount] == Entry_next;
			 assume Hmarked[Hcount] == Entry_marked;

			 assume ReachBetween(Head, n1, Tail);
			 assume ReachBetween(Head, n2, Tail);
			 assert IsAlloc(n3.alloc) || n3 == null;
			 assume n1.next == n2 && n2.next == n3;
			 assume n1.marked == False;
			 assume n2.marked == True;
			 assume n1.key < e && e == n2.key;
			 assume n3 != null ==> e < n3.key;

		  	 n1.next := n3;

			 // record history
			 Hcount := Hcount + 1;
			 Hnext[Hcount] := Entry_next;
			 Hmarked[Hcount] := Entry_marked;

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
}

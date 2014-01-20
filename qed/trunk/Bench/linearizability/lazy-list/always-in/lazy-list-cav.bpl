
record Node 
{
       key: int;
       next: Node;
       marked: boolean;
}

type nextType = [Node]Node;
type keyType = [Node]int;
type markedType = [Node]boolean;
type allocType = [Node]AllocType;

//---------------------------------
// abstract set
//var AbsSet: [int]bool; // set of ints AbsSet[e]==true means e is in the set.
//---------------------------------

//---------------------------------
// History
var Hnext: [int]nextType;
var Hmarked: [int]markedType;
var Halloc: [int]allocType;
var Hcount: int; // length of the history
//---------------------------------

const unique null: Node;
const unique Head: Node;
const unique Tail: Node;

const E: int;
axiom MIN_INT < E && E < MAX_INT;

procedure contains(e: int) returns (wasPresent: bool)
{
	var pred, curr: Node;
	var qseq: [int]int;
	var qcount: int;
	var m: Node; //***

	assume e == E; //***

	havoc qseq; // guess all time sequences now
	
	pred := Head;

	qcount := 1;
	assume 0 <= qseq[qcount] && qseq[qcount] <= Hcount;

	// eval(curr := pred.next)
	curr := Hnext[qseq[qcount]][pred];
	
	// exists node m with key E
	havoc m; //***
	assume m.key == e && Hmarked[qseq[qcount]][m] == False && ReachBetweenSet(Hnext[qseq[qcount]], Head, Tail)[m]; //***
	assert ReachBetweenSet(Hnext[qseq[qcount]], curr, Tail)[m]; //***
	
	while(*) {

		assume (curr.key < e);

		assume e == E; //***

		assert 1 <= qcount;
	      	assert 0 <= qseq[qcount] && qseq[qcount] <= Hcount;
		
		// exists node m with key E
	    	assert m.key == e && Hmarked[qseq[qcount]][m] == False && ReachBetweenSet(Hnext[qseq[qcount]], Head, Tail)[m]; //***
		// curr reaches m and Tail
		assert ReachBetweenSet(Hnext[qseq[qcount]], curr, Tail)[m]; //***

		pred := curr;

		assume qseq[qcount] <= qseq[qcount+1] && qseq[qcount+1] <= Hcount;
	      	qcount := qcount + 1;

		// eval(curr := pred.next)
		curr := Hnext[qseq[qcount]][pred];

		// curr reaches m and Tail
		assert ReachBetweenSet(Hnext[qseq[qcount]], Head, Tail)[m]; //***
		assert ReachBetweenSet(Hnext[qseq[qcount]], curr, Tail)[m]; //***
		assert curr.key <= e; //***

	} // end while

	assume (curr.key >= e);

	assume e == E; //***
	
	wasPresent := (curr.key == e && curr.marked == False);
	
	// linearizability assertion for this split
	assert wasPresent == true; //***
}

procedure add(e : int) returns (wasPresent: bool)
{
	var pred, curr, tmp: Node;

	while(true) {
		
		// call pred, curr := locate (e);
	
		atomic {
            	   assume MIN_INT < e && e < MAX_INT;
            	   assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, pred, Tail)[Tail];
            	   assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, curr, Tail)[Tail];
	    	   assert pred == Head || !ReachBetweenSet(Node_next, pred, Head)[Head];
	    	   assert !ReachBetweenSet(Node_next, curr, Head)[Head];
            	   assert pred != Tail && curr != Head;
           	   assert pred.key < e && e <= curr.key;

            	   assume Hnext[Hcount] == Node_next;
            	   assume Hmarked[Hcount] == Node_marked;
           	   assume Halloc[Hcount] == Node_alloc;

		   if(pred.next == curr && pred.marked == False) {
		     wasPresent := (curr.key == e);
		     assume e == E ==> wasPresent; //***
 		     if(!wasPresent) {
		  	 tmp := New Node;
			 // assert tmp.next == tmp;
		  	 tmp.marked := False;
			 assume tmp.key == e; // tmp.key := e;
		  	 tmp.next := curr;
		  	 pred.next := tmp;
			 
			 // record history
			 Hcount := Hcount + 1;
			 Hnext[Hcount] := Node_next;
			 Hmarked[Hcount] := Node_marked;
			 Halloc[Hcount] := Node_alloc;
		     } // if
		     return;
		  } // if
	       } // atomic
         } // while
}

procedure remove(e : int) returns (wasPresent: bool)
{
	var pred, curr: Node;

	while(true) {
		
		// call pred, curr := locate (e);
	
		atomic {
            	   assume MIN_INT < e && e < MAX_INT;
            	   assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, pred, Tail)[Tail];
            	   assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, curr, Tail)[Tail];
	    	   assert pred == Head || !ReachBetweenSet(Node_next, pred, Head)[Head];
	    	   assert !ReachBetweenSet(Node_next, curr, Head)[Head];
            	   assert pred != Tail && curr != Head;
           	   assert pred.key < e && e <= curr.key;

            	   assume Hnext[Hcount] == Node_next;
            	   assume Hmarked[Hcount] == Node_marked;
           	   assume Halloc[Hcount] == Node_alloc;

		   if(pred.next == curr && pred.marked == False) {
		     wasPresent := (curr.key == e);
		     assume wasPresent ==> e != E; //***
 		     if(wasPresent) {

		  	 curr.marked := True;
			 pred.next := curr.next;

			 // record history
			 Hcount := Hcount + 1;
			 Hnext[Hcount] := Node_next;
			 Hmarked[Hcount] := Node_marked;
			 Halloc[Hcount] := Node_alloc;
		     } // if
		     return;
		  } // if
	       } // atomic
         } // while
}

/**************
procedure locate(e : int) returns (pred: Node, curr: Node)
{
	var qseq: [int]int;
	var qcount: int;

	atomic {
	  havoc qseq; // guess all time sequence now
    	  assume (forall i: int :: {qseq[i]} qseq[i] <= qseq[i+1]);
	  qcount := 0;
	}
	
	pred := Head;
	atomic {
	       assume 0 <= qcount;
	       qcount := qcount + 1;
	       assume 0 <= qseq[qcount] && qseq[qcount] <= Hcount;

	       // ekey(curr := pred.next)
	       curr := Hnext[qseq[qcount]][pred];
	}

	while(*) {
		assume (curr.key < e);

		pred := curr;

		atomic {
		       assume 0 <= qcount;
      		       qcount := qcount + 1;
		       assume 0 <= qseq[qcount] && qseq[qcount] <= Hcount;

		       // ekey(curr := pred.next)
		       curr := Hnext[qseq[qcount]][pred];
		       cseq[qcount] := curr;
		}
	} // end while
	
	assume (curr.key >= e);
}
**************/
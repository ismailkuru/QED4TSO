
record Node 
{
       key: int;
       next: Node;
       marked: boolean;
       mutex: Mutex;
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

procedure locate(e : int) returns (pred: Node, curr: Node)
{
	assume MIN_INT < e && e < MAX_INT; 
	pred := Head;
	curr := pred.next;	
	
	while(*) {
		assume MIN_INT < e && e < MAX_INT;
		assume (curr.key < e);

		pred := curr;
		curr := pred.next;

	} // end while
	
	assume (curr.key >= e);
}

procedure add(e : int) returns (wasPresent: bool)
{
	var pred, curr, tmp: Node;

	while(true) {
		
		call pred, curr := locate (e);

		call lock(pred.mutex);
		call lock(curr.mutex);
	
		atomic {
		   assert pred.mutex.owner == tid;
		   assert curr.mutex.owner == tid;

            	   assume MIN_INT < e && e < MAX_INT;

            	   assume Hnext[Hcount] == Node_next;
            	   assume Hmarked[Hcount] == Node_marked;
           	   assume Halloc[Hcount] == Node_alloc;

		   if(pred.next == curr && pred.marked == False) {
		     
		     assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, Head, Tail)[pred];
            	     assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, Head, Tail)[curr];
	    	     assert pred == Head || !ReachBetweenSet(Node_next, pred, Head)[Head];
	    	     assert !ReachBetweenSet(Node_next, curr, Head)[Head];
            	     assert pred != Tail && curr != Head;
           	     assert pred.key < e && e <= curr.key;


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

		     call unlock(pred.mutex);
		     call unlock(curr.mutex);

		     return;
		  } // if
	       } // atomic

	       call unlock(pred.mutex);
	       call unlock(curr.mutex);

         } // while
}

procedure remove(e : int) returns (wasPresent: bool)
{
	var pred, curr: Node;

	while(true) {
		
		call pred, curr := locate (e);

		call lock(pred.mutex);
		call lock(curr.mutex);
	
		if(*) {

		atomic {
		   assert pred.mutex.owner == tid;
		   assert curr.mutex.owner == tid;

            	   assume MIN_INT < e && e < MAX_INT;

            	   assume Hnext[Hcount] == Node_next;
            	   assume Hmarked[Hcount] == Node_marked;
           	   assume Halloc[Hcount] == Node_alloc;

		   assume pred.next == curr && pred.marked == False; // if(pred.next == curr && pred.marked == False) {

		     assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, Head, Tail)[pred];
            	     assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, Head, Tail)[curr];
	    	     assert pred == Head || !ReachBetweenSet(Node_next, pred, Head)[Head];
	    	     assert !ReachBetweenSet(Node_next, curr, Head)[Head];
            	     assert pred != Tail && curr != Head;
           	     assert pred.key < e && e <= curr.key;


		     wasPresent := (curr.key == e);
		     assume wasPresent ==> e != E; //***
 		     if(wasPresent) {

		  	 curr.marked := True;
			 // pred.next := curr.next;

			 // record history
			 Hcount := Hcount + 1;
			 Hnext[Hcount] := Node_next;
			 Hmarked[Hcount] := Node_marked;
			 Halloc[Hcount] := Node_alloc;
		     }
		     // return;
		  // } // if
	       } // atomic


	       atomic {
	       	   assert pred.mutex.owner == tid;
		   assert curr.mutex.owner == tid;

            	   assume MIN_INT < e && e < MAX_INT;

            	   assume Hnext[Hcount] == Node_next;
            	   assume Hmarked[Hcount] == Node_marked;
           	   assume Halloc[Hcount] == Node_alloc;

		   assume pred.next == curr && pred.marked == False; // if(pred.next == curr && pred.marked == False) {
		     
		     assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, Head, Tail)[pred];
            	     assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, Head, Tail)[curr];
	    	     assert pred == Head || !ReachBetweenSet(Node_next, pred, Head)[Head];
	    	     assert !ReachBetweenSet(Node_next, curr, Head)[Head];
            	     assert pred != Tail && curr != Head;
           	     assert pred.key < e && e <= curr.key;


		     wasPresent := (curr.key == e);
		     //  assume wasPresent ==> e != E; //***
 		     if(wasPresent) {

		  	 assume curr.marked == True; // curr.marked := True;
			 pred.next := curr.next;

			 // record history
			 Hcount := Hcount + 1;
			 Hnext[Hcount] := Node_next;
			 Hmarked[Hcount] := Node_marked;
			 Halloc[Hcount] := Node_alloc;
		     }

		     call unlock(pred.mutex);
		     call unlock(curr.mutex);

		     return;
		  // } // if
	       } // atomic

	       } // end if(*)

	       call unlock(pred.mutex);
	       call unlock(curr.mutex);

         } // while
}

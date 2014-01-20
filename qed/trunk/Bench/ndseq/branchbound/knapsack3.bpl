// problem
record Item {
  size: int;
  value: int;
}
const ITEMS: [int]Item;
const NUM_ITEMS: int;
const CAPACITY: int;

// solution
record Solution {
  level: int;
  size: int;
  value: int;
  items: [int]bool;
}

// empty solution
const EMPTY: [int]bool;
axiom (forall i: int :: EMPTY[i] == false);

// bound
function bound(Solution) returns(int);
axiom (forall s: Solution :: bound(s) >= 0);

// best solution
var best: int;
var best_soln: Solution;
//invariant best == best_soln.value;

var worklist: Set Solution;

procedure {:entry} knapsack() {
  var root: Solution;
  var e: bool;
  var C,L,R: Solution;

  root := New Solution;
  root.level := 0;
  root.size := 0;
  root.value := 0;
  root.items := EMPTY;

  call set_add(worklist, root);

  foreach {:parallel} (C in worklist) {
atomic {
    if(bound(C) <= best) {
    	if(*) {
    		continue;
	}
    }
}

atomic {
assume C.owner == tid;
assume C.alloc == Alloc;
    if(C.size < CAPACITY && C.value > best) {
      best := C.value;
      best_soln := C;
    }

    if(C.level == NUM_ITEMS) {
      break;
    }
}

    /////////////////////////////////
    ///////////////////////////////// 
atomic {
assume C.owner == tid;  
assume C.alloc == Alloc;
    L := New Solution;
    L.level := C.level + 1;
    L.size := C.size + ITEMS[L.level].size;
    L.value := C.value + ITEMS[L.level].value;
    L.items := C.items;
    // add the item to the solution
    assume L.items[L.level] == false;
    L.items[L.level] := true;

    call set_add(worklist, L);
} // end atomic
    /////////////////////////////////
    /////////////////////////////////
atomic {
assume C.owner == tid;  
assume C.alloc == Alloc;
    R := New Solution;
    R.level := C.level + 1;
    R.size := C.size;
    R.value := C.value;
    R.items := C.items;
    assume R.items[R.level] == false;

    call set_add(worklist, L);
}// end atomic
    
  } // end foreach
}

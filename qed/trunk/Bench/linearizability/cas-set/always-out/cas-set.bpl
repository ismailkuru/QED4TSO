
record Node 
{
  key: int;
  next: Node;
  marked: boolean;
}

const unique null: Node;

var Head: Node;
var Tail: Node;

const unique E: int;
axiom MIN_INT < E && E < MAX_INT;

procedure {:isatomic true} {:ispublic false} get(node: Node) returns (s: Node, m: bool)
{
  s := node.next;
  m := toBool(node.marked);
}

procedure {:isatomic true} {:ispublic false} compareAndSet(node: Node, _old: Node, _new: Node, _old_m: bool, _new_m: bool) returns (r: bool)
{
  r := (node.next == _old && node.marked == toBoolean(_old_m));
  if(r) {
    node.next := _new;
    node.marked := toBoolean(_new_m);
  }
}

  /**
   * If element is present, returns node and predecessor. If absent, returns
   * node with least larger key.
   * @param head start of list
   * @param key key to search for
   * @return If element is present, returns node and predecessor. If absent, returns
   * node with least larger key.
   */
procedure find(e: int) returns (pred: Node, curr: Node)
{
    var succ: Node;
    var marked: bool;
    var snip : bool;
    
    // pred := null; curr := null; succ := null;
    marked := false;

    while (true) {

      pred := Head;
      curr := pred.next;
      succ := null;
      while (true) {
        // succ = curr.next.get(marked); 
        call succ, marked := get(curr);
        while (marked) {           // replace curr if marked
          // snip = pred.next.compareAndSet(curr, succ, false, false);
	  atomic {
	    assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, pred, Tail)[Tail];
	    assert IsAlloc(succ.alloc) && ReachBetweenSet(Node_next, succ, Tail)[Tail];
            assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, curr, Tail)[Tail];
	    assert curr.marked == True && curr.next == succ;
	    call snip := compareAndSet(pred, curr, succ, false, false);
	    assume snip;

	    curr := pred.next;
            call succ, marked := get(curr);
	  }
        }
	  atomic {
            if (curr.key >= e) {
              return;
	    }
	  }    
          pred := curr;
          curr := succ;
      }
    }
  }

  /**
   * Add an element.
   * @param item element to add
   * @return true iff element was not there already
   */
procedure add(e: int) returns (wasPresent: bool) {
    var done: bool;
    var pred, curr: Node;
    var node: Node;
    
    while (true) {
      // find predecessor and curren entries
      call pred, curr := find(e);
      // is the key present?
      wasPresent := (curr.key == e);
      assume MIN_INT < e && e < MAX_INT;
      if (wasPresent) {
        return;
      } else {
        // splice in new node
        atomic {
	   assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, pred, Tail)[Tail];
           assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, curr, Tail)[Tail];
	   assert pred == Head || !ReachBetweenSet(Node_next, pred, Head)[Head];
	   assert !ReachBetweenSet(Node_next, curr, Head)[Head];
           assert pred != Tail && curr != Head;
           assert pred.key < e && e <= curr.key;

	  // assert ReachBetweenSet(Node_next, curr, Tail)[Tail] && curr != Head;
	  // assert curr.key > e;
	  
	  node := New Node;
	  assume node.key == e; // node.key := e;
	  node.marked := False;
	  node.next := curr;
	  // node.next = new AtomicMarkableReference(curr, false);
	  call done := compareAndSet(pred, curr, node, false, false);
	  
	  if(done) {
	    return;
          } else {
	    node.marked := True;
	    node.next := node;
	    Free node;
	  }
        }
      }
    }
  }

  /**
   * Remove an element.
   * @param item element to remove
   * @return true iff element was present
   */
procedure remove(e: int) returns (wasPresent: bool) 
{
    var pred, curr: Node;
    var succ: Node;
    var snip: bool;

    while (true) {
      // find predecessor and curren entries
      call pred, curr := find(e);

      // is the key present?
      wasPresent := (curr.key == e);
      if (!wasPresent) {
        return;
      } else {
        // snip out matching node
        succ := curr.next;
	// curr.next.attemptMark(succ, true);
	atomic {
	  assert ReachBetweenSet(Node_next, curr, Tail)[Tail] && curr != Head && curr != Tail;
	  assert ReachBetweenSet(Node_next, succ, Tail)[Tail] || succ == null;
	  assert curr.marked == False ==> curr.next == succ;
          call snip := compareAndSet(curr, succ, succ, false, true);
	}
        if (snip) {
	  atomic {
	    assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, pred, Tail)[Tail];
	    assert IsAlloc(succ.alloc) && ReachBetweenSet(Node_next, succ, Tail)[Tail];
            assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, curr, Tail)[Tail];
	    assert curr.marked == True && curr.next == succ;
            call snip := compareAndSet(pred, curr, succ, false, false);
	  }
          return;
	}
      }
    }
  }

  /**
   * Test whether element is present
   * @param item element to test
   * @return true iff element is present
   */
  procedure contains(e: int) returns (wasPresent: bool) {
    var pred, curr: Node;
    var succ: Node;
    var marked: bool;
    var snip : bool;
    
    // pred := null; curr := null; succ := null;
    marked := false;

    while (true) {

      pred := Head;
      curr := pred.next;
      succ := null;
      while (true) {
        // succ = curr.next.get(marked); 
        call succ, marked := get(curr);
        while (marked) {           // replace curr if marked
          // snip = pred.next.compareAndSet(curr, succ, false, false);
	  atomic {
	    assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, pred, Tail)[Tail];
	    assert IsAlloc(succ.alloc) && ReachBetweenSet(Node_next, succ, Tail)[Tail];
            assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, curr, Tail)[Tail];
	    assert curr.marked == True && curr.next == succ;
	    call snip := compareAndSet(pred, curr, succ, false, false);
	    assume snip;

	    curr := pred.next;
            call succ, marked := get(curr);
	  }
        }
	  atomic {
            if (curr.key >= e) {
	      wasPresent := curr.key == e;
	      assert !wasPresent;
              return;
	    }
	  }    
          pred := curr;
          curr := succ;
      }
    }
  }




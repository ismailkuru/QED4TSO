
record Node {
       next: Node;
       val: int;
}

const unique null : Node;
invariant IsNull(null.alloc);

const Head: Node;
const Tail: Node;

invariant (forall m : Node, n : Node :: ReachBetween(Node_next,m.next,n,n) ==> (m != n));

// procedure {:ispublic false} remove_helper(e : int) returns (pred : Node, curr : Node)
// {
// 	var guard : bool;

// 	pred := Head;
// 	curr := Head.next;

// 	guard := (curr.val < e);
// 	while (guard) {
// 		pred := curr;
// 		curr := curr.next;
// 		guard := (curr.val < e);
// 	} // end while

// 	return;
// }

procedure {:ispublic true} remove(e : int) returns (removed: bool)
{
	var pred, curr : Node;
	var guard : bool;

atomic {
	// call pred, curr := remove_helper(e);
	havoc pred, curr;

	guard := ((pred.next == curr) && (pred.val < curr.val) && (curr.val == e) && (curr != Tail));
	if (guard) {
		// assume (curr.next != pred);
		pred.next := curr.next;
		removed := true;
	} else {
		removed := false;
	}
}

	return;
}

// procedure {:ispublic false} add_helper(e : int) returns (pred : Node, curr : Node)
// {
// 	var guard : bool;

// 	pred := Head;
// 	curr := Head.next;

// 	guard := (curr.val < e);
// 	while (guard) {
// 		pred := curr;
// 		curr := curr.next;
// 		guard := (curr.val < e);
// 	} // end while

// 	return;
// }

// procedure {:ispublic true} add(e : int) returns (added: bool)
// {
// 	var pred, curr, n : Node;
// 	var guard : bool;

// atomic {
// 	call pred, curr := add_helper(e);

// 	guard := (curr.val == e);
// 	if (guard) {
// 		added := false;
// 	} else {
// 		n := New Node;
// 		n.val := e;
// 		n.next := curr;
// 		pred.next := n;
// 		added := true;
// 	}
// }

// 	return;
// }

procedure {:ispublic false} contains_nondet_advance(e : int) returns (curr : Node)
{
	return;
}

procedure {:ispublic false} contains_helper(e : int) returns (curr : Node)
{
	var guard : bool;
	var m, n : Node;

	curr := Head;

	guard := (curr.val < e);
	while (guard) {
		// Nondeterministic version of read "curr := curr.next".
		atomic {
			assume (curr.next != Tail);

			// Pick a node later in the list, without skipping e or running off the end.
			havoc m;
			assume (ReachBetween(Node_next,curr.next,m,m));
			assume (forall x : Node :: ReachBetween(Node_next,curr,x,m) && (x != m) ==> (x.val != e));
			assume (forall x : Node :: ReachBetween(Node_next,curr,x,m) && (x != m) ==> (x != Tail));

			// Pick a node from which n is reachable but curr is not.
			havoc n;
			assume (ReachBetween(Node_next,n,m,m));
			assume (!ReachBetween(Node_next,n,curr,curr));
			assume (n.val < m.val);

			// Local variable m is dead.
			havoc m;

			curr := n;
		}

		guard := (curr.val < e);
		assume (guard);
	} // end while

	if (guard) {
		// Nondeterministic version of read "curr := curr.next".
		atomic {
			// Pick a node later in the list, without skipping e or running off the end.
			havoc m;
			assume (ReachBetween(Node_next,curr.next,m,m));
			assume (forall x : Node :: ReachBetween(Node_next,curr,x,m) && (x != m) ==> (x.val != e));
			assume (forall x : Node :: ReachBetween(Node_next,curr,x,m) && (x != m) ==> (x != Tail));

			// Pick a node from which n is reachable but curr is not.
			havoc n;
			assume (ReachBetween(Node_next,n,m,m));
			assume (!ReachBetween(Node_next,n,curr,curr));
			assume (n.val < m.val);

			curr := n;
		}

		guard := (curr.val < e);
		assume (!guard);
	}

	return;
}

procedure {:ispublic true} contains(e : int) returns (found: bool)
{
	var curr : Node;
	var guard : bool;

	call curr := contains_helper(e);

	found := (curr.val == e);

	return;
}

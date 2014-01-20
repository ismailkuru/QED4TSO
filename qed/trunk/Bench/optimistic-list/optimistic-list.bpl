
record Node { next: Node; key: int; lock: boolean; marked: boolean; }

const unique null : Node;
invariant IsNull(null.alloc);

var Head: Node;
var Tail: Node;

const unique MinInt: int;
const unique MaxInt: int;
axiom (MinInt < MaxInt);
axiom (forall i: int :: (i != MinInt && i != MaxInt) ==> (MinInt < i && i < MaxInt));

//invariant IsAlloc(Head.alloc) && IsAlloc(Tail.alloc);
//invariant (Head.key == MinInt) && (Tail.key == MaxInt);
//invariant ReachBetween(Node_next, Head, Tail, Tail);
//invariant (forall node: Node :: ReachBetween(Node_next, Head, node, Tail) ==> IsAlloc(node.alloc));

procedure {:isatomic true} {:ispublic false} acq(node: Node)
{
	assume node.lock == False;
	node.lock := True;
}

procedure {:isatomic true} {:ispublic false} rel(node: Node)
{
	assert node.lock == True;
	node.lock := False;
}

procedure {:ispublic false} contains(k : int) returns (res: bool)
{
	var guard: bool;

	curr := Head;

	 guard := (curr.key < k);
	 while(guard) {
	  curr := curr.next;
	  guard := (curr.key < k);
	 }
	
	if(curr.key == k) {
	 if(curr.marked == False) {
	  if(pred.next == curr) {
	   res := True;
	  } else {
	   res := False;
	} else {
	 res := False;
	}
}

procedure {:ispublic false} locate(k : int) returns (pred: Node, curr: Node)
{
	var guard: bool;

	while(true) {
	 pred := Head;
	 curr := pred.next;	

	 guard := (curr.key < k);
	 while(guard) {
	  pred := curr;
	  curr := curr.next;
	  guard := (curr.key < k);
	 }
	
	acq(pred);
	acq(curr);
	if(pred.marked == False) {
	 if(curr.marked == False) {
	  if(pred.next == curr) {
	   return;
	  }
	 }
	}
	rel(pred);
	rel(curr);
       }
}

procedure add(k : int) returns (res: bool)
{
	var pred,curr,entry: Node;

	call pred,curr := locate(k);
   	
	if(curr.key != k) {
	 entry := New Node;
	 entry.marked := False;
	 entry.key := k;
	 entry.next := curr;
	 pred.next := entry;
	 res := true;
	} else {
	 res := false;
	}
	call rel(pred);
	call rel(curr);
}


procedure remove(k : Data) returns (res: bool)
{
	var pred,curr,entry: Node;

	call pred,curr := locate(k);
   	
	if(curr.key == k) {
	 curr.marked := True;
	 entry := curr.next;
	 pred.next := entry;
	 res := true;
	} else {
	 res := false;
	}
	call rel(pred);
	call rel(curr);
}
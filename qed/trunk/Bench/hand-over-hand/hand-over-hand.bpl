
type Node;
var next  : [Node]Node;
var val   : [Node]int;
var lock  : [Node]bool;

type List;
var head : [List]Node;

var alloc: [Node]bool;

const unique nullNode: Node;

//---------------------------------------
// Helper procedures (without implementations)

procedure acquire(node: Node);
modifies lock;
ensures (forall k:Node :: (k == node) || (old(lock[k]) == lock[k]));
ensures !old(lock[node]) && lock[node];

procedure release(node: Node);
requires lock[node];
modifies lock;
ensures (forall k:Node :: (k == node) || (old(lock[k]) == lock[k]));
ensures !lock[node];

procedure newNode() returns (node: Node);
modifies alloc;
ensures (forall k:Node :: (k == node) || (old(alloc[k]) == alloc[k]));
ensures !old(alloc[node]) && alloc[node];

procedure freeNode(node: Node);
requires alloc[node];
modifies alloc;
ensures (forall k:Node :: (k == node) || (old(alloc[k]) == alloc[k]));
ensures !alloc[node];

//procedure newList() returns (list: List);
//modifies alloc;
//ensures (forall<T> n:T :: (n == list) || (old(alloc[n]) == alloc[n]));
//ensures !old(alloc[list]) && alloc[list];


//---------------------------------------
// Procedures

procedure Find(list : List, x : int) returns (node: Node);
modifies lock;

procedure Insert(list : List, x : int) returns (wasPresent : bool);
modifies next, val, lock, alloc;

procedure Delete(list : List, x : int) returns (wasPresent : bool);
modifies next, val, lock, alloc;

//---------------------------------------
// Implementations


implementation Find(list : List, x : int) returns (node: Node)
{
	var p:Node;
	var n:Node;

	p := head[list];
	call acquire(p);
	
	n := next[p];
	while(n != nullNode && val[n] < x)
	{
		call acquire(n);
		call release(p);
		p := n;
	}
	
	node := p;	
}

implementation Insert(list : List, x : int) returns (wasPresent: bool)
{
	var p:Node;
	var n:Node;
	var t:Node;

	call p := Find(list, x);
	
	n := next[p];
	if(n == nullNode || val[n] > x)
	{
		call t := newNode();
		val[t] := x;
		next[t] := p;
		next[p] := t;
		wasPresent := false;
	} else {
		wasPresent := true;
	}

	call release(p);
	return;
}


implementation Delete(list : List, x : int) returns (wasPresent: bool)
{
	var p:Node;
	var n:Node;

	call p := Find(list, x);
	
	n := next[p];
	if(n != nullNode || val[n] == x)
	{
		call acquire(n);
		next[p] := next[n];
		call release(n);
		wasPresent := true;
	} else {
		wasPresent := false;
	}

	call release(p);
	call freeNode(n);
	return;
}




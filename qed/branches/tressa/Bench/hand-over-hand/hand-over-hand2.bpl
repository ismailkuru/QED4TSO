
procedure {:isatomic true} {:ispublic false} Acq(node: Node)
{
	assume node.lock == False;
	node.lock := True;
}

procedure {:isatomic true} {:ispublic false} Rel(node: Node)
{
	assert node.lock == True;
	node.lock := False;
}

type Data = int;
record Node { next: Node; val: Data; lock: boolean; }

const unique null : Node;
invariant IsNull(null.alloc);

record List { head: Node; }
invariant (forall list:List :: {List_head[list]} list.head  != null);

procedure {:ispublic false} Find(list : List, x : Data) returns (node: Node)
{
	var p:Node;
	var n:Node;
	var guard: bool;
	
	p := list.head;
	call Acq(p);
	
	n := p.next;
	
	guard := (n != null && n.val < x);
	while(guard)
	{
		call Acq(n);
		call Rel(p);
		p := n;
		n := p.next;
		guard := (n != null && n.val < x);
	}
	
	node := p;	
}

procedure Insert(list : List, x : Data) returns (wasPresent: bool)
{
	var p:Node;
	var n:Node;
	var t:Node;

	call p := Find(list, x);
	
	n := p.next;
	if(n == null || n.val > x)
	{
		t := New Node;
		t.val := x;
		t.next := n;
		p.next := t;
		wasPresent := false;
	} else {
		wasPresent := true;
	}

	call Rel(p);
}

/*
procedure Delete(list : List, x : Data) returns (wasPresent: bool)
{
	var p:Node;
	var n:Node;

	call p := Find(list, x);
	
	n := p.next;
	if(n != null || n.val == x)
	{
		call Acq(n);
		p.next := n.next;
		call Rel(n);
		wasPresent := true;
	} else {
		wasPresent := false;
	}

	call Rel(p);
	Free n;
}
*/


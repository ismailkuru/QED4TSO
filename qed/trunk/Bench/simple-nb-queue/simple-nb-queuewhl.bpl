type Data;

record Object
{
	data: Data;
}

record Node
{
	next: Node;
	value: Object;
}

record Queue
{
	head: Node;
	tail: Node;
}

const unique nullo: Object;
const unique nulln: Node;
const unique nullq: Queue;

invariant IsNull(nullo.alloc);
invariant IsNull(nulln.alloc);
invariant IsNull(nullq.alloc);

procedure {:isatomic true} {:ispublic false} cas_tail(queue: Queue, expected: Node, newValue: Node) returns (result: bool)
{
	result := (queue.tail == expected);
	if (result)
	{
		queue.tail := newValue;
	}
}

procedure {:isatomic true} {:ispublic false} cas_head(queue: Queue, expected: Node, newValue: Node) returns (result: bool)
{
	result := (queue.head == expected);
	if (result)
	{
		queue.head := newValue;
	}
}

procedure {:isatomic true} {:ispublic false} cas_tail_next(queue: Queue, expected: Node, newValue: Node) returns (result: bool)
{
	result := (queue.tail.next == expected);
	if (result)
	{
		queue.tail.next := newValue;
	}
}

procedure {:ispublic false} create_node(val: Object)
returns (this: Node)
{
	this := New Node;
	this.next := nulln;
	this.value := val;
}

procedure enqueue(this: Queue, value: Object)
{
	var node: Node;
	var t: Node;
	var n: Node;
	
	var g: bool;
	
	call node := create_node(value);
	
	while (true)
	{
		t := this.tail;
		n := t.next;
		if(n == nulln)
		{
			call g := cas_tail_next(this, nulln, node); 
			if (g)
			{
				break;
			}
		}
		else //------------------------------------------
		{
			call g := cas_tail(this, t, n);
		}
	}
	
	call g := cas_tail(this, t, node);
}


procedure dequeue(this: Queue) returns (result: Object)
{
	var h: Node;
	var t: Node;
	var n: Node;
	
	var g: bool;
	
	result := nullo;
	while (true)
	{
		h := this.head;
		n := h.next;
		if(n == nulln)
		{
			result := nullo;
			return;
		}
		//------------------------------------------
		call g := cas_head(this, h, n);
		if(g)
		{
			result := h.value;
			return;
		}
		//------------------------------------------
		t := this.tail;
		if(t == h)
		{
			call g := cas_tail(this, h, n);
		}
	}
}


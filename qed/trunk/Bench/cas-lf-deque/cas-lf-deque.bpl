type Status;
const unique STABLE: Status;
const unique RPUSH: Status;
const unique LPUSH: Status;


type Data;


record Ptr
{
	ref: Node;
	cnt: int;
}

record Node
{
	right: Ptr;
	left: Ptr;
	data: Data;
}

const unique null: Node;

record Anchor
{
	leftmost : Node;
	rightmost : Node;
	status : Status;
}

var $anchor: Anchor;

procedure {:isatomic} CAS(l: Node, r: Node, s: Status, nl: Node, nr: Node, ns: Status)
returns (result: bool)
{
	result := ($anchor.leftmost == l && $anchor.rightmost == r && $anchor.status == s);
	if(result)
	{
		$anchor.leftmost := nl;
		$anchor.rightmost := nr;
		$anchor.status := ns;
	}
}

procedure {:isatomic} CASRight(node: Node, r: Node, c: int, nr: Node, nc: int)
returns (result: bool)
{
	result := (node.right.ref == r && node.right.cnt == c);
	if(result)
	{
		node.right.ref := nr;
		node.right.cnt := nc;
	}
}


procedure PushRight(d: Data)
{
	var node : Node;
	var l, r: Ptr;
	var leftmost, rightmost: Node;
	var status: Status;
	var success : bool;

	r := New Ptr;
	r.ref := null;
	r.cnt := 0;
	
	l := New Ptr;
	l.ref := null;
	l.cnt := 0;
	
	node := New Node;
	node.right := r;
	node.left := l;
	node.data := d;
	
	
	while(true)
	{
		atomic {
			leftmost := $anchor.leftmost;
			rightmost := $anchor.rightmost;
			status := $anchor.status;
		}
			
		
		if(rightmost == null)
		{
			call success := CAS(leftmost, rightmost, status, node, node, status);
			if(success)
			{
				return;
			}
		}
		else
		{
			if(status == STABLE)
			{
				node.left.ref := rightmost;
				node.left.cnt := 0;
				
				call success := CAS(leftmost, rightmost, status, leftmost, node, RPUSH);
				if(success)
				{
					call StabilizeRight(leftmost, node, RPUSH);
					return;
				}
			} else {
			  call Stabilize(leftmost, rightmost, status);
			}
		}
	}
} // end PushRight

const unique EMPTY: Data;

procedure PopRight()
returns (d:Data)
{
	var leftmost, rightmost: Node;
	var prev: Node;
	var status: Status;
	var success : bool;

	while(true)
	{
		atomic {
			leftmost := $anchor.leftmost;
			rightmost := $anchor.rightmost;
			status := $anchor.status;
		}
			
		
		if(rightmost == null)
		{
			d := EMPTY;
			return;		
		}
		
		if(rightmost == leftmost)
		{
			call success := CAS(leftmost, rightmost, status, null, null, status);
			break;
		}
		else
		{
			if(status == STABLE)
			{
				prev := rightmost.left.ref;
				call success := CAS(leftmost, rightmost, status, leftmost, prev, status);
				if(success)
				{
					break;
				}
			}
			else
			{
				call Stabilize(leftmost, rightmost, status);
			}
		}		
	}
	
	d := rightmost.data;
	return;
} // end PopRight

procedure Stabilize(l: Node, r: Node, s: Status)
{
	if(s == RPUSH)
	{
		call StabilizeRight(l, r, s);
	}
	
}

procedure StabilizeRight(l: Node, r: Node, s: Status)
{
	var prev: Node;
	var prevnext: Node;
	var t: int;
	var success : bool;
	
	prev := r.left.ref;
	
	atomic {
		if($anchor.leftmost != l || $anchor.rightmost != r || $anchor.status != s)
		{
			return;
		}
	}
	
	prevnext := prev.right.ref;
	t := prev.right.cnt;
	
	if(prevnext != r)
	{
		atomic {
			if($anchor.leftmost != l || $anchor.rightmost != r || $anchor.status != s)
			{
				return;
			}
		}
		
		call success := CASRight(prev, prevnext, t, r, t + 1);
		if(!success)
		{
			return;
		}
	}
	
	call success := CAS(l, r, s, l, r, STABLE);	
}


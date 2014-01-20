
procedure {:isatomic} CAS(chk: Node, set: Node) returns (r: bool)
{
  r := (top == chk);
  if(r)
  {
    top := set;
  }
}

var H: [int]Node;

record Node
{
  tl: Node;
}

var top: Node;

const unique null: Node;
invariant (IsNull(null.alloc));

procedure {:ispublic} pop() returns (t: Node)
{
	var n: Node;
	var guard: bool;

	while(true) 
	{
		t := top;
		if(t == null)
		{
		  break;
		}

		H[tid] := t;

		if(t == top)
		{
		  n := t.tl;

		  call guard := CAS(t, n);
		  if(guard)
		  {
		    break;
		  }
		}
	} // end while		
	
	H[tid] := null;
}

procedure {:ispublic} push(b: Node) returns (r: bool)
{
	var t: Node;
	var n: int;
	var h: Node;
	var guard: bool;

	n := 1;
	while(n <= Tid) 
	{
	  h := H[n];
	  if(h == b)
	  {
	    r := false;
	    return;
	  }
	  n := n + 1;
	} // end while	

	while(true) 
	{
	  t := top;
		
	  b.tl := t;

	  call guard := CAS(t, b);
	  if(guard)
	  {
	    break;
	  }
	} // end while		
	
	r := true;
}

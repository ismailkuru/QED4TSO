
procedure {:isatomic} CAS(this: NBStack, chk: Node, set: Node) returns (r: bool)
{
  r := (this.top == chk);
  if(r)
  {
    this.top := set;
  }
}

var H: [int]Node;

record Node
{
  tl: Node;
}

record NBStack
{
  top: Node;
}

const unique null: Node;
invariant (IsNull(null.alloc));

procedure {:ispublic} pop(this: NBStack) returns (t: Node)
{
	var n: Node;
	var guard: bool;

	while(true) 
	{
		t := this.top;
		if(t == null)
		{
		  break;
		}

		H[tid] := t;

		if(t == this.top)
		{
		  n := t.tl;

		  call guard := CAS(this, t, n);
		  if(guard)
		  {
		    break;
		  }
		}
	} // end while		
	
	H[tid] := null;

	return;
}

procedure {:ispublic} push(this: NBStack, b: Node) returns (r: bool)
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
	  t := this.top;
		
	  b.tl := t;

	  call guard := CAS(this, t, b);
	  if(guard)
	  {
	    break;
	  }
	} // end while		
	
	r := true;
	return;
}

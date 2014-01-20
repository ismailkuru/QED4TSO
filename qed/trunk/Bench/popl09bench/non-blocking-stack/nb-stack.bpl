
procedure {:atomic true} {:ispublic false} CAS(chk : ref, set : ref) returns (r : bool);
modifies TOP;
ensures (old(TOP) == chk && TOP == set && r == true) || (old(TOP) != chk && TOP == old(TOP) && r == false);

procedure {:atomic true} {:ispublic false} New() returns (o : ref);
ensures o != null;


procedure {:atomic false} {:ispublic true} Alloc(tid : int) returns (o : ref)
requires (1 <= tid && tid <= THREADS);
modifies TOP, tl, H;
{
	var y : ref;
	
	call y := Pop(tid);

	if(y == null)
	{
		call y := New();
	}

	o := y;
	return;
}

procedure {:atomic true} {:ispublic false} Free(tid : int, o : ref) returns (r : bool)
requires (1 <= tid && tid <= THREADS);
modifies TOP, tl, H;
{
	call r := Push(tid, o);
	return;
}

var TOP : ref;
var tl : [ref]ref;
var H  : [int]ref;
const THREADS : int;

procedure {:atomic true} {:ispublic false} Pop(tid : int) returns (o : ref)
requires (1 <= tid && tid <= THREADS);
modifies TOP, tl, H;
{
	var t : ref;
	var n : ref;
	var cas : bool;

	while(true) 
	{
		t := TOP;
		if(t == null)
		{
			break;
		}

		H[tid] := t;
		if(t == TOP)
		{
			n := tl[t];

			call cas := CAS(t, n);
			if(cas == true)
			{
				break;
			}
		}
	} // end while		
	
	H[tid] := null;

	o := t;
	return;
}

procedure {:atomic true} {:ispublic false} Push(tid : int, b : ref) returns (r : bool)
requires (1 <= tid && tid <= THREADS);
requires b != null;
modifies TOP, tl, H;
{
	var t : ref;
	var n : int;
	var h : ref;
	var cas : bool;

	n := 1;
	while(n <= THREADS) 
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
		t := TOP;
		
		tl[b] := t;

		call cas := CAS(t, b);
		if(cas == true)
		{
			break;
		}
	} // end while		
	
	r:= false;
	return;
}





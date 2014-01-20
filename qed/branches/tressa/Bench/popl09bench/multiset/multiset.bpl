var elt : [int]ref;
var valid : [int]bool;
var lock : [int]bool;
const max : int;

procedure {:atomic true} {:ispublic false} acquire(i : int);
	modifies lock;
	ensures (old(lock[i]) == false) && (lock[i] == true);
	ensures (forall x:int:: (x == i) || (lock[i] == old(lock[i])));


procedure {:atomic true} {:ispublic false} release(i : int);
	requires lock[i] == true;
	modifies lock;
	ensures lock[i] == false;
	ensures (forall x:int:: (x == i) || (lock[i] == old(lock[i])));


procedure {:atomic false} {:ispublic true} FindSlot(x : ref) returns (r : int)
	requires x != null;
	modifies lock, elt;
	ensures (r == -1) || (r >= 0 && elt[r] == x);
{
	var i : int;
	
	i := 0;
	
	while(i < max)
	{
		call acquire(i);
		if(elt[i] == null)
		{
			elt[i] := x;
			call release(i);
			r := i;
			return;		
		}
		call release(i);
		i := i + 1;	
	}
	r := -1;
	return;
}

procedure {:atomic false} {:ispublic true} Insert(x : ref) returns (r : bool, i : int)
	requires x != null;
	modifies lock, elt, valid;
	ensures (r == false) || (r == true && elt[i] == x && valid[i] == true);
{
	call i := FindSlot(x);
	
	if(i == -1)
	{
		r := false;
		return;
	}
	
	call acquire(i);
	assert elt[i] == x;
	assert valid[i] == false;
	valid[i] := true;
	call release(i);
	
	return;
}

procedure {:atomic false} {:ispublic true} InsertPair(x : ref, y : ref) returns (r : bool, i : int, j : int)
	requires x != null && y != null;
	modifies lock, elt, valid;
	ensures (r == false) || (r == true && elt[i] == x && valid[i] == true && elt[j] == x && valid[j] == true);
{

	call i := FindSlot(x);
	
	if(i == -1)
	{
		r := false;
		return;
	}
	
	call j := FindSlot(y);
	
	if(j == -1)
	{
		call acquire(i);
		elt[i] := null;
		call release(i);
		r:= false;
		return;	
	}
	
	call acquire(i);
	call acquire(j);
	assert elt[i] == x;
	assert elt[j] == y;
	assert valid[i] == false;
	assert valid[j] == false;
	valid[i] := true;
	valid[j] := true;
	call release(i);
	call release(j);
	
	return;
}

procedure {:atomic false} {:ispublic true} Delete(x : ref) returns (r : bool, i : int)
	requires x != null;
	modifies lock, elt, valid;
	ensures (r == false) || (r == true && elt[i] == null && valid[i] == false);
{
		
	i := 0;

	while(i < max)
	{
		call acquire(i);
		if(elt[i] == x && valid[i] == true)
		{
			elt[i] := null;
			valid[i] := false;
			call release(i);
			r := true;
			return;		
		}
		call release(i);
		i := i + 1;	
	}
	r := false;
	return;
}



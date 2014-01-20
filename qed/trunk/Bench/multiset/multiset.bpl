type ref;

const unique null : ref;

var elt : [int]ref;
var valid : [int]bool;
var lock : [int]bool;
const max : int;

invariant 0 <= max;

procedure {:isatomic true} {:ispublic false} acquire(i : int)
	modifies lock;
{
	assume lock[i] == false;
	lock[i] := true;
	
}


procedure {:isatomic true} {:ispublic false} release(i : int)
	modifies lock;
{
	assert lock[i] == true;
	lock[i] := false;
}


procedure {:isatomic false} {:ispublic true} FindSlot(x : ref) returns (r : int)
	modifies lock, elt;
{
	var j : int;
	
	j := 0;
	
	while(j < max)
	{
		call acquire(j);
		if(elt[j] == null)
		{
			elt[j] := x;
			call release(j);
			r := j;
			return;		
		}
		call release(j);
		j := j + 1;	
	}
	r := -1;
	return;
}

procedure {:isatomic false} {:ispublic true} Insert(x : ref) returns (r : bool, i : int)
	modifies lock, elt, valid;
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

procedure {:isatomic false} {:ispublic true} InsertPair(x : ref, y : ref) returns (r : bool, i : int, j : int)
	modifies lock, elt, valid;
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

procedure {:isatomic false} {:ispublic true} Delete(x : ref) returns (r : bool, i : int)
	modifies lock, elt, valid;
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

procedure {:isatomic false} {:ispublic true} LookUp(x : ref) returns (r : bool, i : int)
	modifies lock;
{		
	i := 0;

	while(i < max)
	{
		call acquire(i);
		if(elt[i] == x && valid[i] == true)
		{
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


type ref;

const unique null : ref;

var elt : [int]ref;
var valid : [int]int;
var lock : [int]int;
const max : int;

invariant 0 <= max;
invariant (forall x:int :: {lock[x]} lock[x] == 0 || lock[x] == 1);
invariant (forall x:int :: {valid[x]} valid[x] == 0 || valid[x] == 1);

procedure {:isatomic true} {:ispublic false} acquire(i : int)
	modifies lock;
{
	assume lock[i] == 0;
	lock[i] := 1;
	
}


procedure {:isatomic true} {:ispublic false} release(i : int)
	modifies lock;
{
	assert lock[i] == 1;
	lock[i] := 0;
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
	assert valid[i] == 0;
	valid[i] := 1;
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
	assert valid[i] == 0;
	assert valid[j] == 0;
	valid[i] := 1;
	valid[j] := 1;
	call release(i);
	call release(j);
	
	return;
}

/*
procedure {:isatomic false} {:ispublic true} Delete(x : ref) returns (r : bool, i : int)
	modifies lock, elt, valid;
{		
	i := 0;

	while(i < max)
	{
		call acquire(i);
		if(elt[i] == x && valid[i] == 1)
		{
			elt[i] := null;
			valid[i] := 0;
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
*/

procedure {:isatomic false} {:ispublic true} LookUp(x : ref) returns (r : bool, i : int)
	modifies lock;
{		
	i := 0;

	while(i < max)
	{
		call acquire(i);
		if(elt[i] == x && valid[i] == 1)
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



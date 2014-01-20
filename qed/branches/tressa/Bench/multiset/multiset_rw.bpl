var elt : [int]ref;
var valid : [int]bool;
var readers : [int]int;
var write : [int]bool;
const max : int;

procedure {:atomic true} {:ispublic false} acquire_read(i : int);
	modifies readers;
	ensures (old(write[i]) == false) && (readers[i] == old(readers[i]) + 1);
	ensures (forall x:int:: (x == i) || (readers[i] == old(readers[i])));


procedure {:atomic true} {:ispublic false} release_read(i : int);
	modifies readers;
	requires (old(readers[i]) > 0) && (old(write[i]) == false);
	ensures (readers[i] == old(readers[i]) - 1);
	ensures (forall x:int:: (x == i) || (readers[i] == old(readers[i])));


procedure {:atomic true} {:ispublic false} acquire_write(i : int);
	modifies write;
	ensures (old(write[i]) == false) && (write[i] == true) && (old(readers[i]) == 0);
	ensures (forall x:int:: (x == i) || (write[i] == old(write[i])));


procedure {:atomic true} {:ispublic false} release_write(i : int);
	modifies write;
	requires (old(write[i]) == false) && (old(readers[i]) == 0);
	ensures (write[i] == false);
	ensures (forall x:int:: (x == i) || (write[i] == old(write[i])));



procedure {:atomic false} {:ispublic true} FindSlot(x : ref) returns (r : int)
	requires x != null;
	modifies write, elt;
	ensures (r == -1) || (r >= 0 && elt[r] == x);
{
	var i : int;
	
	i := 0;
	
	while(i < max)
	{
		call acquire_write(i);
		if(elt[i] == null)
		{
			elt[i] := x;
			call release_write(i);
			r := i;
			return;		
		}
		call release_write(i);
		i := i + 1;	
	}
	r := -1;
	return;
}

procedure {:atomic false} {:ispublic true} Insert(x : ref) returns (r : bool, i : int)
	requires x != null;
	modifies write, elt, valid;
	ensures (r == false) || (r == true && elt[i] == x && valid[i] == true);
{
	call i := FindSlot(x);
	
	if(i == -1)
	{
		r := false;
		return;
	}
	
	call acquire_write(i);
	assert elt[i] == x;
	assert valid[i] == false;
	valid[i] := true;
	call release_write(i);
	
	return;
}

procedure {:atomic false} {:ispublic true} InsertPair(x : ref, y : ref) returns (r : bool, i : int, j : int)
	requires x != null && y != null;
	modifies write, elt, valid;
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
		call acquire_write(i);
		elt[i] := null;
		call release_write(i);
		r:= false;
		return;	
	}
	
	call acquire_write(i);
	call acquire_write(j);
	assert elt[i] == x;
	assert elt[j] == y;
	assert valid[i] == false;
	assert valid[j] == false;
	valid[i] := true;
	valid[j] := true;
	call release_write(i);
	call release_write(j);
	
	return;
}



procedure {:atomic false} {:ispublic true} Delete(x : ref) returns (r : bool, i : int)
	requires x != null;
	modifies write, elt, valid;
	ensures (r == false) || (r == true && old(elt[i]) == x && old(valid[i]) == true && elt[i] == null && valid[i] == false);
{
		
	i := 0;

	while(i < max)
	{
		call acquire_write(i);
		if(elt[i] == x && valid[i] == true)
		{
			elt[i] := null;
			valid[i] := false;
			call release_write(i);
			r := true;
			return;		
		}
		call release_write(i);
		i := i + 1;	
	}
	r := false;
	return;
}


procedure {:atomic false} {:ispublic true} LookUp(x : ref) returns (r : bool, i : int)
	modifies readers;
	requires x != null;
	ensures (r == false) || (r == true && old(elt[i]) == x && old(valid[i]) == true);
{
		
	i := 0;

	while(i < max)
	{
		call acquire_read(i);
		if(elt[i] == x && valid[i] == true)
		{
			call release_read(i);
			r := true;
			return;		
		}
		call release_read(i);
		i := i + 1;	
	}
	r := false;
	return;
}


type ref;

const unique null : ref;

record Cell {
 elt: ref;
 vld: boolean;
 lck: Mutex;
}

var M: [int]Cell;
invariant (forall j:int :: 0 <= j && j <= N ==> IsAlloc(M[j].alloc));

const N : int;
axiom 0 <= N;

procedure FindSlot(x : ref) returns (r : int)
{
	var i : int;
	
	i := 0;
	
	while(i < N)
	{
		call lock(M[i].lck);
		if(M[i].elt == null)
		{
			M[i].elt := x;
			call unlock(M[i].lck);
			r := i;
			return;		
		}
		call unlock(M[i].lck);
		i := i + 1;	
	}
	r := -1;
	return;
}

procedure Insert(x : ref) returns (r : bool)
{
      var i : int;
      call i := FindSlot(x);
	
	if(i == -1)
	{
		r := false;
		return;
	}
	
	call lock(M[i].lck);
	assert M[i].elt == x;
	assert M[i].vld == False;
	M[i].vld := True;
	call unlock(M[i].lck);
        r := true;
}

procedure InsertPair(x : ref, y : ref) returns (r : bool)
{
	var i : int, j : int;
	call i := FindSlot(x);
	
	if(i == -1)
	{
		r := false;
		return;
	}
	
	call j := FindSlot(y);
	
	if(j == -1)
	{
		call lock(M[i].lck);
		M[i].elt := null;
		call unlock(M[i].lck);
		r:= false;
		return;	
	}
	
	call lock(M[i].lck);
	call lock(M[j].lck);
	assert M[i].elt == x;
	assert M[j].elt == y;
	assert M[i].vld == False;
	assert M[j].vld == False;
	M[i].vld := True;
	M[j].vld := True;
	call unlock(M[i].lck);
	call unlock(M[j].lck);
        r := true;
}

procedure Delete(x : ref) returns (r : bool)
{		
	var i : int;
	i := 0;

	while(i < N)
	{
		call lock(M[i].lck);
		if(M[i].elt == x && M[i].vld == True)
		{
			M[i].elt := null;
			M[i].vld := False;
			call unlock(M[i].lck);
			r := true;
			return;		
		}
		call unlock(M[i].lck);
		i := i + 1;	
	}
	r := false;
}

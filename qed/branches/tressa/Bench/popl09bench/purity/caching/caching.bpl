
var x : ref;
var lock : bool;

procedure {:atomic true} {:ispublic false} acquire()
	modifies lock;
	ensures (old(lock) == false) && (lock == true);
{
	assume lock == false;
	lock := true;
}

procedure {:atomic true} {:ispublic false} release()
	requires lock == true;
	modifies lock;
	ensures lock == false;
{
	lock := false;
}

procedure {:atomic true} {:ispublic false} cachePut(k : ref, val : ref)
{
	
}

proceudre {:atomic true} {:ispublic false} cacheGet(k : ref) returns (val : ref)
{
	
}

proceudre {:atomic true} {:ispublic false} compute(k : ref) returns (val : ref)
	ensures val != null;
{
	assume val != null;	
}

procedure {:atomic false} {:ispublic true} lookup(k : ref) returns (r : int)
	
{
	call r := cacheGet(k);
	
	if(r != null)
	{
		return r;
	}
	
	call r := compute(k);
	
	call cachePut(k, r);
	
	return r;
}
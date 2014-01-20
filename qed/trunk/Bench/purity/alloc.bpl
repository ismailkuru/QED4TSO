
var freeMap : [int]bool;
var lock : [int]bool;
const max : int;

procedure {:atomic true} {:ispublic false} acquire(i : int);
	modifies lock;
	ensures (forall x:int :: {lock[x]} (i == x) || (lock[x] == old(lock[x]))); 
	ensures (old(lock[i]) == false) && (lock[i] == true);

procedure {:atomic true} {:ispublic false} release(i : int);
	requires lock[i] == true;
	modifies lock;
	ensures (forall x:int :: {lock[x]} (i == x) || (lock[x] == old(lock[x]))); 
	ensures lock[i] == false;

procedure {:atomic false} {:ispublic true}  alloc() returns (r : int)
	requires max > 0;
	modifies lock, freeMap;
	ensures (r == -1) || (r != -1 && freeMap[r]);
{
	var i : int;
	
	i := 0;
	r := -1;

	while(i < max)
	//invariant (forall x:int :: {lock[x]} lock[x] == old(lock[x]));	
	{
		call acquire(i);
		if(freeMap[i] == true)
		{
			freeMap[i] := false;
			call release(i);
			r := i;
			break;		
		}
		call release(i);
		i := i + 1;
	}
	return;
}


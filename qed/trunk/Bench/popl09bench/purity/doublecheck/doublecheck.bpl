
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

procedure {:atomic true} {:ispublic false} allocate() returns (r : ref)
	ensures r != null;
{
	assume r != null;
}

procedure {:atomic false} {:ispublic true} init()
	modifies lock, x;
	ensures x != null;
{
	if(x == null)
	{
		call acquire();
		if(x == null)
		{
			call x := allocate();
		}
		call release();
	}
}
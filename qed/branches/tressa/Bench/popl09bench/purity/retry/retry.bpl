
var z : int;
var lock : bool;

procedure {:atomic 1} acquire()
	modifies lock;
	ensures (old(lock) == false) && (lock == true);
{
	assume lock == false;
	lock := true;
}

procedure {:atomic 1} release()
	requires lock == true;
	modifies lock;
	ensures lock == false;
{
	lock := false;
}

/*
procedure {:atomic 1} f(i : int) returns (r : int)
{
	
}
*/

procedure {:check 1} apply_f()
	ensures z == f(old(z));
{
	var x;
	var fx;
	
	call acquire();
	x := z;
	call release();
	
	while(true)
	{
		call fx := f(x);
		
		call acquire();
		if(x == z)
		{
			z := fx;
			call release();
			break;
		}
		x := z;
		call release();
	}

}
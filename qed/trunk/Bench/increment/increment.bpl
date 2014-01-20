
record X {
	v : int;
}

procedure {:isatomic true} {:ispublic false} CAS(x:X, a:int, b:int) returns (r:bool)
modifies X_v;
{
	var e : bool;
	
	e := x.v == a;
	if(e)
	{
		x.v := b;
		r := true;
	} else
	{
		r := false;
	}
}

procedure {:ispublic false} inc(x:X)
modifies X_v;
{
	var t : int;
	var b : bool;
	
	while(true)
	{
		t := x.v;
		call b := CAS(x, t, t + 1);
		if(b)
		{
			break;
		}
	}
}

var g : X;

procedure add()
modifies X_v;
{
	var n : int;
	
	//assume g.v >= 0;
	
	while(0 < n)
	{
		call inc(g);
		n := n - 1;
	}
	
	//assert g.v >= n;
}
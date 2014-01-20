
procedure {:ispublic false} {:isatomic true} lock(obj: X)
modifies X_lock;
{
	assume obj.lock == False;
	obj.lock := True;
}

procedure {:ispublic false} {:isatomic true} unlock(obj: X)
modifies X_lock;
{
	assert obj.lock == True;
	obj.lock := False;
}

record X
{
	value: int;
	lock: boolean;
}

procedure {:ispublic false} inc(obj: X)
modifies X_value, X_lock;
{
	var temp: int;
	
	call lock(obj);
	
	temp := obj.value;
	temp := temp + 1;
	obj.value := temp;
	
	call unlock(obj);
}

procedure {:ispublic false} dec(obj: X)
modifies X_value, X_lock;
{
	var temp: int;
	
	call lock(obj);
	
	temp := obj.value;
	temp := temp - 1;
	obj.value := temp;
	
	call unlock(obj);
}


procedure add(obj: X, n: int)
modifies X_value, X_lock;
{
	var dummy: int;
	var old_value: int;
	
	dummy := n;
	
	call lock(obj);
	old_value := obj.value;
	call unlock(obj);
	
	while (dummy > 0)
	{
		dopar {
			call inc(obj);
		}
		with {
			call dec(obj);
		}
		dummy := dummy - 1;
	}
	
	assert (obj.value == old_value);
}






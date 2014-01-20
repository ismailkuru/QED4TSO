
record Lock 
{
	held: boolean;
}

var l: Lock;

procedure {:ispublic false} {:isatomic true} CAS (expected: boolean, newVal: boolean) returns (result: boolean)
{
	var guard: bool;
	result := l.held;
	
	guard := (l.held == expected);
	if (guard)
	{
		l.held := newVal;
	}
}

procedure lock ()
{
	var old_val: boolean;
	call old_val := CAS(False, True);
	while (old_val == True)
	{
		assume l.held == False;
		call old_val := CAS(False, True);
	}
}

procedure unl ()
{
	l.held := False;
}




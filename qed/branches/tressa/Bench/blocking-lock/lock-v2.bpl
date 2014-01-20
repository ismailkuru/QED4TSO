
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
	old_val := True;
	while (old_val == True)
	{
		call old_val := CAS(False, True);
		assume l.held == False;
	}
}

procedure unl ()
{
	l.held := False;
}




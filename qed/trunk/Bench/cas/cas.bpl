
var c : int;

procedure {:atomic true} {:ispublic false} CAS(chk : int, set : int) returns (o : int);
	modifies c;
	ensures (old(c) == chk && c == set) || (old(c) != chk && c == old(c));
	ensures o == old(c);


procedure {:atomic false} {:ispublic true} CasIncrement()
	modifies c;
{
	var i : int;
	var l : int;
	
	i := c;
	call l := CAS(i, i + 1);
	while(l != i)
	{
		i := c;
		call l := CAS(i, i + 1);
	}
}


procedure {:atomic false} {:ispublic true} CasDecrement()
	modifies c;
{
	var i : int;
	var l : int;
	
	i := c;
	call l := CAS(i, i - 1);
	while(l != i)
	{
		i := c;
		call l := CAS(i, i - 1);
	}
}




type item;

const unique null: item;

record queue
{
	back : int;
	items : [int]item;
}

procedure {:isatomic true} {:ispublic false} INC(q: queue) returns (r: int)
{
	r := q.back;
	q.back := q.back + 1;
}

procedure {:isatomic true} {:ispublic false} STORE(q: queue, i: int, x: item)
{
	q.items[i] := x;
}

procedure {:isatomic true} {:ispublic false} READ(q: queue) returns(r: int)
{
	r := q.back;
}

procedure {:isatomic true} {:ispublic false} SWAP(q: queue, i: int, x: item) returns (r: item)
{
	r := q.items[i];
	q.items[i] := x;
}

procedure Enq (q: queue, x: item)
{
	var i: int;
	
	call i := INC(q);
	
	call STORE(q, i, x);
}

procedure Deq (q: queue) returns (x: item)
{
	var range: int;
	var i: int;
	
	while(true)
	{
		call range := READ(q);
		range := range - 1;
		
		i := 1;
		while(i <= range)
		{
			call x := SWAP(q, i, null);
			
			if(x != null)
			{
				return;
			}
			i := i + 1;
		}
	}
}
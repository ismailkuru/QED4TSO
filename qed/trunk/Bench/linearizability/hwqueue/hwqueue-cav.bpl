
type item;

const unique null: item;

var back : int;
var items : [int]item;

procedure Enq (x: item)
{
	var i: int;
	
	// call i := INC(q);
	atomic {
	  i := back;
   	  back := back + 1;
	}
	
	// call STORE(q, i, x);
	atomic {
	  items[i] := x;
	}
}

procedure Deq () returns (x: item)
{
	var range: int;
	var i: int;
	
	while(true)
	{
		// call range := READ(q);
		range := back - 1;
		
		i := 1;
		while(i <= range)
		{
			// call x := SWAP(q, i, null);
			atomic {
			  x := items[i];
			  items[i] := x;
			}
			
			if(x != null)
			{
				return;
			}
			i := i + 1;
		}
	}
}
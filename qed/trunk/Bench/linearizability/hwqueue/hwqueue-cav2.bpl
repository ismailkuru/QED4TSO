
type item;

const unique null: item;

var time: int;
var Hback : [int]int;
var Hitems : [int,int]item;

procedure Enq (x: item)
{
	var i: int;
	var timeSeq: [int]int, last: int;
  	
	atomic {
    	  havoc timeSeq; // guess all time sequence now
	  assume (forall i: int :: {timeSeq[i]} timeSeq[i] <= timeSeq[i+1]);
	  last := 0;
  	}
	
	// call i := INC(q);
	atomic {
	  assume 0 <= last && timeSeq[last] <= time;
	  i := Hback[timeSeq[last]];
	  last := last + 1;

	  Hback[time] := Hback[timeSeq[last]-1] + 1;
   	  back := back + 1;
	}
	
	// call STORE(q, i, x);
	atomic {
	  time := time + 1;
	  Hitems[time,i] := x;
	}
}

procedure Deq () returns (x: item)
{
	var range: int;
	var i: int;
	
	while(true)
	{
		// call range := READ(q);
		atomic {
		  range := Hback[time] - 1;
		}
		
		i := 1;
		while(i <= range)
		{
			// call x := SWAP(q, i, null);
			atomic {
			  x := Hitems[time,i];
			  time := time + 1;
			  Hitems[time,i] := null;
			}
			
			if(x != null)
			{
				return;
			}
			i := i + 1;
		}
	}
}
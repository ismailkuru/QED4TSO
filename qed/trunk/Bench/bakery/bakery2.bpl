var choosing : [int] bool;
var number : [int] int;
var counter: int;

procedure bakery()
{
	var j,k : int;
	var max : int;

	choosing[tid] := true;
	
	/*
	k := 1;
	max := 0;
	while(k <= Tid) 
	{
		if(number[k] > max) {
			max := number[k];		
		}	
		k := k + 1;
	}
	number[tid] := 1 + max;
	*/

	atomic{
		havoc max;
		assume (forall t:TID :: 1 <= t && t <= Tid ==> max > number[t]);
		number[tid] := 1 + max;
	}
	
	choosing[tid] := false;
	
	j := 1;
	while(j <= Tid)
	{	
		if(j != tid) {	
		     assume choosing[j] == false;
		     assume number[j] == 0 || (number[j] > number[tid]) || ((number[j] == number[tid]) && (j > tid));
		}
		j := j + 1;
	}

	// begin critical region
	counter := counter + 1;
	assert counter == 1;
	counter := counter - 1;
	// end critical region

	// release the lock
	number[tid] := 0;
}


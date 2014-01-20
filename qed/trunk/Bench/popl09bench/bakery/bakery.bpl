const N : int;
var choosing : [int] bool;
var number : [int] int;

var c : int; // this is for checking the safety property


procedure {:atomic false} {:ispublic true} bakery(i : int)
	requires N > 0;
	modifies choosing, number, c;
{
	var j : int;
	var max : int;

	choosing[i] := true;
	
	j := 1;
	max := 0;
	while(j <= N) 
	{
		if(number[j] > max) {
			max := number[j];		
		}	
		j := j + 1;
	}
	number[i] := 1 + number[i];
	
	choosing[i] := false;
	
	j := 1;
	while(j <= N)
	{		
		while(choosing[j] != false) { /* wait */ }
		while(number[j] != 0 && ((number[j] < number[i]) || ((number[j] == number[i]) && (j < i)))) { /* wait */ }
		j := j + 1;
	}

	// critical section
	
	c := c + 1;

	assert c == 1;

	c := c - 1;
	

	// release
	number[i] := 0;
}


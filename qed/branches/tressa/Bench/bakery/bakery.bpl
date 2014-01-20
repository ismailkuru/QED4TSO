const N : int;
var choosing : [int] bool;
var number : [int] int;


procedure {:isatomic false} {:ispublic true} Acquire(i : int)
	requires N > 0;
	modifies choosing, number;
{
	var j : int;
	var max : int;
	var localIf : bool;

	choosing[i] := true;
	tressa true;
	
	j := 1;
	max := 0;
	while(j <= N) 
	invariant j <= N+1 && max >= 0 && j >= 1 && (forall x:int :: {number[x]} ((1 <= x) && (x <= N)) ==> (max >= number[x])) && (max == 0 || (exists y : int :: ((1 <= y) && (y <= N)) && max == number[y]));
	invariant j <= N+1 && max >= 0 && j >= 1 && (forall x:int :: {number[x]} ((1 <= x) && (x < j)) ==> (max >= number[x])) && (max == 0 || (exists y : int :: ((1 <= y) && (y < j)) && max == number[y]));
	{
	 localIf := number[j]>max;
		if(localIf) {
			max := number[j];		
		}	
		j := j + 1;
	}
	number[i] := 1 + number[i];
	
	choosing[i] := false;
	
	j := 1;
	while(j <= N)
	invariant j <= N+1 && j >= 1 && (forall x:int :: {choosing[x]} ((1 <= x) && (x <= N)) ==> ((choosing[x] == true) && ((number[j] == 0) || ((number[j] < number[i]) || ((number[j] == number[i]) && (j < i))))));
	invariant j <= N+1 && j >= 1 && (forall x:int :: {choosing[x]} ((1 <= x) && (x < j)) ==> ((choosing[x] == true) && ((number[j] == 0) || ((number[j] < number[i]) || ((number[j] == number[i]) && (j < i))))));
	{		
		assume choosing[j] == true;
		assume number[j] == 0 || ((number[j] < number[i]) || ((number[j] == number[i]) && (j < i)));
		j := j + 1;
	}
}


procedure {:isatomic false} {:ispublic true} Release(i : int)
	requires number[i] > 0;
  	modifies choosing, number;
{
	number[i] := 0;
}


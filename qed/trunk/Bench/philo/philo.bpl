const unique NUM_PHIL: int;
const unique tid: int;

var id: [int]int;
var forks: [int]bool;
var objlock: int;
var ownforks: [int]int;

procedure getForks()
 modifies forks, objlock, ownforks;
{
	var id1, id2: int;
	
	if (*) {
		atomic { assume objlock==0; objlock := tid; }
		id1 := id[tid]; 
		id2 := id[(tid+1) % NUM_PHIL];
		atomic {	assert objlock==tid;	assume !(forks[id1] && forks[id2]); }
		atomic { assert objlock==tid; objlock := 0; }
		while (*) {
			atomic { assume objlock==0; objlock := tid; }
			atomic { assert objlock==tid; assume !(forks[id1] && forks[id2]); }
			atomic { assert objlock==tid; objlock := 0; }
		}
		atomic { assume objlock==0; objlock := tid; }
		atomic { assert objlock==tid; assume forks[id1] && forks[id2]; }
		atomic { 
			assert objlock==tid; 
			forks[id1] := false; 
			assert ownforks[id1]==0;
			ownforks[id1] := tid; 
		}
		atomic { 
			assert objlock==tid; 
			forks[id2] := false; 
			assert ownforks[id2]==0;
			ownforks[id2] := tid; 
		}
		atomic { assert objlock==tid; objlock := 0; }
	}
	else {
		atomic { assume objlock==0; objlock := tid; }
		id1 := id[tid];
		id2 := id[(tid+1) % NUM_PHIL];
		atomic { assert objlock==tid; assume forks[id1] && forks[id2]; }
		atomic { 
			assert objlock==tid; 
			forks[id1] := false; 
			assert ownforks[id1]==0;
			ownforks[id1] := tid; 
		}
		atomic { 
			assert objlock==tid; 
			forks[id2] := false; 
			assert ownforks[id2]==0;
			ownforks[id2] := tid; 
		}
		atomic { assert objlock==tid; objlock := 0; }
	}
}

procedure putForks()
	modifies forks, objlock, ownforks;
{
	var id1, id2: int; 
	
	atomic { assume objlock==0; objlock := tid; }
	id1 := id[tid];
	id2 := id[(tid+1) % NUM_PHIL];
	atomic { 
		assert objlock==tid;
		assert ownforks[id1]==tid;
		assert !forks[id1]; 
		forks[id1] := true;
		ownforks[id1] := 0;
	}
	atomic { 
		assert objlock==tid;
		assert ownforks[id2]==tid;
		assert !forks[id2];
		forks[id2] := true; 
		ownforks[id2] := 0;
	}
	atomic { assert objlock==tid; objlock := 0; }
}
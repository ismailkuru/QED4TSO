const unique NUM_PHIL: int;

const unique tid: int;

var id: [int]int;

var forks: [int]bool;

var objlock: int;

var ownforks: [int]int;

procedure getForks();
  modifies forks, objlock, ownforks;



implementation getForks()
{
  var id1: int;
  var id2: int;
  var pc: int;

	if (*)
	{

		atomic { // None-mover
			assume objlock == 0;
			objlock := tid;

			id1 := id[tid];
			id2 := id[(tid + 1) % NUM_PHIL];
			assert objlock == tid;
//			assume !(forks[id1] && forks[id2]);
			assert objlock == tid;
			objlock := 0;
		}

		while (*)
		{
			atomic { // None-mover
				assume objlock == 0;
				objlock := tid;
				assert objlock == tid;
//				assume !(forks[id1] && forks[id2]);
				assert objlock == tid;
				objlock := 0;
 		}
		}
	}
	else
	{
		atomic { // Right-mover
			assume objlock == 0;
			objlock := tid;
			id1 := id[tid];
			id2 := id[(tid + 1) % NUM_PHIL];
			assert objlock == tid;
			assume forks[id1] && forks[id2];
			assert objlock == tid;
			forks[id1] := false;
			assert ownforks[id1] == 0;
			ownforks[id1] := tid;
			assert objlock == tid;
			forks[id2] := false;
			assert ownforks[id2] == 0;
			ownforks[id2] := tid;
			assert objlock == tid;
			objlock := 0;
		}
 }
}



procedure putForks();
  modifies forks, objlock, ownforks;



implementation putForks()
{
  var id1: int;
  var id2: int;
  var pc: int;


 atomic { // Both-mover
  assume objlock == 0;
  objlock := tid;
  id1 := id[tid];
  id2 := id[(tid + 1) % NUM_PHIL];
  assert objlock == tid;
  assert ownforks[id1] == tid;
  assert !forks[id1];
		forks[id1] := true;
		ownforks[id1] := 0;

		assert objlock == tid;
		assert ownforks[id2] == tid;
		assert !forks[id2];
		forks[id2] := true;
		ownforks[id2] := 0;

		assert objlock == tid;
		objlock := 0;
 }
}




invariant (forall a: int :: id[a] == a);

invariant objlock == 0;

invariant (forall a: int :: forks[a] <==> ownforks[a] == tid);

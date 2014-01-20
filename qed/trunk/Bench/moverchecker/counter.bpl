var _Count: [int]int;

var _Free: [int]bool;

 

invariant (forall x: int :: _Count[x] >= 0);

 

procedure Allocate() returns (x: int)

modifies _Count, _Free;

{

  assume _Count[x] == 0;

  _Count[x] := 1;

  _Free[x] := false;

}

 

procedure MyFree(x: int)

modifies _Count, _Free;

{

  assert !_Free[x];

  assert _Count[x] >= 1;

  _Count[x] := _Count[x] - 1;

  _Free[x] := true;

}

 

procedure Increment(x: int)

modifies _Count;

{

  assert !_Free[x];

  assert _Count[x] >= 1;

  _Count[x] := _Count[x] + 1;

}

 

procedure Decrement(x: int)

modifies _Count;

{

  assert _Count[x] >= 1;

  _Count[x] := _Count[x] - 1;

}
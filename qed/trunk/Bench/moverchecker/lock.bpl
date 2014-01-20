var Lock: [int]int;
// const tid: int;

procedure Acquire(x: int)
modifies Lock;
{
  assume Lock[x] == 0;
  Lock[x] := tid;
}

procedure Release(x: int)
modifies Lock;
{
  assert Lock[x] == tid;
  Lock[x] := 0;
}
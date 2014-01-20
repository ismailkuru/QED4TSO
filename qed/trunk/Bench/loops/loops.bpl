
function f(int) returns (int);

axiom (exists k: int :: f(k) == K);

const K: int;

procedure {:atomic false} {:ispublic true} Find(a: int, b: int) returns (k: int)
requires a <= b;
{
  var x: int, y: int;
  var i: int;
  var found: bool;
  
  found := false;
  x := a;
  y := b;
  i := -1;

  while (!found)
    invariant x <= y && (forall j: int :: x < j && j < y ==> f(j) != K);
  {
    if (f(x) == K) {
      i := x;
      found := true;
    } else if (f(y) == K) {
      i := y;
      found := true;
    }
    x := x-1;
    y := y+1;
  }
  
  k := i;
  return;
}


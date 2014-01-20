record M<T> {
 fld: [int]T;
}

record another {
 fld: [int]int;
}

const b: bool;
axiom b == true;
const z: int;
axiom z == 5;
type C;
type D W;
const k,l : C;
var tayfun: [int]C;
var K: D bool;
var L: <Z>[Z]int;
procedure main<U>(inn: U) {
var i : int;
var m : Queue C;
var n: M C;
atomic {
       assume k != l;
       assume tayfun[i] == k;
       assume tayfun[i+1] == l;
       tayfun[i] := tayfun[i+1];
}
}
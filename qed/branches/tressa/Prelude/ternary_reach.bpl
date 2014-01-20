
// interpreted "store1" function in Boogie
function store1(f: [int]int, p: int, q: int) returns ([int]int);

////////////////////
// Between predicate
//////////////////// 
function ReachBetween(f: [int]int, x: int, y: int, z: int) returns (bool);
function ReachAvoiding(f: [int]int, x: int, y: int, z: int) returns (bool);


//////////////////////////
// Between set constructor
//////////////////////////
function ReachBetweenSet(f: [int]int, x: int, z: int) returns ([int]bool);

////////////////////////////////////////////////////
// axioms relating ReachBetween and ReachBetweenSet
////////////////////////////////////////////////////
axiom(forall f: [int]int, x: int, y: int, z: int :: {ReachBetweenSet(f, x, z)[y]} ReachBetweenSet(f, x, z)[y] <==> ReachBetween(f, x, y, z));
axiom(forall f: [int]int, x: int, y: int, z: int :: {ReachBetween(f, x, y, z), ReachBetweenSet(f, x, z)} ReachBetween(f, x, y, z) ==> ReachBetweenSet(f, x, z)[y]);
axiom(forall f: [int]int, x: int, z: int :: {ReachBetweenSet(f, x, z)} ReachBetween(f, x, x, x));


//////////////////////////
// Axioms for ReachBetween
//////////////////////////

// reflexive
axiom(forall f: [int]int, x: int :: ReachBetween(f, x, x, x));

// step
//axiom(forall f: [int]int, x: int :: {f[x]} ReachBetween(f, x, f[x], f[x])); 
axiom(forall f: [int]int, x: int, y: int, z: int, w:int :: {ReachBetween(f, y, z, w), f[x]} ReachBetween(f, x, f[x], f[x])); 

// reach
axiom(forall f: [int]int, x: int, y: int :: {f[x], ReachBetween(f, x, y, y)} ReachBetween(f, x, y, y) ==> x == y || ReachBetween(f, x, f[x], y));

// cycle
axiom(forall f: [int]int, x: int, y:int :: {f[x], ReachBetween(f, x, y, y)} f[x] == x && ReachBetween(f, x, y, y) ==> x == y);

// sandwich
axiom(forall f: [int]int, x: int, y: int :: {ReachBetween(f, x, y, x)} ReachBetween(f, x, y, x) ==> x == y);

// order1
axiom(forall f: [int]int, x: int, y: int, z: int :: {ReachBetween(f, x, y, y), ReachBetween(f, x, z, z)} ReachBetween(f, x, y, y) && ReachBetween(f, x, z, z) ==> ReachBetween(f, x, y, z) || ReachBetween(f, x, z, y));

// order2
axiom(forall f: [int]int, x: int, y: int, z: int :: {ReachBetween(f, x, y, z)} ReachBetween(f, x, y, z) ==> ReachBetween(f, x, y, y) && ReachBetween(f, y, z, z));

// transitive1
axiom(forall f: [int]int, x: int, y: int, z: int :: {ReachBetween(f, x, y, y), ReachBetween(f, y, z, z)} ReachBetween(f, x, y, y) && ReachBetween(f, y, z, z) ==> ReachBetween(f, x, z, z));

// transitive2
axiom(forall f: [int]int, x: int, y: int, z: int, w: int :: {ReachBetween(f, x, y, z), ReachBetween(f, y, w, z)} ReachBetween(f, x, y, z) && ReachBetween(f, y, w, z) ==> ReachBetween(f, x, y, w) && ReachBetween(f, x, w, z));

// transitive3
axiom(forall f: [int]int, x: int, y: int, z: int, w: int :: {ReachBetween(f, x, y, z), ReachBetween(f, x, w, y)} ReachBetween(f, x, y, z) && ReachBetween(f, x, w, y) ==> ReachBetween(f, x, w, z) && ReachBetween(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.  
// It cannot be proved using the rest of the axioms.
axiom(forall f: [int]int, u:int, x: int :: {ReachBetween(f, u, x, x)} ReachBetween(f, u, x, x) ==> ReachBetween(f, u, u, x));

// relation between ReachAvoiding and ReachBetween
axiom(forall f: [int]int, x: int, y: int, z: int :: {ReachAvoiding(f, x, y, z)}{ReachBetween(f, x, y, z)} ReachAvoiding(f, x, y, z) <==> (ReachBetween(f, x, y, z) || (ReachBetween(f, x, y, y) && !ReachBetween(f, x, z, z))));

// update
axiom(forall f: [int]int, u: int, v: int, x: int, p: int, q: int :: {ReachAvoiding(store1(f, p, q), u, v, x)} ReachAvoiding(store1(f, p, q), u, v, x) <==> ((ReachAvoiding(f, u, v, p) && ReachAvoiding(f, u, v, x)) || (ReachAvoiding(f, u, p, x) && p != x && ReachAvoiding(f, q, v, p) && ReachAvoiding(f, q, v, x))));


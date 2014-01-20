
type byte;
function OneByteToInt(byte) returns (int);
function TwoBytesToInt(byte, byte) returns (int);
function FourBytesToInt(byte, byte, byte, byte) returns (int);
axiom(forall b0:byte, c0:byte :: {OneByteToInt(b0), OneByteToInt(c0)} OneByteToInt(b0) == OneByteToInt(c0) ==> b0 == c0);
axiom(forall b0:byte, b1: byte, c0:byte, c1:byte :: {TwoBytesToInt(b0, b1), TwoBytesToInt(c0, c1)} TwoBytesToInt(b0, b1) == TwoBytesToInt(c0, c1) ==> b0 == c0 && b1 == c1);
axiom(forall b0:byte, b1: byte, b2:byte, b3:byte, c0:byte, c1:byte, c2:byte, c3:byte :: {FourBytesToInt(b0, b1, b2, b3), FourBytesToInt(c0, c1, c2, c3)} FourBytesToInt(b0, b1, b2, b3) == FourBytesToInt(c0, c1, c2, c3) ==> b0 == c0 && b1 == c1 && b2 == c2 && b3 == c3);

// Mutable
var Mem_BYTE:[int]byte;
var alloc:[int]name;


function Field(int) returns (name);
function Base(int) returns (int);

// Constants
const unique UNALLOCATED:name;
const unique ALLOCATED: name;
const unique FREED:name;

const unique BYTE:name;

function Equal([int]bool, [int]bool) returns (bool);
function Subset([int]bool, [int]bool) returns (bool);
function Disjoint([int]bool, [int]bool) returns (bool);

function Empty() returns ([int]bool);
function Singleton(int) returns ([int]bool);
function Reachable([int,int]bool, int) returns ([int]bool);
function Union([int]bool, [int]bool) returns ([int]bool);
function Intersection([int]bool, [int]bool) returns ([int]bool);
function Difference([int]bool, [int]bool) returns ([int]bool);
function Dereference([int]bool, [int]int) returns ([int]bool);
function Inverse(f:[int]int, x:int) returns ([int]bool);

function AtLeast(int, int) returns ([int]bool);
function Rep(int, int) returns (int);
axiom(forall n:int, x:int, y:int :: {AtLeast(n,x)[y]} AtLeast(n,x)[y] ==> x <= y && Rep(n,x) == Rep(n,y));
axiom(forall n:int, x:int, y:int :: {AtLeast(n,x),Rep(n,x),Rep(n,y)} x <= y && Rep(n,x) == Rep(n,y) ==> AtLeast(n,x)[y]);
axiom(forall n:int, x:int :: {AtLeast(n,x)} AtLeast(n,x)[x]);
axiom(forall n:int, x:int, z:int :: {PLUS(x,n,z)} Rep(n,x) == Rep(n,PLUS(x,n,z)));
axiom(forall n:int, x:int :: {Rep(n,x)} (exists k:int :: Rep(n,x) - x  == n*k));

/*
function AtLeast(int, int) returns ([int]bool);
function ModEqual(int, int, int) returns (bool);
axiom(forall n:int, x:int :: ModEqual(n,x,x));
axiom(forall n:int, x:int, y:int :: {ModEqual(n,x,y)} ModEqual(n,x,y) ==> ModEqual(n,y,x));
axiom(forall n:int, x:int, y:int, z:int :: {ModEqual(n,x,y), ModEqual(n,y,z)} ModEqual(n,x,y) && ModEqual(n,y,z) ==> ModEqual(n,x,z));
axiom(forall n:int, x:int, z:int :: {PLUS(x,n,z)} ModEqual(n,x,PLUS(x,n,z)));
axiom(forall n:int, x:int, y:int :: {ModEqual(n,x,y)} ModEqual(n,x,y) ==> (exists k:int :: x - y == n*k));
axiom(forall x:int, n:int, y:int :: {AtLeast(n,x)[y]}{ModEqual(n,x,y)} AtLeast(n,x)[y] <==> x <= y && ModEqual(n,x,y));
axiom(forall x:int, n:int :: {AtLeast(n,x)} AtLeast(n,x)[x]);
*/

function Array(int, int, int) returns ([int]bool);
axiom(forall x:int, n:int, z:int :: {Array(x,n,z)} z <= 0 ==> Equal(Array(x,n,z), Empty()));
axiom(forall x:int, n:int, z:int :: {Array(x,n,z)} z > 0 ==> Equal(Array(x,n,z), Difference(AtLeast(n,x),AtLeast(n,PLUS(x,n,z)))));


axiom(forall x:int :: !Empty()[x]);

axiom(forall x:int, y:int :: {Singleton(y)[x]} Singleton(y)[x] <==> x == y);
axiom(forall y:int :: {Singleton(y)} Singleton(y)[y]);

/* this formulation of Union IS more complete than the earlier one */
/* (A U B)[e], A[d], A U B = Singleton(c), d != e */
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Union(S,T)[x]} Union(S,T)[x] <==> S[x] || T[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Union(S,T), S[x]} S[x] ==> Union(S,T)[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Union(S,T), T[x]} T[x] ==> Union(S,T)[x]);

axiom(forall x:int, S:[int]bool, T:[int]bool :: {Intersection(S,T)[x]} Intersection(S,T)[x] <==>  S[x] && T[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Intersection(S,T), S[x]} S[x] && T[x] ==> Intersection(S,T)[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Intersection(S,T), T[x]} S[x] && T[x] ==> Intersection(S,T)[x]);

axiom(forall x:int, S:[int]bool, T:[int]bool :: {Difference(S,T)[x]} Difference(S,T)[x] <==> S[x] && !T[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Difference(S,T), S[x]} S[x] ==> Difference(S,T)[x] || T[x]);

axiom(forall x:int, S:[int]bool, M:[int]int :: {Dereference(S,M)[x]} Dereference(S,M)[x] ==> (exists y:int :: x == M[y] && S[y]));
axiom(forall x:int, S:[int]bool, M:[int]int :: {M[x], S[x], Dereference(S,M)} S[x] ==> Dereference(S,M)[M[x]]);
axiom(forall x:int, y:int, S:[int]bool, M:[int]int :: {Dereference(S,M[x := y])} !S[x] ==> Equal(Dereference(S,M[x := y]), Dereference(S,M)));
axiom(forall x:int, y:int, S:[int]bool, M:[int]int :: {Dereference(S,M[x := y])} 
     S[x] &&  Equal(Intersection(Inverse(M,M[x]), S), Singleton(x)) ==> Equal(Dereference(S,M[x := y]), Union(Difference(Dereference(S,M), Singleton(M[x])), Singleton(y))));
axiom(forall x:int, y:int, S:[int]bool, M:[int]int :: {Dereference(S,M[x := y])} 
     S[x] && !Equal(Intersection(Inverse(M,M[x]), S), Singleton(x)) ==> Equal(Dereference(S,M[x := y]), Union(Dereference(S,M), Singleton(y))));

axiom(forall f:[int]int, x:int :: {Inverse(f,f[x])} Inverse(f,f[x])[x]);
axiom(forall f:[int]int, x:int, y:int :: {Inverse(f,y), f[x]} Inverse(f,y)[x] ==> f[x] == y);

axiom(forall f:[int]int, x:int, y:int :: {Inverse(f[x := y],y)} Equal(Inverse(f[x := y],y), Union(Inverse(f,y), Singleton(x))));
axiom(forall f:[int]int, x:int, y:int, z:int :: {Inverse(f[x := y],z)} y == z || Equal(Inverse(f[x := y],z), Difference(Inverse(f,z), Singleton(x))));

axiom(forall S:[int]bool, T:[int]bool :: {Equal(S,T)} Equal(S,T) <==> Subset(S,T) && Subset(T,S));
axiom(forall x:int, S:[int]bool, T:[int]bool :: {S[x], Subset(S,T)} S[x] && Subset(S,T) ==> T[x]);
axiom(forall S:[int]bool, T:[int]bool :: {Subset(S,T)} Subset(S,T) || (exists x:int :: S[x] && !T[x]));
axiom(forall x:int, S:[int]bool, T:[int]bool :: {S[x], Disjoint(S,T), T[x]} !(S[x] && Disjoint(S,T) && T[x]));
axiom(forall S:[int]bool, T:[int]bool :: {Disjoint(S,T)} Disjoint(S,T) || (exists x:int :: S[x] && T[x]));

function Unified([name][int]int) returns ([int]int);
axiom(forall M:[name][int]int, x:int :: {Unified(M)[x]} Unified(M)[x] == M[Field(x)][x]);
axiom(forall M:[name][int]int, x:int, y:int :: {Unified(M[Field(x) := M[Field(x)][x := y]])} Unified(M[Field(x) := M[Field(x)][x := y]]) == Unified(M)[x := y]);


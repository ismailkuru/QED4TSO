
/////////////////////////////////////////////////////////
// Allocatedness
/////////////////////////////////////////////////////////

type AllocType;

const unique Alloc: AllocType;

const unique Dealloc: AllocType;

const unique Null: AllocType;

axiom (forall a: AllocType :: a == Alloc || a == Dealloc || a == Null);

function IsAlloc(AllocType) returns (bool);
axiom (forall a: AllocType :: {IsAlloc(a)} IsAlloc(a) <==> a == Alloc);

function IsDealloc(AllocType) returns (bool);
axiom (forall a: AllocType :: {IsDealloc(a)} IsDealloc(a) <==> a == Dealloc);

function IsNull(AllocType) returns (bool);
axiom (forall a: AllocType :: {IsNull(a)} IsNull(a) <==> a == Null);

/////////////////////////////////////////////////////////
// Threads
/////////////////////////////////////////////////////////

const unique tid: int;

const unique tidx: int;

axiom 0 < tid && 0 < tidx && tid != tidx;

var Tid: int;

invariant 0 < Tid && tid <= Tid && tidx <= Tid;

record Thread
{
	id: int;
	interrupted: boolean;
	// parked: boolean;
}

var Threads: [int]Thread;

const unique NULL_THREAD: Thread;

invariant (forall i: int :: i <= 0 ==> (Threads[i]) == NULL_THREAD);
invariant (forall i: int :: i >= 0 ==> (Threads[i]).id == i);

// This is the model of native isInterrupted() method of the Thread.java
procedure {:isatomic true} {:ispublic false} Thread_nativeIsInterrupted(this: Thread, clearInterrupted: bool) returns (result: bool)
{
	var guard: bool;
	result := (this.interrupted == True);
	if (result)
	{
		if (clearInterrupted)
		{
			this.interrupted := False;
		}
	}
}

// interrupt() method
procedure {:ispublic false} Thread_interrupt(this: Thread)
{
	this.interrupted := True;
}

// return the current thread
procedure {:ispublic false} {:isatomic true} Thread_currentThread() returns (result: Thread) 
{
	result := Threads[tid];
}

procedure {:ispublic false} Thread_interrupted() returns (result: bool)
{
	var currentThread: Thread;
	// currentThread := Threads[tid];
	call currentThread := Thread_currentThread();
	call result := Thread_nativeIsInterrupted(currentThread, true);
}

/////////////////////////////////////////////////////////
// Exceptions
/////////////////////////////////////////////////////////

type Exception;

const unique ExReturn: Exception;

const unique ExSkip: Exception;

const unique ExBreak: Exception;

const unique ExContinue: Exception;


// common exceptions
const unique NullPointerException: Exception;
const unique InterruptedException: Exception;

/////////////////////////////////////////////////////////
// Subtyping for exceptions
/////////////////////////////////////////////////////////

function subtype(Exception, Exception) returns (bool);
// reflexive
axiom (forall e: Exception :: subtype(e,e));
// transitive
axiom (forall e1,e2,e3: Exception :: {subtype(e1,e2), subtype(e2,e3)} (subtype(e1,e2) && subtype(e2,e3)) ==> subtype(e1,e3));

/////////////////////////////////////////////////////////
// Boolean type
/////////////////////////////////////////////////////////

type boolean;

const unique True: boolean;

const unique False: boolean;

axiom (forall b: boolean :: b == True || b == False);

function toBool(boolean) returns (bool);
axiom (toBool(True) == true) && (toBool(False) == false);

function toBoolean(bool) returns (boolean);
axiom (toBoolean(true) == True) && (toBoolean(false) == False);

/////////////////////////////////////////////////////////
// Long type
/////////////////////////////////////////////////////////

type long = int;

/////////////////////////////////////////////////////////
// Reachability axioms
/////////////////////////////////////////////////////////

// interpreted "store1" function in Boogie
// function store1(f: [T]T, p: T, q: T) returns ([T]T);

////////////////////
// Between predicate
//////////////////// 
function ReachBetween<T>(f: [T]T, x: T, y: T, z: T) returns (bool);
function ReachAvoiding<T>(f: [T]T, x: T, y: T, z: T) returns (bool);


//////////////////////////
// Between set constructor
//////////////////////////
function ReachBetweenSet<T>(f: [T]T, x: T, z: T) returns ([T]bool);

////////////////////////////////////////////////////
// axioms relating ReachBetween and ReachBetweenSet
////////////////////////////////////////////////////
axiom(forall<T> f: [T]T, x: T, y: T, z: T :: {ReachBetweenSet(f, x, z)[y]} ReachBetweenSet(f, x, z)[y] <==> ReachBetween(f, x, y, z));
axiom(forall<T> f: [T]T, x: T, y: T, z: T :: {ReachBetween(f, x, y, z), ReachBetweenSet(f, x, z)} ReachBetween(f, x, y, z) ==> ReachBetweenSet(f, x, z)[y]);
axiom(forall<T> f: [T]T, x: T, z: T :: {ReachBetweenSet(f, x, z)} ReachBetween(f, x, x, x));


//////////////////////////
// Axioms for ReachBetween
//////////////////////////

// reflexive
axiom(forall<T> f: [T]T, x: T :: ReachBetween(f, x, x, x));

// step
//axiom(forall f: [T]T, x: T :: {f[x]} ReachBetween(f, x, f[x], f[x])); 
axiom(forall<T> f: [T]T, x: T, y: T, z: T, w:T :: {ReachBetween(f, y, z, w), f[x]} ReachBetween(f, x, f[x], f[x])); 

// reach
axiom(forall<T> f: [T]T, x: T, y: T :: {f[x], ReachBetween(f, x, y, y)} ReachBetween(f, x, y, y) ==> x == y || ReachBetween(f, x, f[x], y));

// cycle
axiom(forall<T> f: [T]T, x: T, y:T :: {f[x], ReachBetween(f, x, y, y)} f[x] == x && ReachBetween(f, x, y, y) ==> x == y);

// sandwich
axiom(forall<T> f: [T]T, x: T, y: T :: {ReachBetween(f, x, y, x)} ReachBetween(f, x, y, x) ==> x == y);

// order1
axiom(forall<T> f: [T]T, x: T, y: T, z: T :: {ReachBetween(f, x, y, y), ReachBetween(f, x, z, z)} ReachBetween(f, x, y, y) && ReachBetween(f, x, z, z) ==> ReachBetween(f, x, y, z) || ReachBetween(f, x, z, y));

// order2
axiom(forall<T> f: [T]T, x: T, y: T, z: T :: {ReachBetween(f, x, y, z)} ReachBetween(f, x, y, z) ==> ReachBetween(f, x, y, y) && ReachBetween(f, y, z, z));

// transitive1
axiom(forall<T> f: [T]T, x: T, y: T, z: T :: {ReachBetween(f, x, y, y), ReachBetween(f, y, z, z)} ReachBetween(f, x, y, y) && ReachBetween(f, y, z, z) ==> ReachBetween(f, x, z, z));

// transitive2
axiom(forall<T> f: [T]T, x: T, y: T, z: T, w: T :: {ReachBetween(f, x, y, z), ReachBetween(f, y, w, z)} ReachBetween(f, x, y, z) && ReachBetween(f, y, w, z) ==> ReachBetween(f, x, y, w) && ReachBetween(f, x, w, z));

// transitive3
axiom(forall<T> f: [T]T, x: T, y: T, z: T, w: T :: {ReachBetween(f, x, y, z), ReachBetween(f, x, w, y)} ReachBetween(f, x, y, z) && ReachBetween(f, x, w, y) ==> ReachBetween(f, x, w, z) && ReachBetween(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.  
// It cannot be proved using the rest of the axioms.
axiom(forall<T> f: [T]T, u:T, x: T :: {ReachBetween(f, u, x, x)} ReachBetween(f, u, x, x) ==> ReachBetween(f, u, u, x));

// relation between ReachAvoiding and ReachBetween
axiom(forall<T> f: [T]T, x: T, y: T, z: T :: {ReachAvoiding(f, x, y, z)}{ReachBetween(f, x, y, z)} ReachAvoiding(f, x, y, z) <==> (ReachBetween(f, x, y, z) || (ReachBetween(f, x, y, y) && !ReachBetween(f, x, z, z))));

// update
axiom(forall<T> f: [T]T, u: T, v: T, x: T, p: T, q: T :: {ReachAvoiding(f[p := q], u, v, x)} ReachAvoiding(f[p := q], u, v, x) <==> ((ReachAvoiding(f, u, v, p) && ReachAvoiding(f, u, v, x)) || (ReachAvoiding(f, u, p, x) && p != x && ReachAvoiding(f, q, v, p) && ReachAvoiding(f, q, v, x))));


/////////////////////////////////////////////////////////
// Set axioms
/////////////////////////////////////////////////////////

function Equal<T>([T]bool, [T]bool) returns (bool);
function Subset<T>([T]bool, [T]bool) returns (bool);
function Disjoint<T>([T]bool, [T]bool) returns (bool);

function Empty<T>(T) returns ([T]bool);
function Singleton<T>(T) returns ([T]bool);
function Reachable<T>([T,T]bool, T) returns ([T]bool);
function Union<T>([T]bool, [T]bool) returns ([T]bool);
function Intersection<T>([T]bool, [T]bool) returns ([T]bool);
function Difference<T>([T]bool, [T]bool) returns ([T]bool);
function Dereference<T>([T]bool, [T]T) returns ([T]bool);
function Inverse<T>(f:[T]T, x:T) returns ([T]bool);

axiom(forall<T> x,y:T :: !Empty(y)[x]);

axiom(forall<T> x:T, y:T :: {Singleton(y)[x]} Singleton(y)[x] <==> x == y);
axiom(forall<T> y:T :: {Singleton(y)} Singleton(y)[y]);

/* this formulation of Union IS more complete than the earlier one */
/* (A U B)[e], A[d], A U B = Singleton(c), d != e */
axiom(forall<T> x:T, S:[T]bool, T:[T]bool :: {Union(S,T)[x]} Union(S,T)[x] <==> S[x] || T[x]);
axiom(forall<T> x:T, S:[T]bool, T:[T]bool :: {Union(S,T), S[x]} S[x] ==> Union(S,T)[x]);
axiom(forall<T> x:T, S:[T]bool, T:[T]bool :: {Union(S,T), T[x]} T[x] ==> Union(S,T)[x]);

axiom(forall<T> x:T, S:[T]bool, T:[T]bool :: {Intersection(S,T)[x]} Intersection(S,T)[x] <==>  S[x] && T[x]);
axiom(forall<T> x:T, S:[T]bool, T:[T]bool :: {Intersection(S,T), S[x]} S[x] && T[x] ==> Intersection(S,T)[x]);
axiom(forall<T> x:T, S:[T]bool, T:[T]bool :: {Intersection(S,T), T[x]} S[x] && T[x] ==> Intersection(S,T)[x]);

axiom(forall<T> x:T, S:[T]bool, T:[T]bool :: {Difference(S,T)[x]} Difference(S,T)[x] <==> S[x] && !T[x]);
axiom(forall<T> x:T, S:[T]bool, T:[T]bool :: {Difference(S,T), S[x]} S[x] ==> Difference(S,T)[x] || T[x]);

axiom(forall<T> x:T, S:[T]bool, M:[T]T :: {Dereference(S,M)[x]} Dereference(S,M)[x] ==> (exists y:T :: x == M[y] && S[y]));
axiom(forall<T> x:T, S:[T]bool, M:[T]T :: {M[x], S[x], Dereference(S,M)} S[x] ==> Dereference(S,M)[M[x]]);
axiom(forall<T> x:T, y:T, S:[T]bool, M:[T]T :: {Dereference(S,M[x := y])} !S[x] ==> Equal(Dereference(S,M[x := y]), Dereference(S,M)));
axiom(forall<T> x:T, y:T, S:[T]bool, M:[T]T :: {Dereference(S,M[x := y])} 
     S[x] &&  Equal(Intersection(Inverse(M,M[x]), S), Singleton(x)) ==> Equal(Dereference(S,M[x := y]), Union(Difference(Dereference(S,M), Singleton(M[x])), Singleton(y))));
axiom(forall<T> x:T, y:T, S:[T]bool, M:[T]T :: {Dereference(S,M[x := y])} 
     S[x] && !Equal(Intersection(Inverse(M,M[x]), S), Singleton(x)) ==> Equal(Dereference(S,M[x := y]), Union(Dereference(S,M), Singleton(y))));

axiom(forall<T> f:[T]T, x:T :: {Inverse(f,f[x])} Inverse(f,f[x])[x]);
axiom(forall<T> f:[T]T, x:T, y:T :: {Inverse(f,y), f[x]} Inverse(f,y)[x] ==> f[x] == y);

axiom(forall<T> f:[T]T, x:T, y:T :: {Inverse(f[x := y],y)} Equal(Inverse(f[x := y],y), Union(Inverse(f,y), Singleton(x))));
axiom(forall<T> f:[T]T, x:T, y:T, z:T :: {Inverse(f[x := y],z)} y == z || Equal(Inverse(f[x := y],z), Difference(Inverse(f,z), Singleton(x))));

axiom(forall<T> S:[T]bool, T:[T]bool :: {Equal(S,T)} Equal(S,T) <==> Subset(S,T) && Subset(T,S));
axiom(forall<T> x:T, S:[T]bool, T:[T]bool :: {S[x], Subset(S,T)} S[x] && Subset(S,T) ==> T[x]);
axiom(forall<T> S:[T]bool, T:[T]bool :: {Subset(S,T)} Subset(S,T) || (exists x:T :: S[x] && !T[x]));
axiom(forall<T> x:T, S:[T]bool, T:[T]bool :: {S[x], Disjoint(S,T), T[x]} !(S[x] && Disjoint(S,T) && T[x]));
axiom(forall<T> S:[T]bool, T:[T]bool :: {Disjoint(S,T)} Disjoint(S,T) || (exists x:T :: S[x] && T[x]));

/////////////////////////////////////////////////////////
// Connected function
/////////////////////////////////////////////////////////

function Connected<T>(f: [T]T, x: T, y: T) returns (bool);

axiom (forall<T> f: [T]T, x: T, y: T :: {Connected(f, x, y)} Connected(f, x, y) <==> (ReachBetween(f, x, y, y) || ReachBetween(f, y, x, x)));

/////////////////////////////////////////////////////////
// Equality axioms for arrays
/////////////////////////////////////////////////////////

function Equals<T,K>([T]K, [T]K) returns (bool);
axiom(forall<T,K> A,B:[T]K :: {Equals(A,B)} Equals(A,B) || (exists x:T :: A[x] != B[x]));
axiom(forall<T,K> A,B:[T]K, x:T :: {Equals(A,B), A[x]} {Equals(A,B), B[x]} Equals(A,B) <==> (A[x] == B[x]));


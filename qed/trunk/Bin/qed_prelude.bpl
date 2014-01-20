
/////////////////////////////////////////////////////////
// MAX_INT and MIN_INT
/////////////////////////////////////////////////////////

const MAX_INT: int;
const MIN_INT: int;
// axiom (forall i: int :: (i != MIN_INT && i != MAX_INT) ==> (MIN_INT < i && i < MAX_INT));

/////////////////////////////////////////////////////////
// Default models for set, queue and stack
/////////////////////////////////////////////////////////

/********************
// SET
record Set<T> {
  items: [T]bool;
}

procedure {:isatomic} {:autolabel} {:ispublic} {:skipmc} set_add<U>(s: Set U, x: U)
{
  s.items[x] := true;
}

procedure {:isatomic} {:autolabel} {:ispublic} {:skipmc} set_remove<U>(s: Set U, x: U)
{
  s.items[x] := false;
}

procedure {:isatomic} {:autolabel} {:ispublic} {:skipmc} set_contains<U>(s: Set U, x: U) returns(r: bool)
{
  r := (s.items[x] == true);
}
********************/

/********************
// QUEUE
record Queue<T> {
  items: [int]T;
  head: int;
  tail: int;
}

//invariant (forall<U> q: Queue U :: q.head <= q.tail);

procedure {:isatomic} {:autolabel} {:ispublic} {:skipmc} queue_isempty<U>(q: Queue U) returns(e: bool) {
  e := (q.head == q.tail);
}

procedure {:isatomic} {:autolabel} {:ispublic} {:skipmc} queue_enqueue<U>(q: Queue U, x: U) {
     q.items[q.tail] := x;
     q.tail := q.tail + 1;
}

procedure {:isatomic} {:autolabel} {:ispublic} {:skipmc} queue_dequeue<U>(q: Queue U) returns(x: U) {
     assert q.head < q.tail; // queue is not empty
     x := q.items[q.head];
     q.head := q.head + 1;
}
********************/
/*
procedure removeAny() returns(s:Solution) {
  var q: Queue;
  var i: int;
  atomic {
     assert head < tail; // queue is not empty
     havoc i;
     assume head <= i && i < tail;
     s := queue[i];

    // reorganize the queue
    havoc q;
    assume (forall j: int :: head <= j && j < i ==> queue[j] == q[j]);
    assume (forall j: int :: i < j && j < tail ==> queue[j] == q[j-1]);
    queue := q;
  }
}
*/

/********************
// STACK
record Stack<T> {
  items: [int]T;
  top: int;
}

//invariant (forall<U> s: Stack U :: s.top >= -1);

procedure {:isatomic} {:autolabel} {:ispublic} {:skipmc} stack_isempty<U>(s: Stack U) returns(e: bool) {
  e := (s.top == -1);
}

procedure {:isatomic} {:autolabel} {:ispublic} {:skipmc} stack_push<U>(s: Stack U, x: U) {
     s.top := s.top + 1;
     s.items[s.top] := x;
}

procedure {:isatomic} {:autolabel} {:ispublic} {:skipmc} stack_pop<U>(s: Stack U) returns(x: U) {
     assert s.top >= 0; // queue is not empty
     x := s.items[s.top];
     s.top := s.top - 1;
}
********************/

/********************
// PRIORITY QUEUE
record PrioQueue<T> {
  items: [int]T;
  prio: [int]int;
  last: int;
}

//invariant (forall<U> q: Queue U :: q.head <= q.tail);

procedure {:isatomic} {:autolabel} {:ispublic} {:skipmc} prioqueue_isempty<U>(q: PrioQueue U) returns(e: bool) {
  e := (q.last == -1);
}

procedure {:isatomic} {:autolabel} {:ispublic} {:skipmc} prioqueue_enqueue<U>(q: PrioQueue U, x: U, p: int) {
   q.last := q.last + 1;
   q.items[q.last] := x;
   q.prio[q.last] := 1;
}

procedure {:isatomic} {:autolabel} {:ispublic} {:skipmc} prioqueue_dequeue<U>(q: PrioQueue U) returns(x: U, p: int) {
    assert q.last >= 0; // queue is not empty
    x := q.items[q.last];
    p := q.prio[q.last];
    q.last := q.last - 1;
}
********************/

/////////////////////////////////////////////////////////
// owner field of records
/////////////////////////////////////////////////////////

function ThreadLocal(TID) returns(bool);
axiom (forall t: TID :: {ThreadLocal(t)} ThreadLocal(t) <==> (t==tid));


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
// Locking
/////////////////////////////////////////////////////////

record Mutex { owner: TID; }

procedure {:isatomic} {:skipmc} lock(m: Mutex)
{
lock: atomic {
    assume m.owner == 0;
    m.owner := tid;
  }
}

procedure {:isatomic} {:skipmc} trylock(m: Mutex) returns (succ: bool)
{
trylock: atomic {
    succ := m.owner == 0;
    if(succ == true) {
       m.owner := tid;
    }
  }
}

procedure {:isatomic} {:skipmc} unlock(m: Mutex)
{
unlock: atomic {
    assert m.owner == tid;
    m.owner := 0;
  }
}

/////////////////////////////////////////////////////////
// Threads
/////////////////////////////////////////////////////////

type TID = int;

const unique tid: TID;

const unique tidx: TID;

axiom 0 < tid && 0 < tidx && tid != tidx;

const Tid: TID;

axiom 0 < Tid && tid <= Tid && tidx <= Tid;

record Thread
{
	id: TID;
	interrupted: boolean;
	// parked: boolean;
}

var Threads: [int]Thread;

// define the null thread
const unique NULL_THREAD: Thread;
axiom (IsNull(NULL_THREAD.alloc));

//invariant (forall i: int :: i <= 0 ==> (Threads[i]) == NULL_THREAD);
//invariant (forall i: int :: i >= 0 ==> (Threads[i]).id == i);

/********************
// This is the model of native isInterrupted() method of the Thread.java
procedure {:isatomic} {:ispublic} {:skipmc} Thread_nativeIsInterrupted(this: Thread, clearInterrupted: bool) returns (result: bool)
{
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
procedure {:isatomic} {:skipmc} Thread_interrupt(this: Thread)
{
	this.interrupted := True;
}

// return the current thread
procedure {:isatomic} {:skipmc} Thread_currentThread() returns (result: Thread) 
{
	result := Threads[tid];
}
********************/

/*
procedure Thread_interrupted() returns (result: bool)
{
	var currentThread: Thread;
	
	call currentThread := Thread_currentThread();
	call result := Thread_nativeIsInterrupted(currentThread, true);
}
*/

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
const unique Error: Exception;
const unique IllegalMonitorStateException: Exception;
const unique RuntimeException: Exception;

axiom subtype(NullPointerException, RuntimeException);
axiom subtype(IllegalMonitorStateException, RuntimeException);
// Note that in java Error is not a RuntimeException!
// axiom subtype(Error, RuntimeException);

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
/////////////////////////////////////////////////////////

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

/*************************************************/
/************** Ismail added  TSO abstractions : Primitive Types ***************/


invariant (forall t:thread :: t.wb_tail >= t.wb_head);
	
invariant (forall v1,v2:variable :: v1!= v2 <==> v1.addr != v2.addr);
invariant (forall t1,t2:TID :: ThreadPool[t1] != ThreadPool[t2] <==> t1 != t2);
// Bak buna eksik klamis hatirlamadim ! invariant(forall td: TID :: IsBufferEmpty(td,ThreadPool) ==> T);


// Added after Monday(28 Oct.) meeting
invariant(forall addr1,addr2:int :: addr2variable[addr1].addr != addr2variable[addr2].addr ==> addr1 != addr2);

// BU NEDEN TUTMUYOR ACABA MAPIN DIGER TARAFLARINI PATLATTIGIM ICN MI? 
invariant(forall addr1:int :: addr2variable[addr1].addr == addr1);

// BU BIR ASSERTION DISCHARGE INVARIANT'i SONRADAN EKLE
//invariant(forall va:variable:: AllBuffersEmptyForVar(va,ThreadPool) ==> va.value == va.mostRecent);

// Generic buffer related correctness predicates

// Buffer of current thread is empty or not
function IsBufferEmpty(t:TID, th_pool:[TID]thread)returns(bool);
axiom (forall td:TID , thpl : [TID]thread  ::{ IsBufferEmpty(td,thpl) } 
      IsBufferEmpty(td, thpl ) <==>
      	thpl[td].wb_head == thpl[td].wb_tail);
		
function AllBuffersEmpty(th_pool:[TID]thread)returns(bool);
axiom(forall td:TID , t_p:[TID]thread :: t_p[td].wb_head == t_p[td].wb_tail <==> AllBuffersEmpty(t_p));

function AllBuffersEmptyForVar(va:variable, th_pool:[TID]thread)returns(bool);
axiom(forall v:variable, t_p:[TID]thread :: AllBuffersEmptyForVar(v,t_p) <==> (forall td:TID :: !ExistsInBuffer(v,td,t_p)));

function ExistsInBuffer(va:variable , td:TID, th_pool:[TID]thread)returns(bool);
axiom(forall  v:variable,td:TID,t_p:[TID]thread :: (exists index:int :: ((t_p[td].wb_head <= index && index < t_p[td].wb_tail) && (t_p[td].wb[index].addr == v.addr)) <==> ExistsInBuffer(v,td,t_p)));		
		

function flush_mem(adr2var:[int]variable, t:TID, th_pl:[TID]thread)returns([int]variable);
axiom(forall a2v:[int]variable,inb:int, td:TID, t_p:[TID]thread ::  

	t_p[td].wb_head<= inb && inb<t_p[td].wb_tail ==> 
		(flush_mem(a2v,td,t_p)[t_p[td].wb[inb].addr].value == 
		a2v[t_p[td].wb[inb].addr].lastWrittenValue[td] ));
		
axiom(forall a2v:[int]variable,inb:int, td:TID, t_p:[TID]thread ::   
	t_p[td].wb_head<= inb && inb<t_p[td].wb_tail ==> 
		(flush_mem(a2v,td,t_p)[t_p[td].wb[inb].addr].lastWriteToMem == td));

axiom(forall a2v:[int]variable,inb:int, td:TID, t_p:[TID]thread , vr:int::   

	t_p[td].wb_head<= inb && inb<t_p[td].wb_tail  ==> 
		(flush_mem(a2v,td,t_p)[t_p[td].wb[inb].addr].ver == 
		a2v[t_p[td].wb[inb].addr].ver + 1 ));


		
record variable{

	value:int ; // value of variable : Note: ref type may be used
	addr:int; // addr of variable : Note: ref tpye may be used.
	ver:int ; // global version number of a variable
	lastWrittenValue:[TID]int;
	lastWriter:TID;// 
	lastWriteToMem:TID;
	mostRecent:int;
	
	readCounter:[TID]int; // Added for RCU. 
}

record thread{
	
	t_id : TID;
	wb_head:int;
	wb_tail:int;
	wb:[int]assignment;
}


var ThreadPool:[TID]thread;
var addr2variable:[int]variable;

/*
procedure {:isatomic} flush(){

	addr2variable := flush_mem(addr2variable,tid,ThreadPool);
	assume IsBufferEmpty(tid,ThreadPool);
}*/

procedure dummy_while(){
	
		
	while(*){	
		call drainHead();		
	}


}
procedure dummy_emptyBuf_assume(){

	assume IsBufferEmpty(tid,ThreadPool);
}
procedure dummy_emptyBuf(){

	assert IsBufferEmpty(tid,ThreadPool);
	
}

procedure {:isatomic} isAtHeadAndDrain(index:int){
	
var headAddr:int ;

assume index == ThreadPool[tid].wb_head ; 
assume 	ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;

headAddr := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;

addr2variable[headAddr].value := ThreadPool[tid].wb[ThreadPool[tid].wb_head].value;  
addr2variable[headAddr].ver := addr2variable[headAddr].ver + 1;
addr2variable[headAddr].lastWriteToMem := tid;
ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;

}

procedure {:isatomic true} drainHead()
{
	
	
var headAddr:int ;


assume 	ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;	// Buffer has only one element

headAddr := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;

addr2variable[headAddr].value := ThreadPool[tid].wb[ThreadPool[tid].wb_head].value;  
addr2variable[headAddr].ver := addr2variable[headAddr].ver + 1;
addr2variable[headAddr].lastWriteToMem := tid;
ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;

}

procedure {:isatomic true} write_to_ptr(taddr:variable, offset:int, sval:int) returns(result:int){
	
	var as:assignment;
	var headAddr :int;

	//assume (ThreadPool[tid].wb_head <= ThreadPool[tid].wb_tail);
	assume offset >=0 ;
	headAddr := taddr.addr+offset;

	as.value := sval;
	as.addr := headAddr;
		
	ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := as;
	addr2variable[headAddr].lastWrittenValue[tid] := as.value;
	addr2variable[headAddr].lastWriter := tid; 
	addr2variable[headAddr].mostRecent := as.value; 
	result := ThreadPool[tid].wb_tail;
	ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;

	//assert (!IsBufferEmpty(tid,ThreadPool));
	//assert (!AllBuffersEmptyForVar(addr2variable[headAddr],ThreadPool));
}


procedure {:isatomic true} write(taddr:variable, sval : int) returns(result :int){

	var as:assignment;
	
	//assume (ThreadPool[tid].wb_head <= ThreadPool[tid].wb_tail);
	as.value := sval;
	as.addr := taddr.addr;
		
	ThreadPool[tid].wb[ ThreadPool[tid].wb_tail] := as;
	taddr.lastWrittenValue[tid] := as.value;
	taddr.lastWriter := tid;
	taddr.mostRecent := as.value;
	result:= ThreadPool[tid].wb_tail;
	ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
	
	//assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
}


procedure {:isatomic true} read_from_ptr(toRead:variable, offset:int)returns (result:int){
		
	var HD:int;
	var TL:int;
	var addr_of_element:int;
	
	HD := ThreadPool[tid].wb_head;
	TL := ThreadPool[tid].wb_tail;
	
	addr_of_element := toRead.addr + offset;
	
	if(*){
		assume (forall i:int :: HD<=i  && i< TL ==> 
			ThreadPool[tid].wb[i].addr != addr_of_element  );
		
		result := toRead.value;
	
	}
	else{
	
		assume HD < TL;
		havoc result;
		assume (exists i:int:: 
				               (HD<=i && i<TL &&
                                result == ThreadPool[tid].wb[i].value &&		
		                        addr_of_element == ThreadPool[tid].wb[i].addr &&
								(forall j:int:: (i<j&&j<TL) ==> addr_of_element != ThreadPool[tid].wb[j].addr)
					           )
			   );

	}
	
}

procedure {:isatomic true} read(toRead:variable) returns(result : int ){
	var HD:int;
	var TL:int;
	HD := ThreadPool[tid].wb_head;
	TL := ThreadPool[tid].wb_tail;
	
	if(*){
		assume (forall i:int :: HD<=i  && i< TL ==> 
			ThreadPool[tid].wb[i].addr != toRead.addr  );
		
		result := toRead.value;
	
	}
	else{
	
		assume HD < TL;
		havoc result;
		assume (exists i:int:: 
				               (HD<=i && i<TL &&
                                result == ThreadPool[tid].wb[i].value &&		
		                        toRead.addr == ThreadPool[tid].wb[i].addr &&
								(forall j:int:: (i<j&&j<TL) ==> toRead.addr != ThreadPool[tid].wb[j].addr)
					           )
			   );

	}
}
/*********************************************Primitive types for tso**********************************************************/

//invariant (forall v1,v2:variable_heap :: v1!= v2 <==> v1.value[ADDR] != v2.value[ADDR]);

// Added after Monday(28 Oct.) meeting
//invariant(forall ref1,ref2:ref :: ref_to_variable[ref1.addr].value[ADDR] != ref_to_variable[ref2.addr].value[ADDR] ==> ref1.addr != ref2.addr);
//invariant(forall ref1:ref :: ref_to_variable[ref1.addr].value[ADDR] == ref1.addr);
//invariant(forall va:variable_heap,fld:field:: AllBuffersEmptyForVar_heap(va,fld,ThreadPool) ==> va.value[fld] == va.mostRecent[fld]);

// Generic buffer related correctness predicates

function AllBuffersEmptyForVar_heap(va:variable_heap,fld:field, th_pool:[TID]thread)returns(bool);
axiom(forall v:variable_heap, fl:field,t_p:[TID]thread :: AllBuffersEmptyForVar_heap(v,fl,t_p) <==> (forall td:TID :: !ExistsInBuffer_heap(v,fl,td,t_p)));

function ExistsInBuffer_heap(va:variable_heap , fld:field,td:TID, th_pool:[TID]thread)returns(bool);
axiom(forall  v:variable_heap,fl:field,td:TID,t_p:[TID]thread :: (exists index:int :: ((t_p[td].wb_head <= index && index < t_p[td].wb_tail) &&
																				  (t_p[td].wb[index].addr == v.value[ADDR]) && (t_p[td].wb[index].f_n == fl) ) 
																					<==> 
																					ExistsInBuffer_heap(v,fl,td,t_p)));		
		

/************Ismail addded for TSO non-primitive heap types**************/


type field ;
// Any additional subfield can extend these const unique sub_field names
const unique ADDR :field ;
const unique VAL : field ;
const unique VERSION:field ;
const unique NEXT_PTR : field ;



axiom (forall fld:field ::
	fld == ADDR ||
	fld == VAL ||
	fld == VERSION ||
	fld == NEXT_PTR);


record ref{
	addr : int ;
}
	
record variable_heap{
	value:[field]int;// value of variable : holds any addr of any type.
	ver:int ; // global version number of a variable.
	lastWrittenValue:[TID,field]int;
	lastWriter:[field]TID;
	mostRecent:[field]int;
}


record assignment{
	addr:int;
	f_n:field;
	value:int ;
}


var ref_to_variable:[int]variable_heap;	

/*Predicate to check a reference  refers to null heap location*/

function null_reference( reference :ref) returns(bool);
axiom (forall refer:ref :: null_reference(refer) <==> refer.addr == null_heap_allocation.value[ADDR]); 

const unique null_heap_allocation : variable_heap; // 

procedure {:isatomic true} new_heap_variable() returns (reference_to_heap:ref){
	
	
	havoc reference_to_heap;

	assume ref_to_variable[reference_to_heap.addr] != null_heap_allocation;
	
	
}

procedure {:isatomic} isAtHeadAndDrain_heap(index:int){
	
	var headAddr:int ;
	var headField:field;
	var headValue : int;
	var ref_to_flush : ref;
	

	assume index == ThreadPool[tid].wb_head;
	assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail; // Buffer has only one element

	headAddr := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
	headField := ThreadPool[tid].wb[ThreadPool[tid].wb_head].f_n;
	headValue := ThreadPool[tid].wb[ThreadPool[tid].wb_head].value;
	
	
	ref_to_variable[headAddr].value[headField] := ThreadPool[tid].wb[ThreadPool[tid].wb_head].value;
		
	ref_to_variable[headAddr].value[VERSION] := 
		ref_to_variable[headAddr].value[VERSION] + 1;
	ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
	
	
	//assert ref_to_variable[headAddr].mostRecent[headField] == ref_to_variable[headAddr].value[headField]; 
	//assert(!IsBufferEmpty(tid,ThreadPool));
	//assert(!AllBuffersEmptyForVar_heap(ref_to_variable[headAddr],headField,ThreadPool));
}

procedure {:isatomic true} drainHead_heap()
{
	var headAddr:int ;
	var headField:field;
	var headValue : int;
	var ref_to_flush : ref;

	assume (ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail); // Buffer has only one element
	
	headAddr := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
	headField := ThreadPool[tid].wb[ThreadPool[tid].wb_head].f_n;
	headValue := ThreadPool[tid].wb[ThreadPool[tid].wb_head].value;
	
	

	ref_to_variable[headAddr].value[headField] := ThreadPool[tid].wb[ThreadPool[tid].wb_head].value;
		
	ref_to_variable[headAddr].value[VERSION] := 
		ref_to_variable[headAddr].value[VERSION] + 1;
	ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
	
	//assert ref_to_variable[headAddr].value[headField] == ref_to_variable[headAddr].mostRecent[headField];
	//assert 	IsBufferEmpty(tid,ThreadPool);	
}


procedure {:isatomic true} write_heap(taddrR:ref, sval:int, fld:field) returns(result:int){

	var as:assignment;
	var taddr : variable_heap;
	
	
	//assume (ThreadPool[tid].wb_head <= ThreadPool[tid].wb_tail);
	
	taddr := ref_to_variable[taddrR.addr];
	assert taddr.value[ADDR] == taddrR.addr;
	
	as.value := sval;
	as.addr := taddr.value[ADDR];
	as.f_n :=  fld;
		
	ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := as;
	taddr.lastWrittenValue[tid,fld] := as.value;
	taddr.lastWriter[fld] := tid;
	taddr.mostRecent[fld] := as.value;
	result := ThreadPool[tid].wb_tail;
	ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
	
	//assert(!IsBufferEmpty(tid,ThreadPool));
	//assert(!AllBuffersEmptyForVar_heap(ref_to_variable[as.addr],as.f_n,ThreadPool));
}

procedure {:isatomic true} read_heap(toReadR:ref, fld:field) returns(result : int ){

	var toRead : variable_heap;
	
	var HD:int;
	var TL:int;
	
	HD := ThreadPool[tid].wb_head;
	TL := ThreadPool[tid].wb_tail;
	toRead := ref_to_variable[toReadR.addr];

	if(*){
		assume (forall i:int :: HD<=i  && i< TL ==> 
			ThreadPool[tid].wb[i].addr != toRead.value[ADDR]  );
		
		result := toRead.value[VAL];
	
	}
	else{
	
		assume HD < TL;
		havoc result;
		assume (exists i:int:: 
				               (HD<=i && i<TL &&
                                result == ThreadPool[tid].wb[i].value&&		
		                        toRead.value[ADDR] == ThreadPool[tid].wb[i].addr &&
								(forall j:int:: (i<j&&j<TL) ==> toRead.value[ADDR] != ThreadPool[tid].wb[j].addr)
					           )
			   );

	}
}
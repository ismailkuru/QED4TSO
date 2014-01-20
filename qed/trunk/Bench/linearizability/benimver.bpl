var l: variable;

procedure lock_g();
  modifies variable_value;



implementation lock_g()
{
  var old_val: int;
  var tmp_read: int;
  var changed: bool;
  var ex: Exception;
  var fresh_0: int;
  var fresh_1: int;
  var fresh_2: int;
  var fresh_3: int;
  var fresh_4: bool;

  Atomic_5:
    atomic  {  // Non-mover
        old_val := 1;
    }

  Atomic_45:
    atomic  {  // Non-mover
    }

  Atomic_44:
    atomic  {  // Non-mover
        if (old_val == 1)
        {
            c      
        }
    }
}



procedure unl();
  modifies variable_value, variable_ver, variable_lastWriteToMem, thread_wb_head, assignment_value, assignment_addr, thread_wb, variable_lastWrittenValue, variable_lastWriter, variable_mostRecent, thread_wb_tail;



implementation unl()
{
  var w_i: int;
  var ex: Exception;
  var fresh_0: int;
  var fresh_1: assignment;

  Atomic_18:
    atomic  {  // Non-mover
        assume IsBufferEmpty(tid, ThreadPool);
        /* assert true; [Discharged] */
        /* call w_i := write(l, 0); */
        fresh_1.value := 0;
        fresh_1.addr := l.addr;
        ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := fresh_1;
        l.lastWrittenValue[tid] := fresh_1.value;
        l.lastWriter := tid;
        l.mostRecent := fresh_1.value;
        w_i := ThreadPool[tid].wb_tail;
        ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
    }

  Atomic_39:
    atomic  {  // Non-moverzzzzzzzzzzzzzzzzzzzzzzzzzzzz
        if (*)
        {
            assume w_i == ThreadPool[tid].wb_head;
            assert ThreadPool[tid].wb_head + 1 == ThreadPool[tid].wb_tail;
            /* assert true; [Discharged] */
            /* call isAtHeadAndDrain(w_i); */
            assume w_i == ThreadPool[tid].wb_head;
            assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
            fresh_0 := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
            addr2variable[fresh_0].value := ThreadPool[tid].wb[ThreadPool[tid].wb_head].value;
            addr2variable[fresh_0].ver := addr2variable[fresh_0].ver + 1;
            addr2variable[fresh_0].lastWriteToMem := tid;
            ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
        }
    }
}



const MAX_INT: int;

const MIN_INT: int;

function ThreadLocal(TID) returns (bool);

axiom (forall t: TID :: { ThreadLocal(t) } ThreadLocal(t) <==> t == tid);

type AllocType;

const unique Alloc: AllocType;

const unique Dealloc: AllocType;

const unique Null: AllocType;

axiom (forall a: AllocType :: a == Alloc || a == Dealloc || a == Null);

function IsAlloc(AllocType) returns (bool);

axiom (forall a: AllocType :: { IsAlloc(a) } IsAlloc(a) <==> a == Alloc);

function IsDealloc(AllocType) returns (bool);

axiom (forall a: AllocType :: { IsDealloc(a) } IsDealloc(a) <==> a == Dealloc);

function IsNull(AllocType) returns (bool);

axiom (forall a: AllocType :: { IsNull(a) } IsNull(a) <==> a == Null);

record Mutex {
owner: TID;
alloc: AllocType;
}

type TID = int;

const unique tid: TID;

const unique tidx: TID;

axiom 0 < tid && 0 < tidx && tid != tidx;

const Tid: TID;

axiom 0 < Tid && tid <= Tid && tidx <= Tid;

record Thread {
id: TID;
interrupted: boolean;
alloc: AllocType;
owner: TID;
}

var Threads: [int]Thread;

const unique NULL_THREAD: Thread;

axiom IsNull(NULL_THREAD.alloc);

type Exception;

const unique ExReturn: Exception;

const unique ExSkip: Exception;

const unique ExBreak: Exception;

const unique ExContinue: Exception;

const unique NullPointerException: Exception;

const unique InterruptedException: Exception;

const unique Error: Exception;

const unique IllegalMonitorStateException: Exception;

const unique RuntimeException: Exception;

axiom subtype(NullPointerException, RuntimeException);

axiom subtype(IllegalMonitorStateException, RuntimeException);

function subtype(Exception, Exception) returns (bool);

axiom (forall e: Exception :: subtype(e, e));

axiom (forall e1: Exception, e2: Exception, e3: Exception :: { subtype(e1, e2), subtype(e2, e3) } subtype(e1, e2) && subtype(e2, e3) ==> subtype(e1, e3));

type boolean;

const unique True: boolean;

const unique False: boolean;

axiom (forall b: boolean :: b == True || b == False);

function toBool(boolean) returns (bool);

axiom (toBool(True) <==> true) && (toBool(False) <==> false);

function toBoolean(bool) returns (boolean);

axiom toBoolean(true) == True && toBoolean(false) == False;

type long = int;

function ReachBetween<T>(f: [T]T, x: T, y: T, z: T) returns (bool);

function ReachAvoiding<T>(f: [T]T, x: T, y: T, z: T) returns (bool);

function ReachBetweenSet<T>(f: [T]T, x: T, z: T) returns ([T]bool);

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetweenSet(f, x, z)[y] } ReachBetweenSet(f, x, z)[y] <==> ReachBetween(f, x, y, z));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetween(f, x, y, z), ReachBetweenSet(f, x, z) } ReachBetween(f, x, y, z) ==> ReachBetweenSet(f, x, z)[y]);

axiom (forall<T> f: [T]T, x: T, z: T :: { ReachBetweenSet(f, x, z) } ReachBetween(f, x, x, x));

axiom (forall<T> f: [T]T, x: T :: ReachBetween(f, x, x, x));

axiom (forall<T> f: [T]T, x: T, y: T, z: T, w: T :: { ReachBetween(f, y, z, w), f[x] } ReachBetween(f, x, f[x], f[x]));

axiom (forall<T> f: [T]T, x: T, y: T :: { f[x], ReachBetween(f, x, y, y) } ReachBetween(f, x, y, y) ==> x == y || ReachBetween(f, x, f[x], y));

axiom (forall<T> f: [T]T, x: T, y: T :: { f[x], ReachBetween(f, x, y, y) } f[x] == x && ReachBetween(f, x, y, y) ==> x == y);

axiom (forall<T> f: [T]T, x: T, y: T :: { ReachBetween(f, x, y, x) } ReachBetween(f, x, y, x) ==> x == y);

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetween(f, x, y, y), ReachBetween(f, x, z, z) } ReachBetween(f, x, y, y) && ReachBetween(f, x, z, z) ==> ReachBetween(f, x, y, z) || ReachBetween(f, x, z, y));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetween(f, x, y, z) } ReachBetween(f, x, y, z) ==> ReachBetween(f, x, y, y) && ReachBetween(f, y, z, z));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetween(f, x, y, y), ReachBetween(f, y, z, z) } ReachBetween(f, x, y, y) && ReachBetween(f, y, z, z) ==> ReachBetween(f, x, z, z));

axiom (forall<T> f: [T]T, x: T, y: T, z: T, w: T :: { ReachBetween(f, x, y, z), ReachBetween(f, y, w, z) } ReachBetween(f, x, y, z) && ReachBetween(f, y, w, z) ==> ReachBetween(f, x, y, w) && ReachBetween(f, x, w, z));

axiom (forall<T> f: [T]T, x: T, y: T, z: T, w: T :: { ReachBetween(f, x, y, z), ReachBetween(f, x, w, y) } ReachBetween(f, x, y, z) && ReachBetween(f, x, w, y) ==> ReachBetween(f, x, w, z) && ReachBetween(f, w, y, z));

axiom (forall<T> f: [T]T, u: T, x: T :: { ReachBetween(f, u, x, x) } ReachBetween(f, u, x, x) ==> ReachBetween(f, u, u, x));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachAvoiding(f, x, y, z) } { ReachBetween(f, x, y, z) } ReachAvoiding(f, x, y, z) <==> ReachBetween(f, x, y, z) || (ReachBetween(f, x, y, y) && !ReachBetween(f, x, z, z)));

axiom (forall<T> f: [T]T, u: T, v: T, x: T, p: T, q: T :: { ReachAvoiding(f[p := q], u, v, x) } ReachAvoiding(f[p := q], u, v, x) <==> (ReachAvoiding(f, u, v, p) && ReachAvoiding(f, u, v, x)) || (ReachAvoiding(f, u, p, x) && p != x && ReachAvoiding(f, q, v, p) && ReachAvoiding(f, q, v, x)));

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

function Inverse<T>(f: [T]T, x: T) returns ([T]bool);

axiom (forall<T> x: T, y: T :: !Empty(y)[x]);

axiom (forall<T> x: T, y: T :: { Singleton(y)[x] } Singleton(y)[x] <==> x == y);

axiom (forall<T> y: T :: { Singleton(y) } Singleton(y)[y]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Union(S, T)[x] } Union(S, T)[x] <==> S[x] || T[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Union(S, T), S[x] } S[x] ==> Union(S, T)[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Union(S, T), T[x] } T[x] ==> Union(S, T)[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Intersection(S, T)[x] } Intersection(S, T)[x] <==> S[x] && T[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Intersection(S, T), S[x] } S[x] && T[x] ==> Intersection(S, T)[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Intersection(S, T), T[x] } S[x] && T[x] ==> Intersection(S, T)[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Difference(S, T)[x] } Difference(S, T)[x] <==> S[x] && !T[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Difference(S, T), S[x] } S[x] ==> Difference(S, T)[x] || T[x]);

axiom (forall<T> x: T, S: [T]bool, M: [T]T :: { Dereference(S, M)[x] } Dereference(S, M)[x] ==> (exists y: T :: x == M[y] && S[y]));

axiom (forall<T> x: T, S: [T]bool, M: [T]T :: { M[x], S[x], Dereference(S, M) } S[x] ==> Dereference(S, M)[M[x]]);

axiom (forall<T> x: T, y: T, S: [T]bool, M: [T]T :: { Dereference(S, M[x := y]) } !S[x] ==> Equal(Dereference(S, M[x := y]), Dereference(S, M)));

axiom (forall<T> x: T, y: T, S: [T]bool, M: [T]T :: { Dereference(S, M[x := y]) } S[x] && Equal(Intersection(Inverse(M, M[x]), S), Singleton(x)) ==> Equal(Dereference(S, M[x := y]), Union(Difference(Dereference(S, M), Singleton(M[x])), Singleton(y))));

axiom (forall<T> x: T, y: T, S: [T]bool, M: [T]T :: { Dereference(S, M[x := y]) } S[x] && !Equal(Intersection(Inverse(M, M[x]), S), Singleton(x)) ==> Equal(Dereference(S, M[x := y]), Union(Dereference(S, M), Singleton(y))));

axiom (forall<T> f: [T]T, x: T :: { Inverse(f, f[x]) } Inverse(f, f[x])[x]);

axiom (forall<T> f: [T]T, x: T, y: T :: { Inverse(f, y), f[x] } Inverse(f, y)[x] ==> f[x] == y);

axiom (forall<T> f: [T]T, x: T, y: T :: { Inverse(f[x := y], y) } Equal(Inverse(f[x := y], y), Union(Inverse(f, y), Singleton(x))));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { Inverse(f[x := y], z) } y == z || Equal(Inverse(f[x := y], z), Difference(Inverse(f, z), Singleton(x))));

axiom (forall<T> S: [T]bool, T: [T]bool :: { Equal(S, T) } Equal(S, T) <==> Subset(S, T) && Subset(T, S));

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { S[x], Subset(S, T) } S[x] && Subset(S, T) ==> T[x]);

axiom (forall<T> S: [T]bool, T: [T]bool :: { Subset(S, T) } Subset(S, T) || (exists x: T :: S[x] && !T[x]));

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { S[x], Disjoint(S, T), T[x] } !(S[x] && Disjoint(S, T) && T[x]));

axiom (forall<T> S: [T]bool, T: [T]bool :: { Disjoint(S, T) } Disjoint(S, T) || (exists x: T :: S[x] && T[x]));

function Connected<T>(f: [T]T, x: T, y: T) returns (bool);

axiom (forall<T> f: [T]T, x: T, y: T :: { Connected(f, x, y) } Connected(f, x, y) <==> ReachBetween(f, x, y, y) || ReachBetween(f, y, x, x));

function Equals<T,K>([T]K, [T]K) returns (bool);

axiom (forall<T,K> A: [T]K, B: [T]K :: { Equals(A, B) } Equals(A, B) || (exists x: T :: A[x] != B[x]));

axiom (forall<T,K> A: [T]K, B: [T]K, x: T :: { Equals(A, B), A[x] } { Equals(A, B), B[x] } Equals(A, B) <==> A[x] == B[x]);

invariant (forall t: thread :: t.wb_tail >= t.wb_head);

invariant (forall v1: variable, v2: variable :: v1 != v2 <==> v1.addr != v2.addr);

invariant (forall t1: TID, t2: TID :: ThreadPool[t1] != ThreadPool[t2] <==> t1 != t2);

invariant (forall addr1: int, addr2: int :: addr2variable[addr1].addr != addr2variable[addr2].addr ==> addr1 != addr2);

invariant (forall addr1: int :: addr2variable[addr1].addr == addr1);

function IsBufferEmpty(t: TID, th_pool: [TID]thread) returns (bool);

axiom (forall td: TID, thpl: [TID]thread :: { IsBufferEmpty(td, thpl) } IsBufferEmpty(td, thpl) <==> thpl[td].wb_head == thpl[td].wb_tail);

function AllBuffersEmpty(th_pool: [TID]thread) returns (bool);

axiom (forall td: TID, t_p: [TID]thread :: t_p[td].wb_head == t_p[td].wb_tail <==> AllBuffersEmpty(t_p));

function AllBuffersEmptyForVar(va: variable, th_pool: [TID]thread) returns (bool);

axiom (forall v: variable, t_p: [TID]thread :: AllBuffersEmptyForVar(v, t_p) <==> (forall td: TID :: !ExistsInBuffer(v, td, t_p)));

function ExistsInBuffer(va: variable, td: TID, th_pool: [TID]thread) returns (bool);

axiom (forall v: variable, td: TID, t_p: [TID]thread :: (exists index: int :: t_p[td].wb_head <= index && index < t_p[td].wb_tail && t_p[td].wb[index].addr == v.addr <==> ExistsInBuffer(v, td, t_p)));

function flush_mem(adr2var: [int]variable, t: TID, th_pl: [TID]thread) returns ([int]variable);

axiom (forall a2v: [int]variable, inb: int, td: TID, t_p: [TID]thread :: t_p[td].wb_head <= inb && inb < t_p[td].wb_tail ==> flush_mem(a2v, td, t_p)[t_p[td].wb[inb].addr].value == a2v[t_p[td].wb[inb].addr].lastWrittenValue[td]);

axiom (forall a2v: [int]variable, inb: int, td: TID, t_p: [TID]thread :: t_p[td].wb_head <= inb && inb < t_p[td].wb_tail ==> flush_mem(a2v, td, t_p)[t_p[td].wb[inb].addr].lastWriteToMem == td);

axiom (forall a2v: [int]variable, inb: int, td: TID, t_p: [TID]thread, vr: int :: t_p[td].wb_head <= inb && inb < t_p[td].wb_tail ==> flush_mem(a2v, td, t_p)[t_p[td].wb[inb].addr].ver == a2v[t_p[td].wb[inb].addr].ver + 1);

record variable {
value: int;
addr: int;
ver: int;
lastWrittenValue: [TID]int;
lastWriter: TID;
lastWriteToMem: TID;
mostRecent: int;
alloc: AllocType;
owner: TID;
}

record thread {
t_id: TID;
wb_head: int;
wb_tail: int;
wb: [int]assignment;
alloc: AllocType;
owner: TID;
}

var ThreadPool: [TID]thread;

var addr2variable: [int]variable;

function AllBuffersEmptyForVar_heap(va: variable_heap, fld: field, th_pool: [TID]thread) returns (bool);

axiom (forall v: variable_heap, fl: field, t_p: [TID]thread :: AllBuffersEmptyForVar_heap(v, fl, t_p) <==> (forall td: TID :: !ExistsInBuffer_heap(v, fl, td, t_p)));

function ExistsInBuffer_heap(va: variable_heap, fld: field, td: TID, th_pool: [TID]thread) returns (bool);

axiom (forall v: variable_heap, fl: field, td: TID, t_p: [TID]thread :: (exists index: int :: t_p[td].wb_head <= index && index < t_p[td].wb_tail && t_p[td].wb[index].addr == v.value[ADDR] && t_p[td].wb[index].f_n == fl <==> ExistsInBuffer_heap(v, fl, td, t_p)));

type field;

const unique ADDR: field;

const unique VAL: field;

const unique VERSION: field;

const unique NEXT_PTR: field;

axiom (forall fld: field :: fld == ADDR || fld == VAL || fld == VERSION || fld == NEXT_PTR);

record ref {
addr: int;
alloc: AllocType;
owner: TID;
}

record variable_heap {
value: [field]int;
ver: int;
lastWrittenValue: [TID,field]int;
lastWriter: [field]TID;
mostRecent: [field]int;
alloc: AllocType;
owner: TID;
}

record assignment {
addr: int;
f_n: field;
value: int;
alloc: AllocType;
owner: TID;
}

var ref_to_variable: [int]variable_heap;

function null_reference(reference: ref) returns (bool);

axiom (forall refer: ref :: null_reference(refer) <==> refer.addr == null_heap_allocation.value[ADDR]);

const unique null_heap_allocation: variable_heap;

invariant (forall t1: TID, t2: TID :: ThreadPool[t1] != ThreadPool[t2] <==> t1 != t2);

invariant (forall addr1: int, addr2: int :: addr2variable[addr1].addr != addr2variable[addr2].addr ==> addr1 != addr2);

invariant (forall v1: variable, v2: variable :: v1 != v2 <==> v1.addr != v2.addr);

invariant (forall t: thread :: t.wb_tail >= t.wb_head);

invariant (forall addr1: int :: addr2variable[addr1].addr == addr1);


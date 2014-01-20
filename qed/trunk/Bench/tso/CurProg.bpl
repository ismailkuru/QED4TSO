record Node {
addr: int;
value: int;
idx: int;
alloc: AllocType;
owner: TID;
}

record WriteBuffer {
writebuffer: [int]Node;
head: int;
tail: int;
alloc: AllocType;
owner: TID;
}

var Mem: [int]int;

var ThreadWriteBuffers: [TID]WriteBuffer;

invariant (forall wb: WriteBuffer :: wb.head <= wb.tail);

invariant (forall tid: TID, i: int, j: int :: { ThreadWriteBuffers[tid].writebuffer[i], ThreadWriteBuffers[tid].writebuffer[j] } i != j ==> ThreadWriteBuffers[tid].writebuffer[i] != ThreadWriteBuffers[tid].writebuffer[j]);

invariant (forall tid1: TID, tid2: TID :: { ThreadWriteBuffers[tid1], ThreadWriteBuffers[tid2] } tid1 != tid2 ==> ThreadWriteBuffers[tid1] != ThreadWriteBuffers[tid2]);

function UpdateMemSEG(Memory: [int]int, bf: [int]Node, idx: int, idx2: int, Amap: [Node]int, Vmap: [Node]int) returns ([int]int);

axiom (forall addr: int, i: int, ix: int, update: int, M: [int]int, bf: [int]Node, vmap: [Node]int, amap: [Node]int :: i <= ix && i <= update && update < ix && amap[bf[update]] == addr && (forall ls: int :: i <= ls && ls < ix && amap[bf[ls]] == addr ==> ls <= update) ==> UpdateMemSEG(M, bf, i, ix, amap, vmap)[addr] == vmap[bf[update]]);

axiom (forall addr: int, i: int, ix: int, M: [int]int, bf: [int]Node, vmap: [Node]int, amap: [Node]int :: i <= ix && (forall update: int :: i <= update && update < ix ==> amap[bf[update]] != addr) ==> UpdateMemSEG(M, bf, i, ix, amap, vmap)[addr] == M[addr]);

const unique xAddr: int;

const unique yAddr: int;

const unique zAddr: int;

const unique mAddr: int;

const unique kAddr: int;

const unique vAddr: int;

const unique th1: TID;

const unique th2: TID;

const unique th3: TID;

const unique th4: TID;

var ownerMap: [int]TID;

var toReadX: int;

var toReadF: int;

const unique senderThread: TID;

const unique recvThread: TID;

procedure {:ispublic false} send(addrFlag: int, addrX: int, sentvalue: int);
  modifies WriteBuffer_tail, WriteBuffer_head;



implementation send(addrFlag: int, addrX: int, sentvalue: int)
{
  var flagLocal: int;
  var ex: Exception;
  var fresh_0: WriteBuffer;
  var fresh_1: Node;
  var fresh_2: WriteBuffer;
  var fresh_3: Node;
  var fresh_4: WriteBuffer;
  var fresh_5: int;
  var fresh_6: int;
  var fresh_7: WriteBuffer;
  var fresh_8: int;
  var fresh_9: int;
  var fresh_10: WriteBuffer;
  var fresh_11: int;
  var fresh_12: int;
  var fresh_13: WriteBuffer;
  var fresh_14: int;
  var fresh_15: int;

  Atomic_44:
    atomic  {  // Non-mover
        assume senderThread == tid;
		assert senderThread == tid;
    }

  Call_45:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call absdrain(addrFlag, addrX); */
		assert senderThread == tid;
        fresh_4 := ThreadWriteBuffers[tid];
        fresh_5 := fresh_4.head;
        havoc fresh_6;
        assume fresh_5 <= fresh_6 && fresh_6 <= fresh_4.tail;
        fresh_4.head := fresh_6;
        havoc Mem;
        assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_4.writebuffer, fresh_5, fresh_6, Node_addr, Node_value)[addrFlag];
        assume Mem[addrX] == UpdateMemSEG(Mem, fresh_4.writebuffer, fresh_5, fresh_6, Node_addr, Node_value)[addrX];
    }

  Atomic_46:
    atomic  {  // Non-mover
        assume flagLocal == 0;
		assert senderThread == tid;
    }

  Call_47:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call absdrain(addrFlag, addrX); */
		assert senderThread == tid;
        fresh_7 := ThreadWriteBuffers[tid];
        fresh_8 := fresh_7.head;
        havoc fresh_9;
        assume fresh_8 <= fresh_9 && fresh_9 <= fresh_7.tail;
        fresh_7.head := fresh_9;
        havoc Mem;
        assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_7.writebuffer, fresh_8, fresh_9, Node_addr, Node_value)[addrFlag];
        assume Mem[addrX] == UpdateMemSEG(Mem, fresh_7.writebuffer, fresh_8, fresh_9, Node_addr, Node_value)[addrX];
    }

  Call_48:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call write(addrX, sentvalue); */
		assert senderThread == tid;
        fresh_0 := ThreadWriteBuffers[tid];
        fresh_1 := fresh_0.writebuffer[fresh_0.tail];
        assume fresh_1.idx == fresh_0.tail;
        assume fresh_1.addr == sentvalue;
        assume fresh_1.value == addrX;
        fresh_0.tail := fresh_0.tail + 1;
    }

  Call_49:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call absdrain(addrFlag, addrX); */
		assert senderThread == tid;
        fresh_10 := ThreadWriteBuffers[tid];
        fresh_11 := fresh_10.head;
        havoc fresh_12;
        assume fresh_11 <= fresh_12 && fresh_12 <= fresh_10.tail;
        fresh_10.head := fresh_12;
        havoc Mem;
        assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_10.writebuffer, fresh_11, fresh_12, Node_addr, Node_value)[addrFlag];
        assume Mem[addrX] == UpdateMemSEG(Mem, fresh_10.writebuffer, fresh_11, fresh_12, Node_addr, Node_value)[addrX];
    }

  Call_50:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call write(addrFlag, 1); */
		assert senderThread == tid;
        fresh_2 := ThreadWriteBuffers[tid];
        fresh_3 := fresh_2.writebuffer[fresh_2.tail];
        assume fresh_3.idx == fresh_2.tail;
        assume fresh_3.addr == 1;
        assume fresh_3.value == addrFlag;
        fresh_2.tail := fresh_2.tail + 1;
    }

  Call_51:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call absdrain(addrFlag, addrX); */
		assert senderThread == tid;
        fresh_13 := ThreadWriteBuffers[tid];
        fresh_14 := fresh_13.head;
        havoc fresh_15;
        assume fresh_14 <= fresh_15 && fresh_15 <= fresh_13.tail;
        fresh_13.head := fresh_15;
        havoc Mem;
        assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_13.writebuffer, fresh_14, fresh_15, Node_addr, Node_value)[addrFlag];
        assume Mem[addrX] == UpdateMemSEG(Mem, fresh_13.writebuffer, fresh_14, fresh_15, Node_addr, Node_value)[addrX];
    }
}



procedure {:ispublic false} recieve(addrFlag: int, addrX: int) returns (result: int);
  modifies WriteBuffer_tail, WriteBuffer_head;



implementation recieve(addrFlag: int, addrX: int) returns (result: int)
{
  var flagLocal: int;
  var ex: Exception;
  var fresh_0: WriteBuffer;
  var fresh_1: Node;
  var fresh_2: WriteBuffer;
  var fresh_3: Node;
  var fresh_4: WriteBuffer;
  var fresh_5: Node;
  var fresh_6: WriteBuffer;
  var fresh_7: int;
  var fresh_8: int;
  var fresh_9: WriteBuffer;
  var fresh_10: int;
  var fresh_11: int;
  var fresh_12: WriteBuffer;
  var fresh_13: int;
  var fresh_14: int;

  Atomic_52:
    atomic  {  // Non-mover
        assume recvThread == tid;
		assert recvThread == tidl;
    }

  Call_53:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call flagLocal := read(addrFlag); */
		
		assert recvThread == tidl;
        fresh_2 := ThreadWriteBuffers[tid];
        havoc fresh_3;
        if (*)
        {
            assume fresh_3.idx >= fresh_2.head && fresh_3.idx < fresh_2.tail && fresh_2.writebuffer[fresh_3.idx].addr == addrFlag && (forall nodeRecent: Node :: nodeRecent.idx > fresh_3.idx && nodeRecent.idx <= fresh_2.tail ==> nodeRecent.addr != fresh_3.addr && nodeRecent.addr != addrFlag);
            assume (forall nodeLessRecent: Node :: nodeLessRecent.idx >= fresh_2.head && nodeLessRecent.idx < fresh_2.tail && nodeLessRecent.addr == fresh_3.addr ==> fresh_3.idx >= nodeLessRecent.idx);
            flagLocal := fresh_2.writebuffer[fresh_3.idx].value;
        }
        else
        {
            assume (forall nodeNotFound: Node :: nodeNotFound.idx >= fresh_2.head && nodeNotFound.idx < fresh_2.tail && nodeNotFound.addr != fresh_3.addr);
            flagLocal := Mem[fresh_3.addr];
        }
    }

  Atomic_54:
    atomic  {  // Non-mover
        assume flagLocal == 1;
		
		assert recvThread == tidl;
    }

  Call_55:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call absdrain(addrFlag, addrX); */
		
		assert recvThread == tidl;
        fresh_6 := ThreadWriteBuffers[tid];
        fresh_7 := fresh_6.head;
        havoc fresh_8;
        assume fresh_7 <= fresh_8 && fresh_8 <= fresh_6.tail;
        fresh_6.head := fresh_8;
        havoc Mem;
        assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_6.writebuffer, fresh_7, fresh_8, Node_addr, Node_value)[addrFlag];
        assume Mem[addrX] == UpdateMemSEG(Mem, fresh_6.writebuffer, fresh_7, fresh_8, Node_addr, Node_value)[addrX];
    }

  Call_56:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call result := read(addrX); */
		
		assert recvThread == tidl;
        fresh_4 := ThreadWriteBuffers[tid];
        havoc fresh_5;
        if (*)
        {
            assume fresh_5.idx >= fresh_4.head && fresh_5.idx < fresh_4.tail && fresh_4.writebuffer[fresh_5.idx].addr == addrX && (forall nodeRecent: Node :: nodeRecent.idx > fresh_5.idx && nodeRecent.idx <= fresh_4.tail ==> nodeRecent.addr != fresh_5.addr && nodeRecent.addr != addrX);
            assume (forall nodeLessRecent: Node :: nodeLessRecent.idx >= fresh_4.head && nodeLessRecent.idx < fresh_4.tail && nodeLessRecent.addr == fresh_5.addr ==> fresh_5.idx >= nodeLessRecent.idx);
            result := fresh_4.writebuffer[fresh_5.idx].value;
        }
        else
        {
            assume (forall nodeNotFound: Node :: nodeNotFound.idx >= fresh_4.head && nodeNotFound.idx < fresh_4.tail && nodeNotFound.addr != fresh_5.addr);
            result := Mem[fresh_5.addr];
        }
    }

  Call_57:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call absdrain(addrFlag, addrX); */
		
		assert recvThread == tidl;
        fresh_9 := ThreadWriteBuffers[tid];
        fresh_10 := fresh_9.head;
        havoc fresh_11;
        assume fresh_10 <= fresh_11 && fresh_11 <= fresh_9.tail;
        fresh_9.head := fresh_11;
        havoc Mem;
        assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_9.writebuffer, fresh_10, fresh_11, Node_addr, Node_value)[addrFlag];
        assume Mem[addrX] == UpdateMemSEG(Mem, fresh_9.writebuffer, fresh_10, fresh_11, Node_addr, Node_value)[addrX];
    }

  Call_58:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call write(addrFlag, 0); */
		
		assert recvThread == tidl;
        fresh_0 := ThreadWriteBuffers[tid];
        fresh_1 := fresh_0.writebuffer[fresh_0.tail];
        assume fresh_1.idx == fresh_0.tail;
        assume fresh_1.addr == 0;
        assume fresh_1.value == addrFlag;
        fresh_0.tail := fresh_0.tail + 1;
    }

  Call_59:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call absdrain(addrFlag, addrX); */
		
		assert recvThread == tidl;
        fresh_12 := ThreadWriteBuffers[tid];
        fresh_13 := fresh_12.head;
        havoc fresh_14;
        assume fresh_13 <= fresh_14 && fresh_14 <= fresh_12.tail;
        fresh_12.head := fresh_14;
        havoc Mem;
        assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_12.writebuffer, fresh_13, fresh_14, Node_addr, Node_value)[addrFlag];
        assume Mem[addrX] == UpdateMemSEG(Mem, fresh_12.writebuffer, fresh_13, fresh_14, Node_addr, Node_value)[addrX];
    }
}



procedure testSendRecv();



implementation testSendRecv()
{
  var readVal: int;
  var ex: Exception;

  Call_60:
      call send(1, 5, 10);

  Call_61:
      call readVal := recieve(1, 5);

  Atomic_62:
    atomic  {  // Non-mover
        assert readVal == 10;
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

invariant (forall wb: WriteBuffer :: wb.head <= wb.tail);

invariant (forall tid: TID, i: int, j: int :: { ThreadWriteBuffers[tid].writebuffer[i], ThreadWriteBuffers[tid].writebuffer[j] } i != j ==> ThreadWriteBuffers[tid].writebuffer[i] != ThreadWriteBuffers[tid].writebuffer[j]);

invariant (forall tid1: TID, tid2: TID :: { ThreadWriteBuffers[tid1], ThreadWriteBuffers[tid2] } tid1 != tid2 ==> ThreadWriteBuffers[tid1] != ThreadWriteBuffers[tid2]);


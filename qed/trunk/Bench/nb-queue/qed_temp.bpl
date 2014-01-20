type Data;

record Object {
data: Data;
alloc: AllocType;
}

record QueueItem {
next: QueueItem;
value: Object;
alloc: AllocType;
}

record NBQueue {
Head: QueueItem;
Tail: QueueItem;
alloc: AllocType;
}

const unique NULL_OBJECT: Object;

const unique NULL_QUEUE_ITEM: QueueItem;

const unique NULL_NB_QUEUE: NBQueue;

invariant IsNull(NULL_OBJECT.alloc);

invariant IsNull(NULL_QUEUE_ITEM.alloc);

invariant IsNull(NULL_NB_QUEUE.alloc);

procedure NBQueue_enqueue(this: NBQueue, value: Object);
  modifies QueueItem_next, NBQueue_Tail, QueueItem_alloc, QueueItem_value;



implementation NBQueue_enqueue(this: NBQueue, value: Object)
{
  var node: QueueItem;
  var tail: QueueItem;
  var n: QueueItem;
  var guard: bool;
  var ex: Exception;
  var guard_0: bool;
  var k: QueueItem;

  Call_8:
    atomic  {  // Non-mover
        /* assert true; [Discharged] */
        /* call node := CreateQueueItem(value); */
        node := New QueueItem;

        assume node != NULL_QUEUE_ITEM;

        /* assert node.alloc == Alloc; [Discharged] */
        node.next := NULL_QUEUE_ITEM;

        /* assert node.alloc == Alloc; [Discharged] */
        node.value := value;
    }

    while (*)
    {
      Atomic_9:
        atomic  {  // Non-mover
            assert this.alloc == Alloc;
            /* assert this.Tail.alloc == Alloc; [Discharged] */
            assert (forall q: NBQueue :: q.Head != node && q.Tail != node) && IsAlloc(node.alloc) && node.next == NULL_QUEUE_ITEM && (forall item: QueueItem :: { QueueItem_next[item] } item.next != node);
            havoc guard_0, guard, tail, n, k;
            if (*)
            {
                if (ReachBetween(QueueItem_next, this.Tail.next, k, NULL_QUEUE_ITEM) && k != NULL_QUEUE_ITEM)
                {
                    this.Tail := k;
                }
            }
        }
    }

  Atomic_46:
    atomic  {  // Non-mover
        assert this.alloc == Alloc;
        havoc tail;
        assume ReachBetween(QueueItem_next, tail, this.Tail, this.Tail) && (forall item: QueueItem :: ReachBetween(QueueItem_next, tail, item, this.Tail) ==> IsAlloc(item.alloc));
        havoc guard_0, guard, n, ex;
        assert (forall q: NBQueue :: q.Head != node && q.Tail != node) && IsAlloc(node.alloc) && node.next == NULL_QUEUE_ITEM && (forall item: QueueItem :: { QueueItem_next[item] } item.next != node);
        assume this.Tail.next == NULL_QUEUE_ITEM;
        this.Tail.next := node;
        assume ReachBetween(QueueItem_next, tail.next, node, NULL_QUEUE_ITEM);
    }

  Call_15:
    atomic  {  // Non-mover
        assert node != NULL_QUEUE_ITEM && ReachBetween(QueueItem_next, tail.next, node, NULL_QUEUE_ITEM);
        assert this.alloc == Alloc;
        if (this.Tail == tail)
        {
            this.Tail := node;
        }

        havoc guard;
    }
}



procedure NBQueue_dequeue(this: NBQueue) returns (result: Object);
  modifies NBQueue_Head, NBQueue_Tail;



implementation NBQueue_dequeue(this: NBQueue) returns (result: Object)
{
  var head: QueueItem;
  var tail: QueueItem;
  var n: QueueItem;
  var guard: bool;
  var ex: Exception;
  var guard_1: bool;

  Atomic_16:
    atomic  {  // Non-mover
        result := NULL_OBJECT;
    }

    while (*)
    {
      Atomic_56:
        atomic  {  // Non-mover
          Try_58:
            assume true;
            try {
                if (*)
                {
                    if (*)
                    {
                        assert this.alloc == Alloc;
                        havoc head;
                        assume ReachBetween(QueueItem_next, head, this.Head, this.Head) && (forall item: QueueItem :: ReachBetween(QueueItem_next, head, item, this.Head) ==> IsAlloc(item.alloc));
                        havoc tail;
                        assume ReachBetween(QueueItem_next, head, tail, this.Tail) && IsAlloc(tail.alloc);
                        if (head.next == NULL_QUEUE_ITEM)
                        {
                            n := NULL_QUEUE_ITEM;
                        }
                        else
                        {
                            havoc n;
                            assume ReachBetween(QueueItem_next, head.next, n, NULL_QUEUE_ITEM);
                        }

                        havoc guard_1;
                        assume head == tail;

                        if (n == NULL_QUEUE_ITEM)
                        {
                            throw ExReturn;
                        }
                        else
                        {
                            assert this.alloc == Alloc;
                            guard := this.Tail == tail;
                            if (guard)
                            {
                                assert this.alloc == Alloc;
                                /* assert n != NULL_QUEUE_ITEM && ReachBetween(QueueItem_next, this.Tail.next, n, NULL_QUEUE_ITEM); [Discharged] */
                                this.Tail := n;
                            }
                        }
                    }
                    else
                    {
                        assert this.alloc == Alloc;
                        havoc head;
                        assume ReachBetween(QueueItem_next, head, this.Head, this.Head) && (forall item: QueueItem :: ReachBetween(QueueItem_next, head, item, this.Head) ==> IsAlloc(item.alloc));
                        havoc tail;
                        assume ReachBetween(QueueItem_next, head, tail, this.Tail) && IsAlloc(tail.alloc);

                        /* assert head.alloc == Alloc; [Discharged] */
                        n := head.next;

                        assert this.alloc == Alloc;
                        havoc guard_1;

                        assume guard_1;

                        assume head != tail;

                        /* assert n.alloc == Alloc; [Discharged] */
                        result := n.value;

                        /* assert this.alloc == Alloc; [Discharged] */
                        guard := this.Head == head;
                        if (guard)
                        {
                            /* assert this.alloc == Alloc; [Discharged] */
                            /* assert n != NULL_QUEUE_ITEM && ReachBetween(QueueItem_next, this.Head.next, n, this.Tail); [Discharged] */
                            this.Head := n;
                        }

                        if (guard)
                        {
                            throw ExReturn;
                        }
                    }
                }
                else
                {
                    assert this.alloc == Alloc;
                    havoc head, tail, n, guard_1;
                }
}
            catch {
              Atomic_57:
                atomic  {  // Non-mover
                    assume false;
                }
            }
        }
    }

  Atomic_60:
    atomic  {  // Non-mover
        if (true)
        {
            if (*)
            {
                if (*)
                {
                    assert this.alloc == Alloc;
                    havoc head;
                    assume ReachBetween(QueueItem_next, head, this.Head, this.Head) && (forall item: QueueItem :: ReachBetween(QueueItem_next, head, item, this.Head) ==> IsAlloc(item.alloc));
                    havoc tail;
                    assume ReachBetween(QueueItem_next, head, tail, this.Tail) && IsAlloc(tail.alloc);
                    if (head.next == NULL_QUEUE_ITEM)
                    {
                        n := NULL_QUEUE_ITEM;
                    }
                    else
                    {
                        havoc n;
                        assume ReachBetween(QueueItem_next, head.next, n, NULL_QUEUE_ITEM);
                    }

                    havoc guard_1;
                    assume head == tail;

                    if (n == NULL_QUEUE_ITEM)
                    {
                        return;
                    }
                    else
                    {
                        assert this.alloc == Alloc;
                        guard := this.Tail == tail;
                        if (guard)
                        {
                            assert this.alloc == Alloc;
                            /* assert n != NULL_QUEUE_ITEM && ReachBetween(QueueItem_next, this.Tail.next, n, NULL_QUEUE_ITEM); [Discharged] */
                            this.Tail := n;
                        }
                    }
                }
                else
                {
                    assert this.alloc == Alloc;
                    havoc head;
                    assume ReachBetween(QueueItem_next, head, this.Head, this.Head) && (forall item: QueueItem :: ReachBetween(QueueItem_next, head, item, this.Head) ==> IsAlloc(item.alloc));
                    havoc tail;
                    assume ReachBetween(QueueItem_next, head, tail, this.Tail) && IsAlloc(tail.alloc);

                    /* assert head.alloc == Alloc; [Discharged] */
                    n := head.next;

                    assert this.alloc == Alloc;
                    havoc guard_1;

                    assume guard_1;

                    assume head != tail;

                    /* assert n.alloc == Alloc; [Discharged] */
                    result := n.value;

                    /* assert this.alloc == Alloc; [Discharged] */
                    guard := this.Head == head;
                    if (guard)
                    {
                        /* assert this.alloc == Alloc; [Discharged] */
                        /* assert n != NULL_QUEUE_ITEM && ReachBetween(QueueItem_next, this.Head.next, n, this.Tail); [Discharged] */
                        this.Head := n;
                    }

                    if (guard)
                    {
                        return;
                    }
                }
            }
            else
            {
                assert this.alloc == Alloc;
                havoc head, tail, n, guard_1;
            }

          Atomic_59:
            atomic  {  // Non-mover
                assume false;
            }
        }
    }
}



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
}

var Threads: [int]Thread;

const unique NULL_THREAD: Thread;

axiom IsNull(NULL_THREAD.alloc);

invariant (forall i: int :: i <= 0 ==> Threads[i] == NULL_THREAD);

invariant (forall i: int :: i >= 0 ==> Threads[i].id == i);

procedure {:isatomic} {:ispublic} Thread_nativeIsInterrupted(this: Thread, clearInterrupted: bool) returns (result: bool);
  modifies Thread_interrupted;



implementation Thread_nativeIsInterrupted(this: Thread, clearInterrupted: bool) returns (result: bool)
{
  var ex: Exception;

  Atomic_26:
    atomic  {  // Non-mover
        assert this.alloc == Alloc;
        result := this.interrupted == True;
        if (result)
        {
            if (clearInterrupted)
            {
                assert this.alloc == Alloc;
                this.interrupted := False;
            }
        }
    }
}



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

invariant (forall item: QueueItem :: !IsAlloc(item.alloc) ==> item.next == NULL_QUEUE_ITEM);

invariant (forall q: NBQueue, item: QueueItem :: ReachBetween(QueueItem_next, q.Head, item, q.Tail) ==> IsAlloc(item.alloc)) && (forall q: NBQueue :: ReachBetween(QueueItem_next, q.Head, q.Tail, NULL_QUEUE_ITEM)) && (forall q: NBQueue, item: QueueItem :: ReachBetween(QueueItem_next, q.Head, item, NULL_QUEUE_ITEM) && item != NULL_QUEUE_ITEM ==> IsAlloc(item.alloc));


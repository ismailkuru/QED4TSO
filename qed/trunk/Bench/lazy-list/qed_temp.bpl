type nextType = [Node]Node;

type valType = [Node]int;

type markedType = [Node]boolean;

type verType = [int]int;

var AbsSet: [int]bool;

var Hnext: [int]nextType;

var Hmarked: [int]markedType;

var Hver: [int]verType;

var Hcount: int;

invariant 0 <= Hcount;

function IsIn(head: Node, next: nextType, marked: markedType, val: valType, k: int) returns (res: bool);

axiom (forall head: Node, next: nextType, marked: markedType, val: valType, k: int :: { IsIn(head, next, marked, val, k) } IsIn(head, next, marked, val, k) <==> (exists n: Node :: n != null && marked[n] == False && val[n] == k && ReachBetween(next, head, n, n)));

function IsOut(head: Node, next: nextType, marked: markedType, val: valType, k: int) returns (res: bool);

axiom (forall head: Node, next: nextType, marked: markedType, val: valType, k: int :: { IsOut(head, next, marked, val, k) } IsOut(head, next, marked, val, k) <==> (forall n: Node :: n != null && val[n] == k && ReachBetween(next, head, n, n) ==> marked[n] == True));

invariant (forall n: Node :: IsDealloc(n.alloc) ==> n.next == n);

invariant (forall m: Node, n: Node :: IsDealloc(n.alloc) && m.next == n ==> m == n);

invariant ReachBetween(Node_next, Head, null, null) && null.next == null;

invariant (forall n: Node :: ReachBetween(Node_next, Head, n, n) && n != null ==> IsAlloc(n.alloc));

invariant (forall m: Node, n: Node :: ReachBetween(Node_next, Head, m, n) && n != null && m != null && m != n ==> m.val < n.val);

invariant (forall k: int, s: int, t: int :: s <= t && t <= Hcount ==> Hver[s][k] <= Hver[t][k]);

invariant (forall s: int, t: int, k: int, m: Node, n: Node :: { ReachBetween(Hnext[s], m, n, n), Hver[s][k], Hver[t][k] } s <= t && t <= Hcount && Hver[s][k] == Hver[t][k] && ReachBetween(Hnext[s], Head, n, n) && n.val == k && ReachBetween(Hnext[s], m, n, n) ==> ReachBetween(Hnext[t], m, n, n));

invariant (forall s: int, k: int, m: Node, n: Node :: s < Hcount && Hver[s][k] == Hver[s + 1][k] && m != null && n != null && IsOut(Head, Hnext[s], Hmarked[s], Node_val, k) && ReachBetween(Hnext[s + 1], m, n, n) && ReachBetween(Hnext[s], Head, m, m) ==> n.val != k || n.marked == True);

record Node {
next: Node;
val: int;
marked: boolean;
mutex: Mutex;
alloc: AllocType;
}

const unique null: Node;

invariant IsNull(null.alloc);

const Head: Node;

axiom IsAlloc(Head.alloc);

procedure {:ispublic false} locate(e: int) returns (pred: Node, curr: Node);



implementation locate(e: int) returns (pred: Node, curr: Node)
{
  var guard: bool;
  var valid: bool;
  var ex: Exception;

    while (true)
    {
      Atomic_1:
        atomic  {  // Non-mover
            pred := Head;

            curr := pred.next;

            guard := curr.val < e;
        }

        while (guard)
        {
          Atomic_4:
            atomic  {  // Non-mover
                pred := curr;

                curr := curr.next;

                guard := curr.val < e;
            }
        }

      Call_7:
          call lock(pred.mutex);

      Call_8:
          call lock(curr.mutex);

      Call_9:
          call valid := validate(pred, curr);

      Atomic_39:
        atomic  {  // Both-mover
            if (valid)
            {
                return;
            }
        }

      Call_11:
          call unlock(pred.mutex);

      Call_12:
          call unlock(curr.mutex);
    }
}



procedure {:ispublic false} validate(pred: Node, curr: Node) returns (res: bool);



implementation validate(pred: Node, curr: Node) returns (res: bool)
{
  var ex: Exception;

  Atomic_13:
    atomic  {  // Non-mover
        res := pred.marked == False;
    }

    if (res)
    {
      Atomic_14:
        atomic  {  // Non-mover
            res := curr.marked == False;
        }

      Atomic_40:
        atomic  {  // Right-mover
            if (res)
            {
                res := pred.next == curr;

                return;
            }
        }
    }
}



procedure Contains(e: int) returns (res: bool);



implementation Contains(e: int) returns (res: bool)
{
  var pred: Node;
  var curr: Node;
  var guard: bool;
  var marked: bool;
  var qseq: [int]int;
  var qcount: int;
  var cseq: [int]Node;
  var ex: Exception;

  Atomic_17:
    atomic  {  // Right-mover
        assume qseq[0] <= Hcount;
        cseq[0] := Head;
        qcount := 1;
        curr := Head;

        guard := curr.val < e;
    }

    while (guard)
    {
      Atomic_19:
        atomic  {  // Right-mover
            assume qseq[qcount - 1] <= qseq[qcount] && qseq[qcount] <= Hcount;
            curr := Hnext[qseq[qcount]][curr];
            cseq[qcount] := curr;
            qcount := qcount + 1;

            guard := curr.val < e;
        }
    }

  Atomic_21:
    atomic  {  // Right-mover
        assume qseq[qcount - 1] <= qseq[qcount] && qseq[qcount] <= Hcount;
        marked := Hmarked[qseq[qcount]][curr] == True;
        qcount := qcount + 1;

        if (marked)
        {
            res := false;
        }
        else
        {
            res := curr.val == e;
        }

        assert ((forall i: int :: 0 <= i && i <= qseq[qcount - 1] ==> IsIn(Head, Hnext[i], Hmarked[i], Node_val, e)) ==> res) && ((forall i: int :: 0 <= i && i <= qseq[qcount - 1] ==> IsOut(Head, Hnext[i], Hmarked[i], Node_val, e)) ==> !res);
    }
}



procedure Add(e: int) returns (res: bool);
  modifies Node_alloc, Node_next;



implementation Add(e: int) returns (res: bool)
{
  var n1: Node;
  var n2: Node;
  var n3: Node;
  var guard: bool;
  var ex: Exception;

  Call_23:
      call n1, n3 := locate(e);

  Atomic_24:
    atomic  {  // Non-mover
        guard := n3.val != e;

        if (guard)
        {
            assume Hnext[Hcount] == Node_next;
            assume Hmarked[Hcount] == Node_marked;
            assert IsAlloc(n1.alloc);
            assert IsAlloc(n3.alloc) || n3 == null;
            assert n1.val < e;
            assert n3 != null ==> e < n3.val;
            assert n1.next == n3;
            n2 := New Node;
            assume n2.marked == False;
            assume n2.val == e;
            n2.next := n3;
            n1.next := n2;
            assert AbsSet[e] <==> false;
            AbsSet[e] := true;
            Hcount := Hcount + 1;
            Hnext[Hcount] := Node_next;
            Hmarked[Hcount] := Hmarked[Hcount - 1];
            Hver[Hcount] := Hver[Hcount - 1];
            Hver[Hcount][e] := Hver[Hcount][e] + 1;

            res := true;
        }
        else
        {
            res := false;
            assert AbsSet[e] <==> true;
        }
    }

  Call_28:
      call unlock(n1.mutex);

  Call_29:
      call unlock(n3.mutex);
}



procedure Remove(e: int) returns (res: bool);
  modifies Node_marked, Node_next;



implementation Remove(e: int) returns (res: bool)
{
  var n1: Node;
  var n2: Node;
  var n3: Node;
  var guard: bool;
  var ex: Exception;

  Call_30:
      call n1, n2 := locate(e);

  Atomic_31:
    atomic  {  // Both-mover
        guard := n2.val == e;
    }

    if (guard)
    {
      Atomic_32:
        atomic  {  // Non-mover
            assume Hnext[Hcount] == Node_next;
            assume Hmarked[Hcount] == Node_marked;
            assert IsAlloc(n1.alloc);
            assert IsAlloc(n2.alloc);
            assert n1.val < e && e == n2.val;
            assert n1.next == n2;
            n2.marked := True;
            assert AbsSet[e] <==> true;
            AbsSet[e] := false;
            Hcount := Hcount + 1;
            Hnext[Hcount] := Node_next;
            Hmarked[Hcount] := Node_marked;
            Hver[Hcount] := Hver[Hcount - 1];
            Hver[Hcount][e] := Hver[Hcount][e] + 1;
        }

      Atomic_33:
        atomic  {  // Non-mover
            n3 := n2.next;
        }

      Atomic_34:
        atomic  {  // Non-mover
            assume Hnext[Hcount] == Node_next;
            assume Hmarked[Hcount] == Node_marked;
            assert IsAlloc(n1.alloc);
            assert IsAlloc(n3.alloc) || n3 == null;
            assert IsAlloc(n2.alloc);
            assert n1.val < e && e == n2.val;
            assert n1.next == n2 && n2.next == n3;
            assert n3 != null ==> e < n3.val;
            assert n2.marked == True;
            n1.next := n3;
            Hcount := Hcount + 1;
            Hnext[Hcount] := Node_next;
            Hmarked[Hcount] := Node_marked;
            Hver[Hcount] := Hver[Hcount - 1];
            Hver[Hcount][e] := Hver[Hcount][e] + 1;

            res := true;
        }
    }
    else
    {
      Atomic_36:
        atomic  {  // Non-mover
            res := false;
            assert AbsSet[e] <==> false;
        }
    }

  Call_37:
      call unlock(n1.mutex);

  Call_38:
      call unlock(n2.mutex);
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
owner: int;
alloc: AllocType;
}

procedure {:isatomic} lock(m: Mutex);
  modifies Mutex_owner;



implementation lock(m: Mutex)
{
  var ex: Exception;

  Body:
    atomic  {  // Right-mover
        assume m.owner == 0;
        m.owner := tid;
    }
}



procedure {:isatomic} unlock(m: Mutex);
  modifies Mutex_owner;



implementation unlock(m: Mutex)
{
  var ex: Exception;

  Body:
    atomic  {  // Left-mover
        assert m.owner == tid;
        m.owner := 0;
    }
}



type TID = int;

const unique tid: TID;

const unique tidx: TID;

axiom 0 < tid && 0 < tidx && tid != tidx;

var Tid: TID;

invariant 0 < Tid && tid <= Tid && tidx <= Tid;

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

  Body:
    atomic  {  // Non-mover
        result := this.interrupted == True;
        if (result)
        {
            if (clearInterrupted)
            {
                this.interrupted := False;
            }
        }
    }
}



procedure {:isatomic} Thread_interrupt(this: Thread);
  modifies Thread_interrupted;



implementation Thread_interrupt(this: Thread)
{
  var ex: Exception;

  Body:
    atomic  {  // Non-mover
        this.interrupted := True;
    }
}



procedure {:isatomic} Thread_currentThread() returns (result: Thread);



implementation Thread_currentThread() returns (result: Thread)
{
  var ex: Exception;

  Body:
    atomic  {  // Both-mover
        result := Threads[tid];
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


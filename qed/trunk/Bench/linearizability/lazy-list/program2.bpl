record Node {
key: int;
next: Node;
marked: boolean;
alloc: AllocType;
owner: TID;
}

type nextType = [Node]Node;

type keyType = [Node]int;

type markedType = [Node]boolean;

type allocType = [Node]AllocType;

var Hnext: [int]nextType;

var Hmarked: [int]markedType;

var Halloc: [int]allocType;

var Hcount: int;

const unique null: Node;

const unique Head: Node;

const unique Tail: Node;

const E: int;

axiom MIN_INT < E && E < MAX_INT;

procedure contains(e: int) returns (wasPresent: bool);



implementation contains(e: int) returns (wasPresent: bool)
{
  var pred: Node;
  var curr: Node;
  var qseq: [int]int;
  var qcount: int;
  var ex: Exception;

  Atomic_1:
    atomic  {  // Non-mover
        assume e == E;
        havoc qseq, qcount, pred, curr;
        assume 1 <= qcount;
        assume (forall i: int :: { qseq[i] } 1 <= i && i <= qcount ==> 0 <= qseq[i] && qseq[i] <= Hcount);
        assume (forall i: int, j: int :: { qseq[i], qseq[j] } 1 <= i && i <= j && j <= qcount ==> qseq[i] <= qseq[j]);
        assume (exists m: Node :: m.key == e && ReachBetweenSet(Hnext[qseq[qcount]], curr, Tail)[m] && (forall i: int :: { qseq[i] } 1 <= i && i <= qcount ==> Hmarked[qseq[i]][m] == False && ReachBetweenSet(Hnext[qseq[i]], Head, Tail)[m]));
        assume curr.key <= e;
    }

    while (*)
    {
      Atomic_10:
        atomic  {  // Non-mover
            assume curr.key < e;
            assume e == E;
            /* assert 1 <= qcount; [Discharged] */
            assume 1 <= qcount;
            /* assert 0 <= qseq[qcount] && qseq[qcount] <= Hcount; [Discharged] */
            assume 0 <= qseq[qcount] && qseq[qcount] <= Hcount;
            /* assert (exists m: Node :: m.key == e && Hmarked[qseq[qcount]][m] == False && ReachBetweenSet(Hnext[qseq[qcount]], Head, Tail)[m] && ReachBetweenSet(Hnext[qseq[qcount]], curr, Tail)[m]); [Discharged] */
            assume (exists m: Node :: m.key == e && Hmarked[qseq[qcount]][m] == False && ReachBetweenSet(Hnext[qseq[qcount]], Head, Tail)[m] && ReachBetweenSet(Hnext[qseq[qcount]], curr, Tail)[m]);
            pred := curr;
            assume qseq[qcount] <= qseq[qcount + 1] && qseq[qcount + 1] <= Hcount;
            qcount := qcount + 1;
            curr := Hnext[qseq[qcount]][pred];
            /* assert (exists m: Node :: m.key == e && Hmarked[qseq[qcount]][m] == False && ReachBetweenSet(Hnext[qseq[qcount]], Head, Tail)[m] && ReachBetweenSet(Hnext[qseq[qcount]], curr, Tail)[m]); [Discharged] */
            assume (exists m: Node :: m.key == e && Hmarked[qseq[qcount]][m] == False && ReachBetweenSet(Hnext[qseq[qcount]], Head, Tail)[m] && ReachBetweenSet(Hnext[qseq[qcount]], curr, Tail)[m]);
            /* assert curr.key <= e; [Discharged] */
            assume curr.key <= e;
        }
    }

  Atomic_22:
    atomic  {  // Non-mover
        assume curr.key >= e;
        assume e == E;
        wasPresent := curr.key == e && curr.marked == False;
        /* assert wasPresent <==> true; [Discharged] */
        assume wasPresent <==> true;
    }
}



procedure add(e: int) returns (wasPresent: bool);
  modifies Node_alloc, Node_marked, Node_next;



implementation add(e: int) returns (wasPresent: bool)
{
  var pred: Node;
  var curr: Node;
  var tmp: Node;
  var ex: Exception;

    while (true)
    {
      Atomic_26:
        atomic  {  // Non-mover
            assume MIN_INT < e && e < MAX_INT;
            assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, pred, Tail)[Tail];
            assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, curr, Tail)[Tail];
            assert pred == Head || !ReachBetweenSet(Node_next, pred, Head)[Head];
            assert !ReachBetweenSet(Node_next, curr, Head)[Head];
            assert pred != Tail && curr != Head;
            assert pred.key < e && e <= curr.key;
            assume Hnext[Hcount] == Node_next;
            assume Hmarked[Hcount] == Node_marked;
            assume Halloc[Hcount] == Node_alloc;
            if (pred.next == curr && pred.marked == False)
            {
                wasPresent := curr.key == e;
                assume e == E ==> wasPresent;
                if (!wasPresent)
                {
                    tmp := New Node;
                    tmp.marked := False;
                    assume tmp.key == e;
                    tmp.next := curr;
                    pred.next := tmp;
                    Hcount := Hcount + 1;
                    Hnext[Hcount] := Node_next;
                    Hmarked[Hcount] := Node_marked;
                    Halloc[Hcount] := Node_alloc;
                }

                return;
            }
        }
    }
}



procedure remove(e: int) returns (wasPresent: bool);
  modifies Node_marked, Node_next;



implementation remove(e: int) returns (wasPresent: bool)
{
  var pred: Node;
  var curr: Node;
  var ex: Exception;

    while (true)
    {
      Atomic_28:
        atomic  {  // Non-mover
            assume MIN_INT < e && e < MAX_INT;
            assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, pred, Tail)[Tail];
            assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, curr, Tail)[Tail];
            assert pred == Head || !ReachBetweenSet(Node_next, pred, Head)[Head];
            assert !ReachBetweenSet(Node_next, curr, Head)[Head];
            assert pred != Tail && curr != Head;
            assert pred.key < e && e <= curr.key;
            assume Hnext[Hcount] == Node_next;
            assume Hmarked[Hcount] == Node_marked;
            assume Halloc[Hcount] == Node_alloc;
            if (pred.next == curr && pred.marked == False)
            {
                wasPresent := curr.key == e;
                assume wasPresent ==> e != E;
                if (wasPresent)
                {
                    curr.marked := True;
                    pred.next := curr.next;
                    Hcount := Hcount + 1;
                    Hnext[Hcount] := Node_next;
                    Hmarked[Hcount] := Node_marked;
                    Halloc[Hcount] := Node_alloc;
                }

                return;
            }
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

procedure {:isatomic} {:skipmc} lock(m: Mutex);
  modifies Mutex_owner;



implementation lock(m: Mutex)
{
  var ex: Exception;

  lock:
    atomic  {  // Non-mover
        assume m.owner == 0;
        m.owner := tid;
    }
}



procedure {:isatomic} {:skipmc} unlock(m: Mutex);
  modifies Mutex_owner;



implementation unlock(m: Mutex)
{
  var ex: Exception;

  unlock:
    atomic  {  // Non-mover
        assert m.owner == tid;
        m.owner := 0;
    }
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

invariant Head.key == MIN_INT && Tail.key == MAX_INT;

invariant (forall n: Node :: { n.alloc } IsNull(n.alloc) <==> n == null);

invariant IsAlloc(Head.alloc) && IsAlloc(Tail.alloc) && Tail.next == null && null.next == null && (forall n: Node :: { ReachBetweenSet(Node_next, n, Tail)[Tail] } { n.alloc } IsAlloc(n.alloc) <==> ReachBetweenSet(Node_next, n, Tail)[Tail]) && (forall n: Node :: { n.alloc } !IsAlloc(n.alloc) ==> n.next == n);

invariant (forall n: Node :: { n.next } n.next != Head);

invariant (forall n: Node :: { ReachBetweenSet(Node_next, Head, Tail)[n] } { n.marked } ReachBetweenSet(Node_next, Head, Tail)[n] <==> n.marked == False);

invariant (forall n: Node, m: Node :: { ReachBetweenSet(Node_next, n, m)[m] } { n.alloc, m.alloc } IsAlloc(n.alloc) && IsAlloc(m.alloc) && n != m && ReachBetweenSet(Node_next, n, m)[m] ==> n.key < m.key);

invariant (forall n: Node :: { ReachBetweenSet(Node_next, Head, Tail)[n] } ReachBetweenSet(Node_next, Head, Tail)[n] ==> ReachBetweenSet(Node_next, n, Tail)[Tail]);

invariant (forall n: Node, m: Node :: { ReachBetweenSet(Node_next, n, Tail)[m] } ReachBetweenSet(Node_next, n, Tail)[m] ==> ReachBetweenSet(Node_next, n, m)[m]);

invariant (forall n: Node, m: Node :: { ReachBetweenSet(Node_next, Head, m)[n] } ReachBetweenSet(Node_next, Head, m)[n] ==> ReachBetweenSet(Node_next, n, m)[m]);

invariant 0 <= Hcount;

invariant Hnext[Hcount] == Node_next && Hmarked[Hcount] == Node_marked && Halloc[Hcount] == Node_alloc;

invariant (forall i: int, n: Node :: { Halloc[i][n] } IsNull(Halloc[i][n]) <==> n == null);

invariant (forall i: int :: IsAlloc(Halloc[i][Head]) && IsAlloc(Halloc[i][Tail]) && Hnext[i][Tail] == null && Hnext[i][null] == null);

invariant (forall i: int, n: Node :: { ReachBetweenSet(Hnext[i], n, Tail)[Tail] } { Halloc[i][n] } IsAlloc(Halloc[i][n]) <==> ReachBetweenSet(Hnext[i], n, Tail)[Tail]);

invariant (forall i: int, n: Node :: { Hnext[i][n] } { Halloc[i][n] } !IsAlloc(Halloc[i][n]) ==> Hnext[i][n] == n);

invariant (forall i: int, n: Node :: { Hnext[i][n] } Hnext[i][n] != Head);

invariant (forall i: int, n: Node :: { ReachBetweenSet(Hnext[i], Head, Tail)[n] } { Hmarked[i][n] } ReachBetweenSet(Hnext[i], Head, Tail)[n] <==> Hmarked[i][n] == False);

invariant (forall i: int, n: Node, m: Node :: { ReachBetweenSet(Hnext[i], n, m)[m] } { Halloc[i][n], Halloc[i][m] } IsAlloc(Halloc[i][n]) && IsAlloc(Halloc[i][m]) && n != m && ReachBetweenSet(Hnext[i], n, m)[m] ==> n.key < m.key);

invariant (forall i: int, n: Node :: { ReachBetweenSet(Hnext[i], Head, Tail)[n] } ReachBetweenSet(Hnext[i], Head, Tail)[n] ==> ReachBetweenSet(Hnext[i], n, Tail)[Tail]);

invariant (forall i: int, n: Node, m: Node :: { ReachBetweenSet(Hnext[i], n, Tail)[m] } ReachBetweenSet(Hnext[i], n, Tail)[m] ==> ReachBetweenSet(Hnext[i], n, m)[m]);

invariant (forall i: int, n: Node, m: Node :: { ReachBetweenSet(Hnext[i], Head, m)[n] } ReachBetweenSet(Hnext[i], Head, m)[n] ==> ReachBetweenSet(Hnext[i], n, m)[m]);

invariant (forall i: int, n: Node :: { ReachBetweenSet(Hnext[i], n, Tail) } 0 <= i && i < Hcount && ReachBetweenSet(Hnext[i], n, Tail)[Tail] ==> ReachBetweenSet(Hnext[i + 1], n, Tail)[Tail]);

invariant (forall i: int, n: Node :: { Halloc[i][n] } 0 <= i && i < Hcount && IsAlloc(Halloc[i][n]) ==> IsAlloc(Halloc[i + 1][n]));

invariant (forall i: int, j: int, n: Node :: { Halloc[i][n], Halloc[j][n] } 0 <= i && i <= j && j <= Hcount && IsAlloc(Halloc[i][n]) ==> IsAlloc(Halloc[j][n]));

invariant (forall i: int, j: int, n: Node :: { ReachBetweenSet(Hnext[i], n, Tail)[Tail], ReachBetweenSet(Hnext[j], n, Tail)[Tail] } 0 <= i && i <= j && j <= Hcount && ReachBetweenSet(Hnext[i], n, Tail)[Tail] ==> ReachBetweenSet(Hnext[j], n, Tail)[Tail]);

invariant (exists n: Node :: { n.key } n.key == E && Hmarked[0][n] == False && ReachBetweenSet(Hnext[0], Head, Tail)[n]);

invariant (forall i: int :: 0 <= i && i <= Hcount ==> (exists n: Node :: { n.key } n.key == E && Hmarked[i][n] == False && ReachBetweenSet(Hnext[i], Head, Tail)[n]));

invariant (forall n: Node :: { n.key } n.key == E ==> ReachBetweenSet(Hnext[0], Head, Tail)[n]);

invariant (forall i: int, n: Node :: { ReachBetweenSet(Hnext[i], Head, Tail)[n] } 0 <= i && i < Hcount && n.key == E && ReachBetweenSet(Hnext[i], Head, Tail)[n] ==> ReachBetweenSet(Hnext[i + 1], Head, Tail)[n]);

invariant (forall i: int, j: int, n: Node :: { Hmarked[i][n], Hmarked[j][n] } 0 <= i && i <= j && j <= Hcount && n.key == E && Hmarked[i][n] == False ==> Hmarked[j][n] == False);

invariant (forall i: int, j: int, n: Node :: { ReachBetweenSet(Hnext[i], Head, Tail)[n], ReachBetweenSet(Hnext[j], Head, Tail)[n] } 0 <= i && i <= j && j <= Hcount && n.key == E && ReachBetweenSet(Hnext[i], Head, Tail)[n] ==> ReachBetweenSet(Hnext[j], Head, Tail)[n]);

invariant (forall i: int, n: Node :: { n.key, Hnext[i] } { ReachBetweenSet(Hnext[i], Head, Tail)[n] } 0 <= i && i <= Hcount && n.key == E ==> ReachBetweenSet(Hnext[i], Head, Tail)[n]);

invariant (forall i: int, n: Node, m: Node :: { ReachBetweenSet(Hnext[i], n, Tail)[m] } m.key == E && 0 <= i && i < Hcount && ReachBetweenSet(Hnext[i], n, Tail)[m] && ReachBetweenSet(Hnext[i + 1], Head, Tail)[m] ==> ReachBetweenSet(Hnext[i + 1], n, Tail)[m]);

invariant (forall i: int, j: int, n: Node, m: Node :: { ReachBetweenSet(Hnext[i], n, Tail)[m], ReachBetweenSet(Hnext[j], Head, Tail)[m] } m.key == E && 0 <= i && i <= j && j <= Hcount && ReachBetweenSet(Hnext[i], n, Tail)[m] && ReachBetweenSet(Hnext[j], Head, Tail)[m] ==> ReachBetweenSet(Hnext[j], n, Tail)[m]);

invariant (forall n: Node, m: Node :: ReachBetweenSet(Node_next, Head, Tail)[m] && m.key == n.key && n != m ==> !ReachBetweenSet(Node_next, Head, Tail)[n]);

invariant (forall n: Node, m: Node :: { ReachBetweenSet(Node_next, m, Tail)[n] } ReachBetweenSet(Node_next, Head, Tail)[m] && ReachBetweenSet(Node_next, m, Tail)[n] && m != n ==> m.key < n.key);

invariant (forall n: Node, m: Node :: { ReachBetweenSet(Node_next, m, n)[n] } ReachBetweenSet(Node_next, Head, Tail)[m] && ReachBetweenSet(Node_next, m, n)[n] && m != n && n != null ==> m.key < n.key);

invariant (forall n: Node, m: Node :: { ReachBetweenSet(Node_next, Head, m)[n] } ReachBetweenSet(Node_next, Head, n)[n] && n.next == m ==> ReachBetweenSet(Node_next, Head, m)[n]);

invariant (forall n: Node, m: Node :: { ReachBetweenSet(Node_next, Head, m)[n] } ReachBetweenSet(Node_next, Head, n)[n] && Node_next[n] == m ==> ReachBetweenSet(Node_next, Head, m)[n]);


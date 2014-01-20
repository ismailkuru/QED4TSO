/*
After the command: merge proc pop
*/
var H: [int]Node;

record Node {
tl: Node;
alloc: AllocType;
}

var top: Node;

const unique null: Node;

invariant IsNull(null.alloc);

procedure {:ispublic} pop() returns (t: Node);
  modifies H, AH, top;



implementation pop() returns (t: Node)
{
  var n: Node;
  var guard: bool;
  var ex: Exception;
  var guard_0: bool;

  Atomic_46:
    atomic  {  // Non-mover
        assert H[tid] == null;
        if (*)
        {
            havoc t, n, guard_0, guard;
            H[tid] := t;
        }
    }

    if (true)
    {
      Try_36:
        try {
          Atomic_2_dup:
            atomic  {  // Non-mover
                havoc t;
                if (t == null)
                {
                    throw ExBreak;
                }

                assume owner[t] == 0;
                assert AH[tid] == null && t != null;
                H[tid] := t;
                AH[tid] := t;
                havoc guard_0;

                if (guard_0)
                {
                    assert owner[t] == 0;
                    n := t.tl;

                    assert true;
                    guard := top == t;
                    if (guard)
                    {
                        assert top.tl == n;
                        top := n;
                    }

                    if (guard)
                    {
                        throw ExBreak;
                    }
                }
            }

          Atomic_31_dup:
            atomic  {  // Non-mover
                AH[tid] := null;

                assume false;
            }
}
        catch (ExBreak){
          Atomic_35:
            atomic  {  // Non-mover
                assume true;
            }
        }
    }

  Atomic_9:
    atomic  {  // Non-mover
        assert AH[tid] != null && H[tid] != null;
        H[tid] := null;
        AH[tid] := null;
    }
}



procedure {:ispublic} push(b: Node) returns (r: bool);
  modifies Node_tl, owner, top;



implementation push(b: Node) returns (r: bool)
{
  var t: Node;
  var n: int;
  var h: Node;
  var guard: bool;
  var ex: Exception;
  var guard_1: bool;

  Atomic_11:
    atomic  {  // Non-mover
        assert b != null;
        havoc h, n;
        assume 1 <= n && n <= Tid;
        guard_1 := n <= Tid;
        if (*)
        {
            assume (forall m: TID :: 1 <= m && m < n ==> AH[m] != b);
        }
        else
        {
            r := false;
            return;
        }

        if (guard_1)
        {
            havoc h;
            r := false;
            return;
        }

        assert !ReachBetween(Node_tl, top, b, b);
        owner[b] := tid;

        if (*)
        {
            havoc t;
            assert owner[b] == tid;
            assert !ReachBetween(Node_tl, top, b, b);
            assert b != null;
            b.tl := t;
            havoc guard;
        }

        if (true)
        {
          Try_62:
            try {
                havoc t;
                assert owner[b] == tid;
                assert !ReachBetween(Node_tl, top, b, b);
                assert b != null;
                b.tl := t;

                assert owner[b] == tid;
                assert true;
                guard := top == t;
                if (guard)
                {
                    assert b.tl == top;
                    top := b;
                    owner[b] := 0;
                }

                if (guard)
                {
                    throw ExBreak;
                }

              Atomic_60:
                atomic  {  // Non-mover
                    assume false;
                }
}
            catch (ExBreak){
              Atomic_61:
                atomic  {  // Non-mover
                    assume true;
                }
            }
        }

        r := true;
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

procedure {:isatomic} lock(m: Mutex);
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



procedure {:isatomic} unlock(m: Mutex);
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

  Atomic_22:
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

  Atomic_23:
    atomic  {  // Non-mover
        this.interrupted := True;
    }
}



procedure {:isatomic} Thread_currentThread() returns (result: Thread);



implementation Thread_currentThread() returns (result: Thread)
{
  var ex: Exception;

  Atomic_24:
    atomic  {  // Non-mover
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

var AH: [int]Node;

invariant (forall t: int :: AH[t] == null || AH[t] == H[t]);

var owner: [Node]int;

invariant null.tl == null;

invariant ReachBetween(Node_tl, top, null, null);

invariant (forall t: Node :: ReachBetween(Node_tl, top, t, null) ==> owner[t] == 0);


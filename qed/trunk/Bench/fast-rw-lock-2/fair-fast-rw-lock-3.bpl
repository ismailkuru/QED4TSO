type State;

const unique READER: State;

const unique WRITER: State;

const unique ACTIVE_READER: State;

axiom (forall s: State :: s == READER || s == WRITER || s == ACTIVE_READER);

const unique null: Lelem;

invariant IsNull(null.alloc) && (forall l: Lelem :: IsNull(l.alloc) <==> l == null);

var L: Lelem;

record Lelem {
  state: State;
  spin: int;
  next: Lelem;
  prev: Lelem;
  EL: boolean;
  alloc: AllocType;
}

procedure writerLock() returns (I: Lelem);
  modifies Lelem_alloc, Lelem_state, Lelem_spin, Lelem_next, L, owner, wlock, L;



implementation writerLock() returns (I: Lelem)
{
  var pred: Lelem;

    if (*)
    {
      Atomic_5:
        atomic { // Non-mover
            I := New Lelem;
            I.state := WRITER;
            I.spin := 1;
            I.next := null;
            pred := L;
            L := I;
            assume pred != null;
            owner[I] := tid;
            pred.next := I;
        }

      Atomic_100:
        atomic { // Non-mover
            assume IsAlloc(I.alloc) && owner[I] == tid;

            // assert owner[I] == tid; [Discharged]
            // assert I.alloc == Alloc; [Discharged]
            assume I.spin != 1;
        }
    }
    else
    {
      Atomic_5_else:
        atomic { // Non-mover
            I := New Lelem;
            I.state := WRITER;
            I.spin := 1;
            I.next := null;
            pred := L;
            L := I;
            assume pred == null;
            assert (forall K: Lelem :: rlock[K] == False);
            owner[I] := tid;
            wlock := I;
        }
    }
}



procedure writerUnlock(I: Lelem);
  requires I.state == WRITER && wlock == I && owner[I] == tid && IsAlloc(I.alloc);
  modifies Lelem_prev, Lelem_spin, wlock, rlock, L;



implementation writerUnlock(I: Lelem)
{
  var pred: Lelem;
  var tmp: Lelem;
  var guard_0: bool;
  var abst_Lelem_next_0: [Lelem]Lelem;

  Atomic_101:
    atomic { // Non-mover
        assume I.state == WRITER && wlock == I && owner[I] == tid && IsAlloc(I.alloc);
    }

  Atomic_12:
    atomic { // Non-mover
        assert I.state == WRITER;
        assert wlock == I;
        assert owner[I] == tid;
        havoc abst_Lelem_next_0;
        guard_0 := abst_Lelem_next_0[I] == null;
        assert IsAlloc(I.alloc);
        if (guard_0)
        {
            tmp := L;
            if (L == I)
            {
                L := null;
                wlock := null;
                return;
            }
        }
    }

  Atomic_15:
    atomic { // Non-mover
        assert I.state == WRITER;
        assert wlock == I;
        assert owner[I] == tid;
        assume I.next != null;
        assert I.next.state != WRITER ==> I.next.prev == I;
        assert I.next.state != ACTIVE_READER;
        I.next.prev := null;
        I.next.spin := 0;
        if (I.next.state == WRITER)
        {
            wlock := I.next;
        }
        else
        {
            rlock[I.next] := True;
            wlock := null;
        }
    }
}



procedure readerLock() returns (I: Lelem);
  modifies Lelem_spin, rlock, Lelem_alloc, Lelem_state, Lelem_next, Lelem_prev, owner;



implementation readerLock() returns (I: Lelem)
{
  var pred: Lelem;
  var n: Lelem;
  var nextState: State;
  var predState: State;

    if (*)
    {
      Atomic_18:
        atomic { // Non-mover
            I := New Lelem;
            I.state := READER;
            I.spin := 1;
            I.next := null;
            I.prev := null;
            pred := L;
            L := I;
            owner[I] := tid;
            assume pred != null;
            I.prev := pred;
            pred.next := I;
        }

      Atomic_26:
        atomic { // Non-mover
            assert owner[I] == tid;
            assert pred.alloc == Alloc;
            predState := pred.state;
            if (*)
            {
                if (*)
                {
                    predState := READER;
                }
                else
                {
                    predState := WRITER;
                }
            }

            if (predState != ACTIVE_READER)
            {
                assert I.alloc == Alloc;
                assume I.spin == 0;
            }
        }
    }
    else
    {
      Atomic_18_else:
        atomic { // Non-mover
            I := New Lelem;
            I.state := READER;
            I.spin := 1;
            I.next := null;
            I.prev := null;
            pred := L;
            L := I;
            owner[I] := tid;
            assume pred == null;
            rlock[I] := True;
        }
    }

  Atomic_80:
    atomic { // Non-mover
        if (*)
        {
            assert L != null;
            assert rlock[I] == True;
            assert wlock == null;
            assert owner[I] == tid;
            n := I.next;
            assume n != null;
            assert I.next.state == READER || I.next.state == WRITER;
            assert rlock[I.next] == False;
            assert I.next.state == READER ==> I.next.prev == I;
            nextState := I.next.state;
            if (nextState == READER)
            {
                I.next.spin := 0;
                rlock[I.next] := True;
            }
        }
        else
        {
            assert owner[I] == tid;
            havoc n;
        }

        assert I.state == READER;
        assert rlock[I] == True;
        assert wlock == null;
        I.state := ACTIVE_READER;
    }
}



procedure readerUnlock(I: Lelem);
  modifies Lelem_prev, Lelem_EL, held, rlock, Lelem_spin, wlock, L, Lelem_next;



implementation readerUnlock(I: Lelem)
{
  var p: Lelem;
  var tmp: Lelem;
  var n: Lelem;
  var guard: Lelem;
  var pp: Lelem;
  var abst_Lelem_next_1: [Lelem]Lelem;
  var abst_Lelem_prev_2: [Lelem]Lelem;

  Atomic_32:
    atomic { // Non-mover
        assert I.state == ACTIVE_READER;
        assert owner[I] == tid;
        havoc abst_Lelem_next_1;
        assert I.alloc == Alloc;
        n := abst_Lelem_next_1[I];
        havoc abst_Lelem_prev_2;
        p := abst_Lelem_prev_2[I];
    }

    if (*)
    {
        if (*)
        {
          Atomic_34:
            atomic { // Non-mover
                assert I.state == ACTIVE_READER;
                assert owner[I] == tid;
                assume p != null;
                assert p.alloc == Alloc;
                assume p.EL == False;
                p.EL := True;
                assume p == I.prev;
                held[p] := tid;
                assume p != null;
                assert p.next == I;
                assert p.state != WRITER;
                assume I.EL == False;
                I.EL := True;
                p.next := null;
                held[I] := tid;
                if (*)
                {
                    assert rlock[I] == True;
                    havoc n;
                    pp := I.prev;
                    tmp := L;
                    if (L == I)
                    {
                        L := pp;
                    }

                    if (*)
                    {
                        assume I.next != null;
                    }
                }
                else
                {
                    assert rlock[I] == True;
                    havoc n;
                }
            }

          Atomic_99:
            atomic { // Non-mover
                if (*)
                {
                    assert IsAlloc(I.prev.alloc);
                    assert held[I.prev] == tid;
                    assert L != null;
                    assert I.state == ACTIVE_READER;
                    assert rlock[I] == True;
                    assert owner[I] == tid;
                    assert held[I] == tid;
                    n := I.next;
                    assume n != null;
                    assert (forall K: Lelem :: K != I ==> K.next != I.next);
                    assert I.next.state != WRITER ==> I.next.prev == I;
                    assert I.next.state == WRITER ==> I.next.prev == I || I.next.prev == null;
                    assert wlock == null;
                    I.next.prev := I.prev;
                    assume owner[I] == tid && held[I] == tid && I.alloc == Alloc && rlock[I] == True && I.state == ACTIVE_READER && I.next != null;
                    assert I.prev.next == I;
                    assert I.prev == p;
                    assert I.prev.state != WRITER;
                    I.prev.next := I.next;
                }
                else
                {
                    assert I.state == ACTIVE_READER;
                    assert rlock[I] == True;
                    assert owner[I] == tid;
                    assert held[I] == tid;
                    havoc n;
                }
            }

          Call_46:
            atomic { // Non-mover
                assert L != null && wlock == null;
                assert I.state == ACTIVE_READER;
                assert owner[I] == tid;
                assert held[I] == tid || held[I] == 0;
                assert held[p] == tid || held[p] == 0;
                assert I.EL == True;
                I.EL := False;
                assert p.alloc == Alloc;
                assert p.EL == True;
                p.EL := False;
                held[p] := 0;
                held[I] := 0;
                rlock[I] := False;
                return;
            }
        }
        else
        {
          Atomic_34_else:
            atomic { // Non-mover
                assert I.state == ACTIVE_READER;
                assert owner[I] == tid;
                assume p != null;
                assert p.alloc == Alloc;
                assume p.EL == False;
                p.EL := True;
                assert I.alloc == Alloc;
                assume p == I.prev;
                held[p] := tid;
                assume p == null;
            }
        }
    }
    else
    {
      Atomic_49:
        atomic { // Non-mover
            assert I.state == ACTIVE_READER;
            assert owner[I] == tid;
            assume p == null;
        }
    }

  Atomic_95:
    atomic { // Non-mover
        if (*)
        {
            assert I.prev == null;
            assert I.state == ACTIVE_READER;
            assert owner[I] == tid;
            assume I.EL == False;
            I.EL := True;
            held[I] := tid;
            rlock[I] := False;
            havoc n;
            assert L != null;
            assert wlock == null;
            tmp := L;
            if (L == I)
            {
                assert (forall K: Lelem :: rlock[K] == False);
                L := null;
            }

            if (*)
            {
                assume I.next != null;
            }
        }
        else
        {
            assert I.state == ACTIVE_READER;
            assert owner[I] == tid;
            assume I.EL == False;
            I.EL := True;
            n := I.next;
            held[I] := tid;
            rlock[I] := False;
            assume n != null;
        }
    }

    if (*)
    {
      Atomic_54:
        atomic { // Non-mover
            assert I.state == ACTIVE_READER;
            assert owner[I] == tid;
            assert held[I] == tid;
            n := I.next;
            assume n != null;
            assert I.next.state != WRITER ==> I.next.prev == I;
            assert wlock == null;
            assert L != null;
            I.next.spin := 0;
            if (I.next.state == WRITER)
            {
                assert (forall L: Lelem :: rlock[L] == False);
                wlock := I.next;
            }
            else
            {
                rlock[I.next] := True;
            }
        }

      Atomic_89:
        atomic { // Non-mover
            assert I.prev == null;
            assert (forall K: Lelem :: K != I ==> I.next != K.next);
            assert owner[I] == tid && held[I] == tid && I.alloc == Alloc && I.state == ACTIVE_READER && I.next.alloc == Alloc;
            assert I.next.state != WRITER ==> I.next.prev == I;
            I.next.prev := null;
        }
    }
    else
    {
      Atomic_54_else:
        atomic { // Non-mover
            assert I.state == ACTIVE_READER;
            assert rlock[I] == True;
            assert owner[I] == tid;
            assert held[I] == tid;
            assert I.alloc == Alloc;
            havoc n;
        }
    }

  Call_57:
    atomic { // Non-mover
        assert I.state == ACTIVE_READER;
        assert owner[I] == tid;
        assert held[I] == tid || held[I] == 0;
        assert I.EL == True;
        assert I.alloc == Alloc;
        I.EL := False;
        held[I] := 0;
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

const unique tid: int;

const unique tidx: int;

axiom 0 < tid && 0 < tidx && tid != tidx;

var Tid: int;

invariant 0 < Tid && tid <= Tid && tidx <= Tid;

record Thread {
  id: int;
  interrupted: boolean;
  alloc: AllocType;
}

var Threads: [int]Thread;

const unique NULL_THREAD: Thread;

invariant (forall i: int :: i <= 0 ==> Threads[i] == NULL_THREAD);

invariant (forall i: int :: i >= 0 ==> (Threads[i]).id == i);

procedure {:ispublic false} Thread_interrupted() returns (result: bool);
  modifies Thread_interrupted;



implementation Thread_interrupted() returns (result: bool)
{
  var currentThread: Thread;

  Call_61:
    atomic { // Non-mover
        currentThread := Threads[tid];
        assert currentThread.alloc == Alloc;
        result := currentThread.interrupted == True;
        if (result)
        {
            if (true)
            {
                currentThread.interrupted := False;
            }
        }
    }
}



type Exception;

const unique ExReturn: Exception;

const unique ExSkip: Exception;

const unique ExBreak: Exception;

const unique ExContinue: Exception;

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

var held: [Lelem]int;

invariant (forall I: Lelem :: { Lelem_EL[I] } { held[I] } I.EL != True <==> held[I] == 0);

var owner: [Lelem]int;

invariant (forall L: Lelem :: !IsAlloc(L.alloc) ==> owner[L] == 0);

invariant (forall L: Lelem :: !IsAlloc(L.alloc) ==> L.next == null);

invariant IsAlloc(L.alloc) || IsNull(L.alloc);

invariant L.next == null;

var wlock: Lelem;

var rlock: [Lelem]boolean;

invariant (forall L: Lelem :: !IsAlloc(L.alloc) ==> rlock[L] == False);

invariant L == null ==> wlock == null;

invariant (forall L: Lelem :: IsDealloc(L.alloc) ==> (forall K: Lelem :: K.next != L));


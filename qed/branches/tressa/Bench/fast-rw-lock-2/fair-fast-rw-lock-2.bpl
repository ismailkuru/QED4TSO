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
  modifies Lelem_alloc, Lelem_state, Lelem_spin, Lelem_next;



implementation writerLock() returns (I: Lelem)
{
  var pred: Lelem;

  Atomic_5:
    atomic { // Non-mover
        I := New Lelem;

        assert I.alloc == Alloc;
        I.state := WRITER;

        assert I.alloc == Alloc;
        I.spin := 1;

        assert I.alloc == Alloc;
        I.next := null;

        assert true;
        // call pred := fetch_and_store(I);
        pred := L;
        L := I;
    }

    if (pred != null)
    {
      Atomic_10:
        atomic { // Non-mover
            assert pred.alloc == Alloc;
            pred.next := I;
        }

      Atomic_11:
        atomic { // Right-mover
            assert I.alloc == Alloc;
            assume I.spin != 1;
        }
    }
}



procedure writerUnlock(I: Lelem);
  modifies Lelem_prev, Lelem_spin;



implementation writerUnlock(I: Lelem)
{
  var pred: Lelem;
  var tmp: Lelem;
  var guard_0: bool;

  Atomic_12:
    atomic { // Non-mover
        assert I.alloc == Alloc;
        guard_0 := I.next == null;
    }

  Atomic_68:
    atomic { // Non-mover
        if (guard_0)
        {
            assert true;
            // call tmp := CAS(null, I);
            tmp := L;
            if (L == I)
            {
                L := null;
            }

            if (tmp == I)
            {
                return;
            }
        }
    }

  Atomic_15:
    atomic { // Non-mover
        assert I.alloc == Alloc;
        assume I.next != null;
    }

  Atomic_16:
    atomic { // Non-mover
        assert I.next.alloc == Alloc;
        assert I.alloc == Alloc;
        I.next.prev := null;
    }

  Atomic_17:
    atomic { // Non-mover
        assert I.next.alloc == Alloc;
        assert I.alloc == Alloc;
        I.next.spin := 0;
    }
}



procedure readerLock() returns (I: Lelem);
  modifies Lelem_alloc, Lelem_state, Lelem_spin, Lelem_next, Lelem_prev;



implementation readerLock() returns (I: Lelem)
{
  var pred: Lelem;
  var n: Lelem;
  var nextState: State;
  var predState: State;

  Atomic_18:
    atomic { // Non-mover
        I := New Lelem;

        assert I.alloc == Alloc;
        I.state := READER;

        assert I.alloc == Alloc;
        I.spin := 1;

        assert I.alloc == Alloc;
        I.next := null;

        assert I.alloc == Alloc;
        I.prev := null;

        assert true;
        // call pred := fetch_and_store(I);
        pred := L;
        L := I;
    }

    if (pred != null)
    {
      Atomic_24:
        atomic { // Non-mover
            assert I.alloc == Alloc;
            I.prev := pred;
        }

      Atomic_25:
        atomic { // Non-mover
            assert pred.alloc == Alloc;
            pred.next := I;
        }

      Atomic_26:
        atomic { // Non-mover
            assert pred.alloc == Alloc;
            predState := pred.state;
        }

      Atomic_64:
        atomic { // Right-mover
            if (predState != ACTIVE_READER)
            {
                assert I.alloc == Alloc;
                assume I.spin == 0;
            }
        }
    }

  Atomic_28:
    atomic { // Non-mover
        assert I.alloc == Alloc;
        n := I.next;
    }

    if (n != null)
    {
      Atomic_29:
        atomic { // Non-mover
            assert I.next.alloc == Alloc;
            assert I.alloc == Alloc;
            nextState := I.next.state;
        }

      Atomic_65:
        atomic { // Non-mover
            if (nextState == READER)
            {
                assert I.next.alloc == Alloc;
                assert I.alloc == Alloc;
                I.next.spin := 0;
            }
        }
    }

  Atomic_31:
    atomic { // Non-mover
        assert I.alloc == Alloc;
        I.state := ACTIVE_READER;
    }
}



procedure readerUnlock(I: Lelem);
  modifies Lelem_next, Lelem_prev, Lelem_spin, Lelem_EL;



implementation readerUnlock(I: Lelem)
{
  var p: Lelem;
  var tmp: Lelem;
  var n: Lelem;
  var guard: Lelem;
  var pp: Lelem;

  Atomic_32:
    atomic { // Non-mover
        assert I.alloc == Alloc;
        n := I.next;
    }

  Atomic_33:
    atomic { // Non-mover
        assert I.alloc == Alloc;
        p := I.prev;
    }

    if (*)
    {
      Atomic_34:
        atomic { // Non-mover
            assume p != null;

            assert true;
            // call Acq(p);
            assert p.alloc == Alloc;
            assume p.EL == False;
            assert p.alloc == Alloc;
            p.EL := True;

            assert I.alloc == Alloc;
            assume p == I.prev;
        }

        if (p != null)
        {
          Call_37:
            atomic { // Non-mover
                assert true;
                // call Acq(I);
                assert I.alloc == Alloc;
                assume I.EL == False;
                assert I.alloc == Alloc;
                I.EL := True;

                assert p.alloc == Alloc;
                p.next := null;
            }

          Atomic_39:
            atomic { // Non-mover
                assert I.alloc == Alloc;
                n := I.next;
            }

            if (n == null)
            {
              Atomic_40:
                atomic { // Non-mover
                    assert I.alloc == Alloc;
                    pp := I.prev;
                }

              Call_41:
                atomic { // Non-mover
                    assert true;
                    // call tmp := CAS(pp, I);
                    tmp := L;
                    if (L == I)
                    {
                        L := pp;
                    }
                }

              Atomic_66:
                atomic { // Non-mover
                    if (tmp != I)
                    {
                        assert I.alloc == Alloc;
                        assume I.next != null;
                    }
                }
            }

          Atomic_43:
            atomic { // Non-mover
                assert I.alloc == Alloc;
                n := I.next;
            }

            if (n != null)
            {
              Atomic_44:
                atomic { // Non-mover
                    assert I.next.alloc == Alloc;
                    assert I.alloc == Alloc;
                    assert I.alloc == Alloc;
                    I.next.prev := I.prev;
                }

              Atomic_45:
                atomic { // Non-mover
                    assert I.prev.alloc == Alloc;
                    assert I.alloc == Alloc;
                    assert I.alloc == Alloc;
                    I.prev.next := I.next;
                }
            }

          Call_46:
            atomic { // Left-mover
                assert true;
                // call Rel(I);
                assert I.alloc == Alloc;
                assert I.EL == True;
                assert I.alloc == Alloc;
                I.EL := False;

                assert true;
                // call Rel(p);
                assert p.alloc == Alloc;
                assert p.EL == True;
                assert p.alloc == Alloc;
                p.EL := False;

                return;
            }
        }
    }
    else
    {
      Atomic_49:
        atomic { // Right-mover
            assume p == null;
        }
    }

  Call_50:
    atomic { // Non-mover
        assert true;
        // call Acq(I);
        assert I.alloc == Alloc;
        assume I.EL == False;
        assert I.alloc == Alloc;
        I.EL := True;

        assert I.alloc == Alloc;
        n := I.next;
    }

    if (n == null)
    {
      Call_52:
        atomic { // Non-mover
            assert true;
            // call tmp := CAS(null, I);
            tmp := L;
            if (L == I)
            {
                L := null;
            }
        }

      Atomic_67:
        atomic { // Non-mover
            if (tmp != I)
            {
                assert I.alloc == Alloc;
                assume I.next != null;
            }
        }
    }

  Atomic_54:
    atomic { // Non-mover
        assert I.alloc == Alloc;
        n := I.next;
    }

    if (n != null)
    {
      Atomic_55:
        atomic { // Non-mover
            assert I.next.alloc == Alloc;
            assert I.alloc == Alloc;
            I.next.spin := 0;
        }

      Atomic_56:
        atomic { // Non-mover
            assert I.next.alloc == Alloc;
            assert I.alloc == Alloc;
            I.next.prev := null;
        }
    }

  Call_57:
    atomic { // Left-mover
        assert true;
        // call Rel(I);
        assert I.alloc == Alloc;
        assert I.EL == True;
        assert I.alloc == Alloc;
        I.EL := False;
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
    atomic { // Both-mover
        assert true;
        // call currentThread := Thread_currentThread();
        currentThread := Threads[tid];

        assert true;
        // call result := Thread_nativeIsInterrupted(currentThread, true);
        assert currentThread.alloc == Alloc;
        result := currentThread.interrupted == True;
        if (result)
        {
            if (true)
            {
                assert currentThread.alloc == Alloc;
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


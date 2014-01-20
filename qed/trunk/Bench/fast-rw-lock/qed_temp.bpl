type State;

const unique READER: State;

const unique WRITER: State;

const unique ACTIVE_READER: State;

axiom (forall s: State :: s == READER || s == WRITER || s == ACTIVE_READER);

const unique null: Lelem;

record Lelem {
  state: State;
  spin: int;
  next: Lelem;
  prev: Lelem;
  EL: boolean;
  alloc: boolean;
}

record RWLock {
  elem: Lelem;
  alloc: boolean;
}

procedure readerLock(L: RWLock) returns (I: Lelem);
  modifies Lelem_alloc, Lelem_state, Lelem_spin, Lelem_next, Lelem_prev, RWLock_elem, creator, creator;



implementation readerLock(L: RWLock) returns (I: Lelem)
{
  var pred: Lelem;
  var n: Lelem;
  var nextState: State;
  var predState: State;

  Atomic_5:
    atomic { // None-mover
        I := New Lelem;
        I.state := READER;
        I.spin := 1;
        I.next := null;
        I.prev := null;
        pred := L.elem;
        L.elem := I;
        creator[I] := tid;
    }

    if (pred != null)
    {
      Atomic_11:
        atomic { // None-mover
            assert creator[I] == tid;
            assert I != null && I.alloc == True;
            I.prev := pred;
        }

      Atomic_12:
        atomic { // None-mover
            assert creator[I] == tid;
            assert pred != null && pred.alloc == True;
            pred.next := I;
        }

      Atomic_13:
        atomic { // None-mover
            assert creator[I] == tid;
            assert pred != null && pred.alloc == True;
            predState := pred.state;
        }

      Atomic_38:
        atomic { // None-mover
            assert creator[I] == tid;
            if (predState != ACTIVE_READER)
            {
                assume I.spin == 0;
            }
        }
    }

  Atomic_15:
    atomic { // None-mover
        assert creator[I] == tid;
        assert I != null && I.alloc == True;
        n := I.next;
    }

  Atomic_43:
    atomic { // None-mover
        if (n != null)
        {
            assert creator[I] == tid;
            assert n != null && n.alloc == True;
            nextState := n.state;
            assert creator[I] == tid;
            assert n != null && n.alloc == True;
            if (nextState == READER)
            {
                n.spin := 0;
            }
        }
    }

  Atomic_18:
    atomic { // None-mover
        assert creator[I] == tid;
        assert I != null && I.alloc == True;
        I.state := ACTIVE_READER;
    }
}



procedure readerUnlock(L: RWLock, I: Lelem);
  modifies Lelem_next, Lelem_prev, Lelem_spin, Lelem_EL, RWLock_elem, owner;



implementation readerUnlock(L: RWLock, I: Lelem)
{
  var p: Lelem;
  var tmp: Lelem;
  var n: Lelem;
  var guard: Lelem;
  var fresh_0: Lelem;
  var fresh_1: Lelem;
  var abst_Lelem_prev_0: [Lelem]Lelem;

  Atomic_19:
    atomic { // None-mover
        assert creator[I] == tid;
        assert I != null && I.alloc == True;
        n := I.next;
        havoc abst_Lelem_prev_0;
        p := abst_Lelem_prev_0[I];
    }

    if (p != null)
    {
      Call_21:
        atomic { // None-mover
            assert creator[I] == tid;
            assert p != null && p.alloc == True;
            assert I != null && I.alloc == True;
            assume p.EL == False;
            p.EL := True;
            owner[p] := tid;
            assert owner[p] == tid;
            assume p == I.prev;
        }

        if (p != null)
        {
          Call_23:
            atomic { // None-mover
                assert creator[I] == tid;
                assert I != null && I.alloc == True;
                assert p != null && p.alloc == True;
                assert owner[p] == tid;
                assume I.EL == False;
                I.EL := True;
                owner[I] := tid;
                assert owner[I] == tid;
                assert owner[p] == tid;
                p.next := null;
            }

            if (n == null)
            {
              Call_25:
                atomic { // None-mover
                    assert creator[I] == tid;
                    assert I != null && I.alloc == True;
                    assert owner[p] == tid;
                    assert owner[I] == tid;
                    tmp := L.elem;
                    fresh_0 := L.elem;
                    if (fresh_0 == I)
                    {
                        L.elem := I.prev;
                    }
                }

              Atomic_40:
                atomic { // None-mover
                    assert creator[I] == tid;
                    if (tmp != I)
                    {
                        assert owner[I] == tid;
                        assert owner[p] == tid;
                        assume n != null;
                    }
                }
            }

            if (n != null)
            {
              Atomic_27:
                atomic { // None-mover
                    assert creator[I] == tid;
                    assert n != null && n.alloc == True;
                    assert I != null && I.alloc == True;
                    assert owner[p] == tid;
                    assert owner[I] == tid;
                    n.prev := I.prev;
                }

              Atomic_28:
                atomic { // None-mover
                    assert creator[I] == tid;
                    assert I != null && I.alloc == True;
                    assert p != null && p.alloc == True;
                    assert owner[p] == tid;
                    assert owner[I] == tid;
                    p.next := I.next;
                }
            }

          Call_29:
            atomic { // None-mover
                assert creator[I] == tid;
                assert owner[p] == tid;
                assert owner[I] == tid || owner[I] == 0;
                assert I.EL == True;
                I.EL := False;
                owner[I] := 0;
                assert owner[p] == tid || owner[p] == 0;
                assert p.EL == True;
                p.EL := False;
                owner[p] := 0;
                return;
            }
        }
    }

  Call_32:
    atomic { // None-mover
        assert creator[I] == tid;
        assert I != null && I.alloc == True;
        assume I.EL == False;
        I.EL := True;
        owner[I] := tid;
    }

    if (n == null)
    {
      Call_33:
        atomic { // None-mover
            assert I != null && I.alloc == True;
            assert creator[I] == tid;
            assert owner[I] == tid;
            tmp := L.elem;
            fresh_1 := L.elem;
            if (fresh_1 == I)
            {
                L.elem := null;
            }
        }

      Atomic_41:
        atomic { // None-mover
            assert creator[I] == tid;
            if (tmp != I)
            {
                assert owner[I] == tid;
                assume n != null;
            }
        }
    }

    if (n != null)
    {
      Atomic_35:
        atomic { // None-mover
            assert creator[I] == tid;
            assert I != null && I.alloc == True;
            assert I.next != null && I.next.alloc == True;
            assert owner[I] == tid;
            I.next.spin := 0;
        }

      Atomic_36:
        atomic { // None-mover
            assert creator[I] == tid;
            assert I != null && I.alloc == True;
            assert owner[I] == tid;
            I.prev.prev := null;
        }
    }

  Call_37:
    atomic { // None-mover
        assert creator[I] == tid;
        assert owner[I] == tid || owner[I] == 0;
        assert I.EL == True;
        I.EL := False;
        owner[I] := 0;
    }
}



const unique tid: int;

const unique tidx: int;

axiom 0 < tid && 0 < tidx && tid != tidx;

var Tid: int;

invariant 0 < Tid && tid <= Tid && tidx <= Tid;

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

var owner: [Lelem]int;

invariant (forall lelem: Lelem :: { Lelem_EL[lelem] } { owner[lelem] } lelem.EL != True <==> owner[lelem] == 0);

invariant null.next == null && null.prev == null && null.alloc == False && null.EL == False && null.spin == 0;

var creator: [Lelem]int;

invariant (forall elem: Lelem :: elem.alloc == False ==> creator[elem] == 0);


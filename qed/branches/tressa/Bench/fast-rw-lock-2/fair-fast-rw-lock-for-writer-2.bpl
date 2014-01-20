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
  modifies Lelem_alloc, Lelem_state, Lelem_spin, Lelem_next, L, owner, wlock, L, wlock, acq;



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

            // assert true; [Discharged]
            // call pred := fetch_and_store(I);
            pred := L;
            L := I;

            assume pred != null;

            // assert I != null; [Discharged]
            // assert pred.next == null; [Discharged]
            // assert IsAlloc(pred.alloc); [Discharged]
            pred.next := I;

            owner[I] := tid;
        }

      Atomic_11:
        atomic { // Right-mover
            assert IsAlloc(I.alloc);
            assert acq[I] == True;
            assert L != null;
            assert owner[I] == tid;
            assume I.spin != 1;
            assert wlock == I;

            acq[I] := False;
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
            owner[I] := tid;
            wlock := I;

            acq[I] := False;
        }
    }
}



procedure writerUnlock(I: Lelem);
  modifies Lelem_prev, Lelem_spin, wlock, L;



implementation writerUnlock(I: Lelem)
{
  var pred: Lelem;
  var tmp: Lelem;
  var guard_0: bool;
  var abst_Lelem_next_0: [Lelem]Lelem;

  Atomic_12:
    atomic { // Left-mover
        assert wlock == I;
        assert acq[I] == False;
        assert L != null;
        assert owner[I] == tid;
        havoc abst_Lelem_next_0, tmp, guard_0;
        // assert IsAlloc(I.alloc); [Discharged]
        if (*)
        {
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
        assert wlock == I;
        assert acq[I] == False;
        assert L != null;
        assert owner[I] == tid;
        // assert IsAlloc(I.alloc); [Discharged]
        assume I.next != null;
        // assert IsAlloc(I.next.alloc); [Discharged]
        I.next.prev := null;
        I.next.spin := 0;
        wlock := I.next;
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

var owner: [Lelem]int;

invariant (forall L: Lelem :: !IsAlloc(L.alloc) ==> owner[L] == 0);

invariant IsAlloc(L.alloc) || IsNull(L.alloc);

invariant null.next == null && null.prev == null;

invariant L.next == null;

var wlock: Lelem;

invariant L == null <==> wlock == null;

var acq: [Lelem]boolean;

invariant (forall l: Lelem :: l.spin == 0 || l.spin == 1);

invariant (forall l: Lelem :: !IsAlloc(l.alloc) ==> acq[l] == True);

invariant (forall l: Lelem :: !IsAlloc(l.alloc) ==> l.next == null);

invariant (forall k: Lelem, l: Lelem :: IsAlloc(k.alloc) && IsDealloc(l.alloc) ==> !ReachBetween(Lelem_next, k, l, l));

invariant (forall l: Lelem :: IsAlloc(l.alloc) ==> ReachBetween(Lelem_next, l, null, null));

invariant ReachBetween(Lelem_next, wlock, L, null);

invariant (forall k: Lelem, l: Lelem, m: Lelem :: IsAlloc(l.alloc) && k != m && l != m && k != l && ReachBetween(Lelem_next, k, l, null) && ReachBetween(Lelem_next, m, l, null) ==> ReachBetween(Lelem_next, k, m, m) || ReachBetween(Lelem_next, m, k, k));

invariant (forall l: Lelem :: IsAlloc(l.alloc) && ReachBetween(Lelem_next, wlock, l, L) && l != wlock ==> acq[l] == True);

invariant (forall l: Lelem :: IsAlloc(l.alloc) && ReachBetween(Lelem_next, l, wlock, wlock) && l != wlock ==> acq[l] == False) && (forall l: Lelem :: L != null && IsAlloc(l.alloc) && !ReachBetween(Lelem_next, l, L, null) ==> acq[l] == False);

invariant (forall l: Lelem :: IsAlloc(l.alloc) && ReachBetween(Lelem_next, wlock, l, null) && l != null && l != wlock ==> l.spin == 1);


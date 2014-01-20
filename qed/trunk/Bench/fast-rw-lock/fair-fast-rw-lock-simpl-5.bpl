type State;

const unique READER: State;

const unique WRITER: State;

const unique ACTIVE_READER: State;

axiom (forall s: State :: s == READER || s == WRITER || s == ACTIVE_READER);

const unique null: Lelem;

var tail: Lelem;

record Lelem {
  state: State;
  spin: int;
  next: Lelem;
  prev: Lelem;
  EL: boolean;
  alloc: boolean;
  owned: int;
}

var wlock: int;

procedure writerLock() returns (I: Lelem);
  modifies Lelem_alloc, Lelem_state, Lelem_spin, Lelem_next, tail, owner, tail, owner, Lelem_owned;



implementation writerLock() returns (I: Lelem)
{
  var pred: Lelem;

  Atomic_5:
    atomic { // None-mover
        I := New Lelem;
        I.state := WRITER;
        I.next := null;
        pred := tail;
        tail := I;
        owner[I] := tid;
        I.owned := tid;
        if (pred != null)
        {
            pred.next := I;
            I.spin := 1;
        }
        else
        {
            if (*)
            {
                I.spin := 1;
            }
            else
            {
                I.spin := 0;
            }

            wlock := tid;
        }

        assert wlock == tid;
        if (pred != null)
        {
            assume true;
        }
    }
}



procedure writerUnlock(I: Lelem);
  modifies Lelem_prev, Lelem_spin, tail;



implementation writerUnlock(I: Lelem)
{
  var pred: Lelem;
  var tmp: Lelem;
  var guard_1: bool;
  var fresh_0: bool;
  var abst_Lelem_next_0: [Lelem]Lelem;
  var temp: Lelem;

  Atomic_12:
    atomic { // None-mover
        assert tail != null;
        // assert wlock == tid; [Discharged]
        havoc abst_Lelem_next_0;
        // assert owner[I] == tid; [Discharged]
        // assert I != null && I.alloc == True; [Discharged]
        guard_1 := abst_Lelem_next_0[I] == null;
        havoc guard_1;
        // assert owner[I] == tid; [Discharged]
        // assert I != null && I.alloc == True; [Discharged]
        if (*)
        {
            havoc tmp;
            fresh_0 := tail == I;
            if (fresh_0)
            {
                tail := null;
                wlock := 0;
                return;
            }
        }

        // assert wlock == tid; [Discharged]
        // assert owner[I] == tid; [Discharged]
        // assert I != null && I.alloc == True; [Discharged]
        if (*)
        {
            assume I.next != null;
        }
        else
        {
            assume I.next == null;
            tail := null;
            wlock := 0;
            return;
        }

        // assert I.next != null && I.next.alloc == True; [Discharged]
        // assert I != null && I.alloc == True; [Discharged]
        havoc temp;
        I.next.prev := temp;
        // assert owner[I] == tid; [Discharged]
        // assert I.next != null && I.next.alloc == True; [Discharged]
        // assert I != null && I.alloc == True; [Discharged]
        I.next.spin := 0;
        wlock := I.next.owned;
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

invariant (forall elem: Lelem :: elem.alloc == False ==> owner[elem] == 0);

invariant (forall elem: Lelem :: elem == null ==> elem.next == null && elem.prev == null);

invariant (forall elem: Lelem :: elem.alloc == True ==> elem.owned != 0);

invariant tail == null <==> wlock == 0;

invariant tail != null ==> tail.alloc == True;

invariant tail.next == null;

invariant (forall elem: Lelem, t: int :: owner[elem] == t && t != 0 && ReachBetween(Lelem_next, elem, tail, tail) ==> wlock == t && elem.next == null);


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

var wlock: [RWLock]int; 

procedure writerLock(L: RWLock) returns (I: Lelem);
  modifies Lelem_alloc, Lelem_state, Lelem_spin, Lelem_next, RWLock_elem, owner;



implementation writerLock(L: RWLock) returns (I: Lelem)
{
  var pred: Lelem;
		var tmp: Lelem;
		var tmp2: int;
  Atomic_5:
    atomic { // None-mover
        I := New Lelem;
								assume (forall l:RWLock :: l.elem!=null ==> !ReachBetween(Lelem_next,I,l.elem,null));
								assume (forall l:RWLock :: I!=l.elem);
								assume I != null;

        // I.state := WRITER;

        I.spin := 1;

        I.next := null;
								
								//havoc I.prev;
								
        // call pred := fetch_and_store(I, L);
        pred := L.elem;
        L.elem := I;

        if (pred != null)
        {
            // assert pred.alloc == True && pred.next == null && I != null;
            pred.next := I; 
        }
								else { if(*) {I.spin := 0;}else{I.spin := 1;} }

        owner[I] := tid;
    }

  Atomic_21:
    atomic { // None-mover
								assert I != null && I.alloc == True;
								assert ReachBetween(Lelem_next,I,L.elem,L.elem);
        assert owner[I] == tid;
								assert wlock[L]==0; wlock[L]:=tid;
								assert (forall l:RWLock :: l != L ==> !ReachBetween(Lelem_next, I, l.elem, l.elem));
        if (pred != null)
        {
            assume I.spin != 1;
        }
    }
}



procedure writerUnlock(L: RWLock, I: Lelem);
  modifies RWLock_elem, Lelem_prev, Lelem_spin, RWLock_elem, owner;



implementation writerUnlock(L: RWLock, I: Lelem)
{
  var pred: Lelem;
  var tmp: Lelem;
		var tmp2: Lelem;
//  var guard_1: bool;
  var fresh_0: bool;
//  var abst_Lelem_next_0: [Lelem]Lelem;

  Atomic_12:
    atomic { // None-mover
								assert wlock[L]==tid;
        assert owner[I] == tid;
        assert I != null && I.alloc == True;
        if (*)
        {
            fresh_0 := L.elem == I;
            if (fresh_0)
            {
                L.elem := null;
                // havoc guard_1, tmp, fresh_0, abst_Lelem_next_0;
																havoc fresh_0;
                return;
            }
        }

        // havoc guard_1, tmp, fresh_0, abst_Lelem_next_0;
								havoc fresh_0;
    }

  Atomic_15:
    atomic { // None-mover
				    assert (forall l:RWLock :: l!=L ==> l.elem!=I);
				    assert ReachBetween(Lelem_next,I,L.elem,L.elem);
								assert owner[I] == tid;
				    assert wlock[L]==tid;
        assert I != null && I.alloc == True;
								assert L.elem!=null;
								
								if (*) {
									assume I.next != null;
									assert I.next.alloc == True;
									//I.next.prev := null;
									I.next.spin := 0;
								} else {
								 assume I.next == null;
									L.elem := null;
								}
								//tmp2 := I.next;
								havoc I.next;
								assume (forall l:RWLock :: l.elem!=null ==> !ReachBetween(Lelem_next,I.next,l.elem,l.elem));
								havoc tmp2;
								

        owner[I] := 0;
								wlock[L]:=0;
								
								Free I;
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

invariant (forall L: Lelem :: L.alloc == False ==> owner[L] == 0);

invariant (forall L: RWLock :: L.elem != null ==> L.elem.alloc == True);

invariant (forall L1: RWLock, L2: RWLock :: L1.elem != null && L2.elem != null && L1 != L2 ==> L1.elem != L2.elem);

invariant (forall L: RWLock :: L.elem != null ==> L.elem.next == null);

invariant (forall i1,i2:Lelem, l1,l2:RWLock :: ReachBetween(Lelem_next,i1,l1.elem,l1.elem) && ReachBetween(Lelem_next,i2,l2.elem,l2.elem) && l1!=l2 && l1.elem!=null && l2.elem!=null ==> i1!=i2);
invariant (null.next == null) && (null.prev == null);

invariant (forall i: Lelem :: i.alloc==False ==> (i.next==null && i.prev==null));
invariant (forall i: Lelem :: i.spin == 0 || i.spin == 1);
invariant (forall i:Lelem, l1,l2:RWLock :: ReachBetween(Lelem_next,i,l1.elem,l1.elem) && ReachBetween(Lelem_next,i,l2.elem,l2.elem) && l1.elem!=null && l2.elem!=null ==> l1==l2);

invariant (forall i1,i2,i3,i4:Lelem, l1,l2:RWLock :: ReachBetween(Lelem_next,i1,i2,l1.elem) && ReachBetween(Lelem_next,i3,i4,l2.elem) && l1!=l2 && l1.elem != null && l2.elem != null ==> (i1 != i3 && i2 != i4));

invariant (forall i:Lelem :: owner[i] != 0 ==> ReachBetween(Lelem_next, i, null, null));

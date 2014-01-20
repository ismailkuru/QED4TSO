const unique NULL_OBJECT: Object;

const unique NULL_QUEUE_ITEM: QueueItem;

const unique NULL_TWO_LOCK_QUEUE: TwoLockQueue;

record Object {
  lock: boolean;
  alloc: AllocType;
}

record QueueItem {
  next: QueueItem;
  value: Object;
  alloc: AllocType;
}

record TwoLockQueue {
  head: QueueItem;
  tail: QueueItem;
  headLock: Object;
  tailLock: Object;
  alloc: AllocType;
}

procedure TwoLockQueue_enqueue(this: TwoLockQueue, value: Object);
  modifies QueueItem_alloc, QueueItem_next, QueueItem_value, constructed, TwoLockQueue_tail, Object_lock, owner;



implementation TwoLockQueue_enqueue(this: TwoLockQueue, value: Object)
{
  var x_i: QueueItem;
  var tl: Object;
  var t: QueueItem;

  Atomic_1:
    atomic { // Non-mover
        x_i := New QueueItem;
        assume x_i != NULL_QUEUE_ITEM;
        x_i.next := NULL_QUEUE_ITEM;
        x_i.value := value;
        constructed[x_i] := True;
        this.tail.next := x_i;
        this.tail := this.tail.next;
        havoc t;
        havoc tl;
        this.tailLock.lock := False;
        owner[this.tailLock] := 0;
    }
}



procedure TwoLock_dequeue(this: TwoLockQueue) returns (result: Object);
  modifies TwoLockQueue_head, QueueItem_value, Object_lock, owner;



implementation TwoLock_dequeue(this: TwoLockQueue) returns (result: Object)
{
  var x_d: Object;
  var hl: Object;
  var node: QueueItem;
  var newHead: QueueItem;
  var h: QueueItem;

  Atomic_10:
    atomic { // Non-mover
        havoc hl;
        havoc node;
        havoc h;
        havoc newHead;
        if (this.head.next != NULL_QUEUE_ITEM)
        {
            x_d := this.head.next.value;
            this.head := this.head.next;
            this.head.value := NULL_OBJECT;
        }

        result := x_d;
        this.headLock.lock := False;
        owner[this.headLock] := 0;
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

var constructed: [QueueItem]boolean;

var owner: [Object]int;

invariant (forall obj: Object :: obj.lock == True <==> owner[obj] != 0);

invariant (forall lock: TwoLockQueue :: lock.tailLock != lock.headLock);

invariant (forall lock1: TwoLockQueue, lock2: TwoLockQueue :: lock1 != lock2 ==> lock1.headLock != lock2.headLock);

invariant (forall lock1: TwoLockQueue, lock2: TwoLockQueue :: lock1 != lock2 ==> lock1.tailLock != lock2.tailLock);

invariant (forall lock1: TwoLockQueue, lock2: TwoLockQueue :: lock1 != lock2 ==> lock1.headLock != lock2.tailLock);

invariant NULL_QUEUE_ITEM.alloc == Null && NULL_QUEUE_ITEM.next == NULL_QUEUE_ITEM;

invariant (forall lock: TwoLockQueue :: constructed[lock.tail] == True);

invariant (forall item: QueueItem :: constructed[item] == True ==> item != NULL_QUEUE_ITEM);

invariant (forall item: QueueItem :: constructed[item] == True ==> item.alloc == Alloc);

invariant (forall lock1: TwoLockQueue, lock2: TwoLockQueue :: lock1 != lock2 ==> lock1.tail != lock2.tail);

invariant (forall lock: TwoLockQueue :: lock.tail.next == NULL_QUEUE_ITEM);

invariant (forall lock1: TwoLockQueue, lock2: TwoLockQueue, item: QueueItem :: lock1 != lock2 && ReachBetween(QueueItem_next, lock1.head, item, item) ==> !ReachBetween(QueueItem_next, lock2.head, item, item)) && (forall lock: TwoLockQueue :: ReachBetween(QueueItem_next, lock.head, lock.tail, NULL_QUEUE_ITEM)) && (forall lock: TwoLockQueue, item: QueueItem :: ReachBetween(QueueItem_next, lock.head, item, lock.tail) ==> constructed[item] == True);


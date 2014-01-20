const unique NULL_NODE: Node;

const unique NULL_THREAD: Thread;

const unique NullPointerException: Exception;

const unique Error: Exception;

const unique IllegalMonitorStateException: Exception;

const unique RuntimeException: Exception;

record Thread {
  id: int;
  interrupted: boolean;
  alloc: AllocType;
}

var Threads: [int]Thread;

invariant Threads[0] == NULL_THREAD;

invariant (forall i: int :: Threads[i].id == i);

procedure {:isatomic true} {:ispublic false} Thread_nativeIsInterrupted(this: Thread, clearInterrupted: bool) returns (result: bool);
  modifies Thread_interrupted;



implementation Thread_nativeIsInterrupted(this: Thread, clearInterrupted: bool) returns (result: bool)
{
  var guard: bool;

  Atomic_1:
    atomic { // Non-mover
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



procedure {:ispublic false} Thread_interrupt(this: Thread);
  modifies Thread_interrupted;



implementation Thread_interrupt(this: Thread)
{
  Atomic_2:
    atomic { // Non-mover
        this.interrupted := True;
    }
}



procedure {:ispublic false} {:isatomic true} Thread_currentThread() returns (result: Thread);



implementation Thread_currentThread() returns (result: Thread)
{
  Atomic_3:
    atomic { // Non-mover
        result := Threads[tid];
    }
}



procedure {:ispublic false} Thread_interrupted() returns (result: bool);



implementation Thread_interrupted() returns (result: bool)
{
  var currentThread: Thread;

  Call_4:
      call currentThread := Thread_currentThread();

  Call_5:
      call result := Thread_nativeIsInterrupted(currentThread, true);
}



type NodeWaitStatus;

const unique CANCELLED: NodeWaitStatus;

const unique SIGNAL: NodeWaitStatus;

const unique CONDITION: NodeWaitStatus;

const unique NO_WAIT_STATUS: NodeWaitStatus;

axiom (forall nws: NodeWaitStatus :: nws == CANCELLED || nws == SIGNAL || nws == CONDITION || nws == NO_WAIT_STATUS);

const unique SHARED: Node;

record Node {
  waitStatus: NodeWaitStatus;
  prev: Node;
  next: Node;
  nextWaiter: Node;
  thread: Thread;
  alloc: AllocType;
}

procedure {:ispublic false} Node_Node_2(this: Node, thread: Thread, mode: Node);
  modifies Node_nextWaiter, Node_thread, Node_next, Node_prev, Node_waitStatus;



implementation Node_Node_2(this: Node, thread: Thread, mode: Node)
{
  Atomic_6:
    atomic { // Non-mover
        this.nextWaiter := mode;
    }

  Atomic_7:
    atomic { // Non-mover
        this.thread := thread;
    }

  Atomic_8:
    atomic { // Non-mover
        this.next := NULL_NODE;
    }

  Atomic_9:
    atomic { // Non-mover
        this.prev := NULL_NODE;
    }

  Atomic_10:
    atomic { // Non-mover
        this.waitStatus := NO_WAIT_STATUS;
    }
}



procedure {:ispublic false} Node_predecessor(this: Node) returns (result: Node);



implementation Node_predecessor(this: Node) returns (result: Node)
{
  Atomic_11:
    atomic { // Non-mover
        result := this.prev;
    }

    if (result == NULL_NODE)
    {
      Atomic_12:
        atomic { // Non-mover
            throw NullPointerException;
        }
    }
}



record NonfairSync {
  exclusiveOwnerThread: Thread;
  head: Node;
  tail: Node;
  state: int;
  alloc: AllocType;
}

procedure {:ispublic false} AOS_setExclusiveOwnerThread(this: NonfairSync, t: Thread);
  modifies NonfairSync_exclusiveOwnerThread;



implementation AOS_setExclusiveOwnerThread(this: NonfairSync, t: Thread)
{
  Atomic_13:
    atomic { // Non-mover
        this.exclusiveOwnerThread := t;
    }
}



procedure {:ispublic false} AOS_getExclusiveOwnerThread(this: NonfairSync) returns (result: Thread);



implementation AOS_getExclusiveOwnerThread(this: NonfairSync) returns (result: Thread)
{
  Atomic_14:
    atomic { // Non-mover
        result := this.exclusiveOwnerThread;
    }
}



procedure {:ispublic false} AQS_getState(this: NonfairSync) returns (result: int);



implementation AQS_getState(this: NonfairSync) returns (result: int)
{
  Atomic_15:
    atomic { // Non-mover
        result := this.state;
    }
}



procedure {:ispublic false} AQS_setState(this: NonfairSync, newState: int);
  modifies NonfairSync_state;



implementation AQS_setState(this: NonfairSync, newState: int)
{
  Atomic_16:
    atomic { // Non-mover
        this.state := newState;
    }
}



procedure {:ispublic false} {:isatomic true} AQS_enq(this: NonfairSync, node: Node) returns (result: Node);
  modifies Node_alloc, Node_prev, Node_next, Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head, NonfairSync_tail;



implementation AQS_enq(this: NonfairSync, node: Node) returns (result: Node)
{
  var h: Node;
  var t: Node;

  Atomic_17:
    atomic { // Non-mover
        t := this.tail;
        if (t == NULL_NODE)
        {
            h := New Node;
            assume h != NULL_NODE;
            h.prev := NULL_NODE;
            h.next := NULL_NODE;
            h.nextWaiter := NULL_NODE;
            h.thread := NULL_THREAD;
            h.waitStatus := NO_WAIT_STATUS;
            h.next := node;
            node.prev := h;
            this.head := h;
            this.tail := node;
            result := h;
        }
        else
        {
            node.prev := t;
            this.tail := node;
            t.next := node;
            result := t;
        }
    }
}



procedure {:ispublic false} AQS_setHead(this: NonfairSync, node: Node);
  modifies NonfairSync_head, Node_thread, Node_prev;



implementation AQS_setHead(this: NonfairSync, node: Node)
{
  Atomic_18:
    atomic { // Non-mover
        this.head := node;
    }

  Atomic_19:
    atomic { // Non-mover
        node.thread := NULL_THREAD;
    }

  Atomic_20:
    atomic { // Non-mover
        node.prev := NULL_NODE;
    }
}



procedure {:ispublic false} AQS_addWaiter(this: NonfairSync, mode: Node) returns (result: Node);
  modifies Node_alloc, Node_prev, Node_next;



implementation AQS_addWaiter(this: NonfairSync, mode: Node) returns (result: Node)
{
  var node: Node;
  var pred: Node;
  var currentThread: Thread;
  var dummyNode: Node;
  var dummy: bool;
  var done: bool;

  Atomic_21:
    atomic { // Non-mover
        done := false;
    }

  Call_22:
      call currentThread := Thread_currentThread();

  Atomic_23:
    atomic { // Non-mover
        node := New Node;
    }

  Atomic_24:
    atomic { // Non-mover
        assume node != NULL_NODE;
    }

  Call_25:
      call Node_Node_2(node, currentThread, mode);

  Atomic_26:
    atomic { // Non-mover
        pred := this.tail;
    }

    if (pred != NULL_NODE)
    {
      Atomic_27:
        atomic { // Non-mover
            node.prev := pred;
        }

      Call_28:
          call dummy := AQS_compareAndSetTail(this, pred, node);

        if (dummy)
        {
          Atomic_29:
            atomic { // Non-mover
                pred.next := node;
            }

          Atomic_30:
            atomic { // Non-mover
                result := node;
            }

          Atomic_31:
            atomic { // Non-mover
                done := true;
            }
        }
    }

    if (!done)
    {
      Call_32:
          call dummyNode := AQS_enq(this, node);

      Atomic_33:
        atomic { // Non-mover
            result := node;
        }
    }
}



procedure {:ispublic false} AQS_unparkSuccessor(this: NonfairSync, node: Node);



implementation AQS_unparkSuccessor(this: NonfairSync, node: Node)
{
  var s: Node;
  var t: Node;
  var dummy: bool;
  var dummy_2: bool;
  var guard: bool;

  Call_34:
      call dummy := AQS_compareAndSetWaitStatus(node, SIGNAL, NO_WAIT_STATUS);

  Atomic_35:
    atomic { // Non-mover
        s := node.next;
    }

  Atomic_36:
    atomic { // Non-mover
        dummy := s == NULL_NODE || s.waitStatus == CANCELLED;
    }

    if (dummy)
    {
      Atomic_37:
        atomic { // Non-mover
            s := NULL_NODE;
        }

      Atomic_38:
        atomic { // Non-mover
            t := this.tail;
        }

      Atomic_39:
        atomic { // Non-mover
            guard := t != NULL_NODE && t != node;
        }

        while (guard)
        {
          Atomic_40:
            atomic { // Non-mover
                dummy_2 := t.waitStatus != CANCELLED;
            }

            if (dummy_2)
            {
              Atomic_41:
                atomic { // Non-mover
                    s := t;
                }
            }

          Atomic_42:
            atomic { // Non-mover
                t := t.prev;
            }

          Atomic_43:
            atomic { // Non-mover
                guard := t != NULL_NODE && t != node;
            }
        }
    }

    if (s != NULL_NODE)
    {
      Call_44:
          call LockSupport_unpark(s.thread);
    }
}



procedure AQS_release(this: NonfairSync, arg: int) returns (result: bool);



implementation AQS_release(this: NonfairSync, arg: int) returns (result: bool)
{
  var h: Node;
  var dummy: bool;

  Call_45:
      call result := Sync_tryRelease(this, arg);

    if (result)
    {
      Atomic_46:
        atomic { // Non-mover
            h := this.head;
        }

      Atomic_47:
        atomic { // Non-mover
            dummy := h != NULL_NODE && h.waitStatus != NO_WAIT_STATUS;
        }

        if (dummy)
        {
          Call_48:
              call AQS_unparkSuccessor(this, h);
        }
    }
}



procedure {:ispublic false} AQS_cancelAcquire(this: NonfairSync, node: Node);
  modifies Node_thread, Node_prev, Node_waitStatus, Node_next;



implementation AQS_cancelAcquire(this: NonfairSync, node: Node)
{
  var guard: bool;
  var pred: Node;
  var predNext: Node;
  var next: Node;
  var dummy: bool;
  var dummy_2: bool;
  var dummy_3: bool;

    if (node != NULL_NODE)
    {
      Atomic_49:
        atomic { // Non-mover
            node.thread := NULL_THREAD;
        }

      Atomic_50:
        atomic { // Non-mover
            pred := node.prev;
        }

      Atomic_51:
        atomic { // Non-mover
            dummy_2 := pred.waitStatus == CANCELLED;
        }

        while (dummy_2)
        {
          Atomic_52:
            atomic { // Non-mover
                pred := pred.prev;
            }

          Atomic_53:
            atomic { // Non-mover
                node.prev := pred;
            }

          Atomic_54:
            atomic { // Non-mover
                dummy_2 := pred.waitStatus == CANCELLED;
            }
        }

      Atomic_55:
        atomic { // Non-mover
            predNext := pred.next;
        }

      Atomic_56:
        atomic { // Non-mover
            node.waitStatus := CANCELLED;
        }

      Atomic_57:
        atomic { // Non-mover
            guard := node == this.tail;
        }

        if (guard)
        {
          Call_58:
              call guard := AQS_compareAndSetTail(this, node, pred);

            if (guard)
            {
              Call_59:
                  call dummy := AQS_compareAndSetNext(pred, predNext, NULL_NODE);
            }
        }

        if (!guard)
        {
          Atomic_60:
            atomic { // Non-mover
                guard := pred != this.head;
            }

            if (guard)
            {
              Atomic_61:
                atomic { // Non-mover
                    guard := pred.waitStatus == SIGNAL;
                }

                if (!guard)
                {
                  Call_62:
                      call guard := AQS_compareAndSetWaitStatus(pred, NO_WAIT_STATUS, SIGNAL);
                }

                if (guard)
                {
                  Atomic_63:
                    atomic { // Non-mover
                        guard := pred.thread != NULL_THREAD;
                    }

                    if (guard)
                    {
                      Atomic_64:
                        atomic { // Non-mover
                            next := node.next;
                        }

                      Atomic_65:
                        atomic { // Non-mover
                            dummy_3 := next != NULL_NODE && next.waitStatus != CANCELLED;
                        }

                        if (dummy_3)
                        {
                          Call_66:
                              call dummy := AQS_compareAndSetNext(pred, predNext, next);
                        }
                    }
                }
            }

            if (!guard)
            {
              Call_67:
                  call AQS_unparkSuccessor(this, node);
            }

          Atomic_68:
            atomic { // Non-mover
                node.next := node;
            }
        }
    }
}



procedure {:ispublic false} AQS_parkAndCheckInterrupt(this: NonfairSync) returns (result: bool);



implementation AQS_parkAndCheckInterrupt(this: NonfairSync) returns (result: bool)
{
  var currentThread: Thread;

  Call_69:
      call currentThread := Thread_currentThread();

  Call_70:
      call LockSupport_park(currentThread);

  Call_71:
      call result := Thread_interrupted();
}



procedure {:ispublic false} AQS_acquireQueued(this: NonfairSync, node: Node, arg: int) returns (result: bool);
  modifies Node_next;



implementation AQS_acquireQueued(this: NonfairSync, node: Node, arg: int) returns (result: bool)
{
  var interrupted: bool;
  var p: Node;
  var guard: bool;
  var dummy: bool;

  Try_72:
    try {
      Atomic_73:
        atomic { // Non-mover
            interrupted := false;
        }

        while (true)
        {
          Call_74:
              call p := Node_predecessor(node);

          Atomic_75:
            atomic { // Non-mover
                guard := p == this.head;
            }

            if (guard)
            {
              Call_76:
                  call guard := NonfairSync_tryAcquire(this, arg);

                if (guard)
                {
                  Call_77:
                      call AQS_setHead(this, node);

                  Atomic_78:
                    atomic { // Non-mover
                        p.next := NULL_NODE;
                    }

                  Atomic_79:
                    atomic { // Non-mover
                        result := interrupted;
                    }

                  Atomic_80:
                    atomic { // Non-mover
                        return;
                    }
                }
            }

          Call_81:
              call dummy := AQS_shouldParkAfterFailedAcquire(p, node);

            if (dummy)
            {
              Call_82:
                  call dummy := AQS_parkAndCheckInterrupt(this);

                if (dummy)
                {
                  Atomic_83:
                    atomic { // Non-mover
                        interrupted := true;
                    }
                }
            }
        }
}
    catch (RuntimeException){
      Call_84:
          call AQS_cancelAcquire(this, node);
    }
}



procedure {:ispublic true} AQS_acquire(this: NonfairSync, arg: int);



implementation AQS_acquire(this: NonfairSync, arg: int)
{
  var guard: bool;
  var dummyNode: Node;

  Call_85:
      call guard := NonfairSync_tryAcquire(this, arg);

    if (!guard)
    {
      Call_86:
          call dummyNode := AQS_addWaiter(this, NULL_NODE);

      Call_87:
          call guard := AQS_acquireQueued(this, dummyNode, arg);

        if (guard)
        {
          Call_88:
              call AQS_selfInterrupt();
        }
    }
}



procedure {:ispublic false} AQS_shouldParkAfterFailedAcquire(pred: Node, node: Node) returns (result: bool);
  modifies Node_prev, Node_next;



implementation AQS_shouldParkAfterFailedAcquire(pred: Node, node: Node) returns (result: bool)
{
  var pred_dup: Node;
  var s: NodeWaitStatus;
  var dummy: bool;
  var guard: bool;

  Atomic_89:
    atomic { // Non-mover
        s := pred.waitStatus;
    }

    if (s == SIGNAL || s == CONDITION)
    {
      Atomic_90:
        atomic { // Non-mover
            result := true;
        }
    }
    else
    {
        if (s == CANCELLED)
        {
          Atomic_91:
            atomic { // Non-mover
                pred_dup := pred;
            }

          Atomic_92:
            atomic { // Non-mover
                pred_dup := pred_dup.prev;
            }

          Atomic_93:
            atomic { // Non-mover
                node.prev := pred_dup;
            }

          Atomic_94:
            atomic { // Non-mover
                guard := pred_dup.waitStatus == CANCELLED;
            }

            while (guard)
            {
              Atomic_95:
                atomic { // Non-mover
                    pred_dup := pred_dup.prev;
                }

              Atomic_96:
                atomic { // Non-mover
                    node.prev := pred_dup;
                }

              Atomic_97:
                atomic { // Non-mover
                    guard := pred_dup.waitStatus == CANCELLED;
                }
            }

          Atomic_98:
            atomic { // Non-mover
                pred_dup.next := node;
            }

          Atomic_99:
            atomic { // Non-mover
                result := false;
            }
        }
        else
        {
          Call_100:
              call dummy := AQS_compareAndSetWaitStatus(pred, NO_WAIT_STATUS, SIGNAL);

          Atomic_101:
            atomic { // Non-mover
                result := false;
            }
        }
    }
}



procedure {:ispublic false} AQS_selfInterrupt();



implementation AQS_selfInterrupt()
{
  var currentThread: Thread;

  Call_102:
      call currentThread := Thread_currentThread();

  Call_103:
      call Thread_interrupt(currentThread);
}



procedure {:ispublic false} {:isatomic true} AQS_compareAndSetState(this: NonfairSync, expect: int, update: int) returns (result: bool);
  modifies NonfairSync_state;



implementation AQS_compareAndSetState(this: NonfairSync, expect: int, update: int) returns (result: bool)
{
  Atomic_104:
    atomic { // Non-mover
        result := this.state == expect;
        if (result)
        {
            this.state := update;
        }
    }
}



procedure {:ispublic false} {:isatomic true} AQS_compareAndSetTail(this: NonfairSync, expect: Node, update: Node) returns (result: bool);
  modifies NonfairSync_tail;



implementation AQS_compareAndSetTail(this: NonfairSync, expect: Node, update: Node) returns (result: bool)
{
  Atomic_105:
    atomic { // Non-mover
        result := this.tail == expect;
        if (result)
        {
            this.tail := update;
        }
    }
}



procedure {:ispublic false} {:isatomic true} AQS_compareAndSetWaitStatus(node: Node, expect: NodeWaitStatus, update: NodeWaitStatus) returns (result: bool);
  modifies Node_waitStatus;



implementation AQS_compareAndSetWaitStatus(node: Node, expect: NodeWaitStatus, update: NodeWaitStatus) returns (result: bool)
{
  Atomic_106:
    atomic { // Non-mover
        result := node.waitStatus == expect;
        if (result)
        {
            node.waitStatus := update;
        }
    }
}



procedure {:ispublic false} {:isatomic true} AQS_compareAndSetNext(node: Node, expect: Node, update: Node) returns (result: bool);
  modifies Node_next;



implementation AQS_compareAndSetNext(node: Node, expect: Node, update: Node) returns (result: bool)
{
  Atomic_107:
    atomic { // Non-mover
        result := node.next == expect;
        if (result)
        {
            node.next := update;
        }
    }
}



procedure {:ispublic false} Sync_tryRelease(this: NonfairSync, releases: int) returns (result: bool);



implementation Sync_tryRelease(this: NonfairSync, releases: int) returns (result: bool)
{
  var c: int;
  var currentThread: Thread;
  var ownerThread: Thread;

  Call_108:
      call c := AQS_getState(this);

  Atomic_109:
    atomic { // Non-mover
        c := c - releases;
    }

  Call_110:
      call currentThread := Thread_currentThread();

  Call_111:
      call ownerThread := AOS_getExclusiveOwnerThread(this);

    if (currentThread != ownerThread)
    {
      Atomic_112:
        atomic { // Non-mover
            throw IllegalMonitorStateException;
        }
    }

  Atomic_113:
    atomic { // Non-mover
        result := false;
    }

    if (c == 0)
    {
      Atomic_114:
        atomic { // Non-mover
            result := true;
        }

      Call_115:
          call AOS_setExclusiveOwnerThread(this, NULL_THREAD);
    }

  Call_116:
      call AQS_setState(this, c);
}



procedure {:ispublic false} Sync_nonfairTryAcquire(this: NonfairSync, acquires: int) returns (result: bool);



implementation Sync_nonfairTryAcquire(this: NonfairSync, acquires: int) returns (result: bool)
{
  var current: Thread;
  var c: int;
  var nextc: int;
  var dummy: bool;
  var ownerThread: Thread;

  Atomic_117:
    atomic { // Non-mover
        result := false;
    }

  Call_118:
      call current := Thread_currentThread();

  Call_119:
      call c := AQS_getState(this);

    if (c == 0)
    {
      Call_120:
          call dummy := AQS_compareAndSetState(this, 0, acquires);

        if (dummy)
        {
          Call_121:
              call AOS_setExclusiveOwnerThread(this, current);

          Atomic_122:
            atomic { // Non-mover
                result := true;
            }
        }
    }
    else
    {
      Call_123:
          call ownerThread := AOS_getExclusiveOwnerThread(this);

        if (current == ownerThread)
        {
          Atomic_124:
            atomic { // Non-mover
                nextc := c + acquires;
            }

            if (nextc < 0)
            {
              Atomic_125:
                atomic { // Non-mover
                    throw Error;
                }
            }
            else
            {
              Call_126:
                  call AQS_setState(this, nextc);

              Atomic_127:
                atomic { // Non-mover
                    result := true;
                }
            }
        }
    }
}



procedure {:ispublic false} NonfairSync_tryAcquire(this: NonfairSync, acquires: int) returns (result: bool);



implementation NonfairSync_tryAcquire(this: NonfairSync, acquires: int) returns (result: bool)
{
  Call_128:
      call result := Sync_nonfairTryAcquire(this, acquires);
}



procedure {:ispublic false} NonfairSync_lock(this: NonfairSync);



implementation NonfairSync_lock(this: NonfairSync)
{
  var dummy: bool;
  var currentThread: Thread;

  Call_129:
      call dummy := AQS_compareAndSetState(this, 0, 1);

    if (dummy)
    {
      Call_130:
          call currentThread := Thread_currentThread();

      Call_131:
          call AOS_setExclusiveOwnerThread(this, currentThread);
    }
    else
    {
      Call_132:
          call AQS_acquire(this, 1);
    }
}



procedure {:ispublic false} {:isatomic true} LockSupport_park(thread: Thread);



implementation LockSupport_park(thread: Thread)
{
  Atomic_133:
    atomic { // Non-mover
        assume true;
    }
}



procedure {:ispublic false} {:isatomic true} LockSupport_unpark(thread: Thread);



implementation LockSupport_unpark(thread: Thread)
{
  Atomic_134:
    atomic { // Non-mover
        assume true;
    }
}



record ReentrantLock {
  sync: NonfairSync;
  alloc: AllocType;
}

procedure ReentrantLock_unlock(this: ReentrantLock);



implementation ReentrantLock_unlock(this: ReentrantLock)
{
  var dummy: bool;

  Call_135:
      call dummy := AQS_release(this.sync, 1);
}



procedure ReentrantLock_lock(this: ReentrantLock);



implementation ReentrantLock_lock(this: ReentrantLock)
{
  Call_136:
      call NonfairSync_lock(this.sync);
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


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

record NonfairSync {
  exclusiveOwnerThread: Thread;
  head: Node;
  tail: Node;
  state: int;
  alloc: AllocType;
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
        assert con[node] == True;
        node.thread := NULL_THREAD;
    }

  Atomic_20:
    atomic { // Non-mover
        node.prev := NULL_NODE;
    }
}



procedure {:ispublic false} AQS_addWaiter(this: NonfairSync, mode: Node) returns (result: Node);
  modifies Node_alloc, owner, Node_prev, Node_next, Node_nextWaiter, Node_thread, Node_waitStatus, con, NonfairSync_head, NonfairSync_tail;



implementation AQS_addWaiter(this: NonfairSync, mode: Node) returns (result: Node)
{
  var node: Node;
  var pred: Node;
  var currentThread: Thread;
  var dummyNode: Node;
  var dummy: bool;
  var done: bool;
  var fresh_0: Node;
  var fresh_1: Node;

  Atomic_21:
    atomic { // Non-mover
        done := false;
    }

  Call_22:
    atomic { // Non-mover
        assert true;
        // call currentThread := Thread_currentThread();
        currentThread := Threads[tid];
    }

  Atomic_23:
    atomic { // Non-mover
        node := New Node;
        con[node] := False;
        owner[node] := tid;
    }

  Atomic_24:
    atomic { // Non-mover
        assume node != NULL_NODE;
    }

  Call_25:
    atomic { // Non-mover
        assert true;
        // call Node_Node_2(node, currentThread, mode);
        assert node.alloc == Alloc;
        assert owner[node] == tid;
        assert con[node] == False;
        node.nextWaiter := mode;

        node.thread := currentThread;

        node.next := NULL_NODE;

        node.prev := NULL_NODE;

        node.waitStatus := NO_WAIT_STATUS;
        con[node] := True;
    }

  Atomic_26:
    atomic { // Non-mover
        pred := this.tail;
    }

    if (pred != NULL_NODE)
    {
      Atomic_27:
        atomic { // Non-mover
            assert con[node] == True;
            node.prev := pred;
        }

      Call_28:
        atomic { // Non-mover
            assert true;
            // call dummy := AQS_compareAndSetTail(this, pred, node);
            dummy := this.tail == pred;
            if (dummy)
            {
                this.tail := node;
            }
        }

        if (dummy)
        {
          Atomic_29:
            atomic { // Non-mover
                assert con[pred] == True;
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
        atomic { // Non-mover
            assert con[node] == True;
            assert true;
            fresh_0 := this.tail;
            if (fresh_0 == NULL_NODE)
            {
                fresh_1 := New Node;
                owner[fresh_1] := tid;
                assume fresh_1 != NULL_NODE;
                fresh_1.prev := NULL_NODE;
                fresh_1.next := NULL_NODE;
                fresh_1.nextWaiter := NULL_NODE;
                fresh_1.thread := NULL_THREAD;
                fresh_1.waitStatus := NO_WAIT_STATUS;
                con[fresh_1] := True;
                fresh_1.next := node;
                node.prev := fresh_1;
                this.head := fresh_1;
                this.tail := node;
                dummyNode := fresh_1;
            }
            else
            {
                assert con[fresh_0] == True;
                node.prev := fresh_0;
                this.tail := node;
                fresh_0.next := node;
                dummyNode := fresh_0;
            }
        }

      Atomic_33:
        atomic { // Non-mover
            result := node;
        }
    }
}



procedure {:ispublic false} AQS_unparkSuccessor(this: NonfairSync, node: Node);
  modifies Node_waitStatus;



implementation AQS_unparkSuccessor(this: NonfairSync, node: Node)
{
  var s: Node;
  var t: Node;
  var dummy: bool;
  var dummy_2: bool;
  var guard: bool;

  Call_34:
    atomic { // Non-mover
        assert true;
        // call dummy := AQS_compareAndSetWaitStatus(node, SIGNAL, NO_WAIT_STATUS);
        dummy := node.waitStatus == SIGNAL;
        if (dummy)
        {
            node.waitStatus := NO_WAIT_STATUS;
        }
    }

  Atomic_35:
    atomic { // Non-mover
        assert con[node] == True;
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

          Atomic_143:
            atomic { // Non-mover
                if (dummy_2)
                {
                    s := t;
                }
            }

          Atomic_42:
            atomic { // Non-mover
                assert con[t] == True;
                t := t.prev;
            }

          Atomic_43:
            atomic { // Non-mover
                guard := t != NULL_NODE && t != node;
            }
        }
    }

  Atomic_144:
    atomic { // Non-mover
        if (s != NULL_NODE)
        {
            assert true;
            // call LockSupport_unpark(s.thread);
            assume true;
        }
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
  modifies Node_thread, Node_prev, Node_waitStatus, Node_next, NonfairSync_tail;



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
            assert con[node] == True;
            node.thread := NULL_THREAD;
        }

      Atomic_50:
        atomic { // Non-mover
            assert con[node] == True;
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
                assert con[pred] == True;
                pred := pred.prev;
            }

          Atomic_53:
            atomic { // Non-mover
                assert con[node] == True;
                node.prev := pred;
            }

          Atomic_54:
            atomic { // Non-mover
                dummy_2 := pred.waitStatus == CANCELLED;
            }
        }

      Atomic_55:
        atomic { // Non-mover
            assert con[pred] == True;
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
            atomic { // Non-mover
                assert true;
                // call guard := AQS_compareAndSetTail(this, node, pred);
                guard := this.tail == node;
                if (guard)
                {
                    this.tail := pred;
                }
            }

          Atomic_145:
            atomic { // Non-mover
                assert con[pred] == True;
                if (guard)
                {
                    assert true;
                    // call dummy := AQS_compareAndSetNext(pred, predNext, NULL_NODE);
                    dummy := pred.next == predNext;
                    if (dummy)
                    {
                        pred.next := NULL_NODE;
                    }
                }
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

              Atomic_146:
                atomic { // Non-mover
                    if (!guard)
                    {
                        assert true;
                        // call guard := AQS_compareAndSetWaitStatus(pred, NO_WAIT_STATUS, SIGNAL);
                        guard := pred.waitStatus == NO_WAIT_STATUS;
                        if (guard)
                        {
                            pred.waitStatus := SIGNAL;
                        }
                    }
                }

                if (guard)
                {
                  Atomic_63:
                    atomic { // Non-mover
                        assert con[pred] == True;
                        guard := pred.thread != NULL_THREAD;
                    }

                    if (guard)
                    {
                      Atomic_64:
                        atomic { // Non-mover
                            assert con[node] == True;
                            next := node.next;
                        }

                      Atomic_65:
                        atomic { // Non-mover
                            dummy_3 := next != NULL_NODE && next.waitStatus != CANCELLED;
                        }

                      Atomic_147:
                        atomic { // Non-mover
                            assert con[pred] == True;
                            if (dummy_3)
                            {
                                assert true;
                                // call dummy := AQS_compareAndSetNext(pred, predNext, next);
                                dummy := pred.next == predNext;
                                if (dummy)
                                {
                                    pred.next := next;
                                }
                            }
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
                assert con[node] == True;
                node.next := node;
            }
        }
    }
}



procedure {:ispublic false} AQS_parkAndCheckInterrupt(this: NonfairSync) returns (result: bool);
  modifies Thread_interrupted;



implementation AQS_parkAndCheckInterrupt(this: NonfairSync) returns (result: bool)
{
  var currentThread: Thread;
  var fresh_0: Thread;

  Call_69:
    atomic { // Non-mover
        assert true;
        // call currentThread := Thread_currentThread();
        currentThread := Threads[tid];
    }

  Call_70:
    atomic { // Non-mover
        assert true;
        // call LockSupport_park(currentThread);
        assume true;
    }

  Call_71:
    atomic { // Non-mover
        assert true;
        // call result := Thread_interrupted();
        assert true;
        // call currentThread := Thread_currentThread();
        fresh_0 := Threads[tid];

        assert true;
        // call result := Thread_nativeIsInterrupted(currentThread, true);
        result := fresh_0.interrupted == True;
        if (result)
        {
            if (true)
            {
                fresh_0.interrupted := False;
            }
        }
    }
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
            atomic { // Non-mover
                assert true;
                // call p := Node_predecessor(node);
                assert con[node] == True;
                p := node.prev;

                if (p == NULL_NODE)
                {
                    throw NullPointerException;
                }
            }

          Atomic_75:
            atomic { // Non-mover
                guard := p == this.head;
            }

            if (guard)
            {
              Call_76:
                  call dummy := NonfairSync_tryAcquire(this, arg);

                if (dummy)
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

            if (!guard)
            {
              Call_81:
                  call dummy := AQS_shouldParkAfterFailedAcquire(p, node);

                if (dummy)
                {
                  Call_82:
                      call dummy := AQS_parkAndCheckInterrupt(this);

                  Atomic_148:
                    atomic { // Non-mover
                        if (dummy)
                        {
                            interrupted := true;
                        }
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
  modifies con, Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head, NonfairSync_tail, owner;



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
  modifies Node_prev, Node_next, Node_waitStatus;



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
                assert con[pred_dup] == True;
                pred_dup := pred_dup.prev;
            }

          Atomic_93:
            atomic { // Non-mover
                assert con[node] == True;
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
                    assert con[pred_dup] == True;
                    pred_dup := pred_dup.prev;
                }

              Atomic_96:
                atomic { // Non-mover
                    assert con[node] == True;
                    node.prev := pred_dup;
                }

              Atomic_97:
                atomic { // Non-mover
                    guard := pred_dup.waitStatus == CANCELLED;
                }
            }

          Atomic_98:
            atomic { // Non-mover
                assert con[pred_dup] == True;
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
            atomic { // Non-mover
                assert true;
                // call dummy := AQS_compareAndSetWaitStatus(pred, NO_WAIT_STATUS, SIGNAL);
                dummy := pred.waitStatus == NO_WAIT_STATUS;
                if (dummy)
                {
                    pred.waitStatus := SIGNAL;
                }
            }

          Atomic_101:
            atomic { // Non-mover
                result := false;
            }
        }
    }
}



procedure {:ispublic false} AQS_selfInterrupt();
  modifies Thread_interrupted;



implementation AQS_selfInterrupt()
{
  var currentThread: Thread;

  Call_102:
    atomic { // Non-mover
        assert true;
        // call currentThread := Thread_currentThread();
        currentThread := Threads[tid];
    }

  Call_103:
    atomic { // Non-mover
        assert true;
        // call Thread_interrupt(currentThread);
        currentThread.interrupted := True;
    }
}



procedure {:ispublic false} Sync_tryRelease(this: NonfairSync, releases: int) returns (result: bool);
  modifies NonfairSync_exclusiveOwnerThread, NonfairSync_state;



implementation Sync_tryRelease(this: NonfairSync, releases: int) returns (result: bool)
{
  var c: int;
  var currentThread: Thread;
  var ownerThread: Thread;

  Call_108:
    atomic { // Non-mover
        assert true;
        // call c := AQS_getState(this);
        c := this.state;
    }

  Atomic_109:
    atomic { // Non-mover
        c := c - releases;
    }

  Call_110:
    atomic { // Non-mover
        assert true;
        // call currentThread := Thread_currentThread();
        currentThread := Threads[tid];
    }

  Call_111:
    atomic { // Non-mover
        assert true;
        // call ownerThread := AOS_getExclusiveOwnerThread(this);
        ownerThread := this.exclusiveOwnerThread;
    }

  Atomic_149:
    atomic { // Non-mover
        if (currentThread != ownerThread)
        {
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
        atomic { // Non-mover
            assert true;
            // call AOS_setExclusiveOwnerThread(this, NULL_THREAD);
            this.exclusiveOwnerThread := NULL_THREAD;
        }
    }

  Call_116:
    atomic { // Non-mover
        assert true;
        // call AQS_setState(this, c);
        this.state := c;
    }
}



procedure {:ispublic false} Sync_nonfairTryAcquire(this: NonfairSync, acquires: int) returns (result: bool);
  modifies NonfairSync_exclusiveOwnerThread, NonfairSync_state;



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
    atomic { // Non-mover
        assert true;
        // call current := Thread_currentThread();
        current := Threads[tid];
    }

  Call_119:
    atomic { // Non-mover
        assert true;
        // call c := AQS_getState(this);
        c := this.state;
    }

    if (c == 0)
    {
      Call_120:
        atomic { // Non-mover
            assert true;
            // call dummy := AQS_compareAndSetState(this, 0, acquires);
            dummy := this.state == 0;
            if (dummy)
            {
                this.state := acquires;
            }
        }

        if (dummy)
        {
          Call_121:
            atomic { // Non-mover
                assert true;
                // call AOS_setExclusiveOwnerThread(this, current);
                this.exclusiveOwnerThread := current;
            }

          Atomic_122:
            atomic { // Non-mover
                result := true;
            }
        }
    }
    else
    {
      Call_123:
        atomic { // Non-mover
            assert true;
            // call ownerThread := AOS_getExclusiveOwnerThread(this);
            ownerThread := this.exclusiveOwnerThread;
        }

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
                atomic { // Non-mover
                    assert true;
                    // call AQS_setState(this, nextc);
                    this.state := nextc;
                }

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
  modifies NonfairSync_exclusiveOwnerThread, NonfairSync_state, con, Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head, NonfairSync_tail, owner;



implementation NonfairSync_lock(this: NonfairSync)
{
  var dummy: bool;
  var currentThread: Thread;

  Call_129:
    atomic { // Non-mover
        assert true;
        // call dummy := AQS_compareAndSetState(this, 0, 1);
        dummy := this.state == 0;
        if (dummy)
        {
            this.state := 1;
        }
    }

    if (dummy)
    {
      Call_130:
        atomic { // Non-mover
            assert true;
            // call currentThread := Thread_currentThread();
            currentThread := Threads[tid];
        }

      Call_131:
        atomic { // Non-mover
            assert true;
            // call AOS_setExclusiveOwnerThread(this, currentThread);
            this.exclusiveOwnerThread := currentThread;
        }
    }
    else
    {
      Call_132:
          call AQS_acquire(this, 1);
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
  modifies con, Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head, NonfairSync_tail, owner;



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

var con: [Node]boolean;

var owner: [Node]int;

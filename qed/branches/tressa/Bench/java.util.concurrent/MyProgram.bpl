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
  Atomic_10:
    atomic { // Non-mover
        this.exclusiveOwnerThread := t;
    }
}



procedure {:ispublic false} AOS_getExclusiveOwnerThread(this: NonfairSync) returns (result: Thread);



implementation AOS_getExclusiveOwnerThread(this: NonfairSync) returns (result: Thread)
{
  Atomic_11:
    atomic { // Non-mover
        result := this.exclusiveOwnerThread;
    }
}



procedure {:ispublic false} AQS_getState(this: NonfairSync) returns (result: int);



implementation AQS_getState(this: NonfairSync) returns (result: int)
{
  Atomic_12:
    atomic { // Non-mover
        result := this.state;
    }
}



procedure {:ispublic false} AQS_setState(this: NonfairSync, newState: int);
  modifies NonfairSync_state;



implementation AQS_setState(this: NonfairSync, newState: int)
{
  Atomic_13:
    atomic { // Non-mover
        this.state := newState;
    }
}



procedure {:ispublic false} AQS_enq(this: NonfairSync, node: Node) returns (result: Node);
  modifies Node_alloc, Node_next, Node_prev, NonfairSync_tail, NonfairSync_head, Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head, Node_nextWaiter, Node_thread, Node_waitStatus;



implementation AQS_enq(this: NonfairSync, node: Node) returns (result: Node)
{
  var t: Node;
  var h: Node;
  var dummy: bool;

    while (true)
    {
        if (*)
        {
          Atomic_14:
            atomic { // Non-mover
                havoc t;

                h := New Node;

                assert true;
                // call Node_Node(h);
                h.prev := NULL_NODE;
                h.next := NULL_NODE;
                h.nextWaiter := NULL_NODE;
                h.thread := NULL_THREAD;
                h.waitStatus := NO_WAIT_STATUS;
            }

          Atomic_17:
            atomic { // Non-mover
                assert h.alloc == Alloc;
                h.next := node;
            }

          Atomic_18:
            atomic { // Non-mover
                assert node.alloc == Alloc;
                node.prev := h;
            }

          Call_19:
            atomic { // Non-mover
                assert true;
                // call dummy := AQS_compareAndSetHead(this, h);
                dummy := this.head == NULL_NODE;
                if (dummy)
                {
                    this.head := h;
                }
            }

          Atomic_149:
            atomic { // Non-mover
                if (dummy)
                {
                    this.tail := node;

                    result := h;

                    return;
                }
            }
        }
        else
        {
          Atomic_14_else:
            atomic { // Non-mover
                t := this.tail;

                assume t != NULL_NODE;
            }

          Atomic_23:
            atomic { // Non-mover
                assert node.alloc == Alloc;
                node.prev := t;
            }

          Call_24:
            atomic { // Non-mover
                assert true;
                // call dummy := AQS_compareAndSetTail(this, t, node);
                dummy := this.tail == t;
                if (dummy)
                {
                    this.tail := node;
                }
            }

          Atomic_150:
            atomic { // Non-mover
                assert t.alloc == Alloc;
                if (dummy)
                {
                    t.next := node;

                    result := t;

                    return;
                }
            }
        }
    }
}



procedure {:ispublic false} AQS_setHead(this: NonfairSync, node: Node);
  modifies NonfairSync_head, Node_thread, Node_prev;



implementation AQS_setHead(this: NonfairSync, node: Node)
{
  Atomic_28:
    atomic { // Non-mover
        this.head := node;
    }

  Atomic_29:
    atomic { // Non-mover
        node.thread := NULL_THREAD;
    }

  Atomic_30:
    atomic { // Non-mover
        node.prev := NULL_NODE;
    }
}



procedure {:ispublic false} AQS_addWaiter(this: NonfairSync, mode: Node) returns (result: Node);
  modifies Node_alloc, Node_prev, Node_next, NonfairSync_tail, NonfairSync_head, Node_nextWaiter, Node_thread, Node_waitStatus;



implementation AQS_addWaiter(this: NonfairSync, mode: Node) returns (result: Node)
{
  var node: Node;
  var pred: Node;
  var currentThread: Thread;
  var dummyNode: Node;
  var dummy: bool;
  var done: bool;

  Atomic_31:
    atomic { // Non-mover
        done := false;
    }

  Call_32:
      call currentThread := Thread_currentThread();

  Atomic_33:
    atomic { // Non-mover
        node := New Node;
    }

  Atomic_34:
    atomic { // Non-mover
        assume node != NULL_NODE;
    }

  Call_35:
    atomic { // Non-mover
        assert node.alloc == Alloc;
        assert true;
        // call Node_Node_2(node, currentThread, mode);
        node.nextWaiter := mode;
        node.thread := currentThread;
        node.next := NULL_NODE;
        node.prev := NULL_NODE;
        node.waitStatus := NO_WAIT_STATUS;
    }

  Atomic_36:
    atomic { // Non-mover
        pred := this.tail;
    }

    if (pred != NULL_NODE)
    {
      Atomic_37:
        atomic { // Non-mover
            assert node.alloc == Alloc;
            node.prev := pred;
        }

      Call_38:
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
          Atomic_39:
            atomic { // Non-mover
                assert pred.alloc == Alloc;
                pred.next := node;
            }

          Atomic_40:
            atomic { // Non-mover
                result := node;
            }

          Atomic_41:
            atomic { // Non-mover
                done := true;
            }
        }
    }

    if (!done)
    {
      Call_42:
          call dummyNode := AQS_enq(this, node);

      Atomic_43:
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

  Call_44:
      call dummy := AQS_compareAndSetWaitStatus(node, SIGNAL, NO_WAIT_STATUS);

  Atomic_45:
    atomic { // Non-mover
        assert node.alloc == Alloc;
        s := node.next;
    }

  Atomic_46:
    atomic { // Non-mover
        assert s != NULL_NODE ==> s.alloc == Alloc;
        dummy := s == NULL_NODE || s.waitStatus == CANCELLED;
    }

    if (dummy)
    {
      Atomic_47:
        atomic { // Non-mover
            s := NULL_NODE;
        }

      Atomic_48:
        atomic { // Non-mover
            t := this.tail;
        }

      Atomic_49:
        atomic { // Non-mover
            guard := t != NULL_NODE && t != node;
        }

        while (guard)
        {
          Atomic_50:
            atomic { // Non-mover
                assert t.alloc == Alloc;
                dummy_2 := t.waitStatus != CANCELLED;
            }

            if (dummy_2)
            {
              Atomic_51:
                atomic { // Non-mover
                    s := t;
                }
            }

          Atomic_52:
            atomic { // Non-mover
                assert t.alloc == Alloc;
                t := t.prev;
            }

          Atomic_53:
            atomic { // Non-mover
                guard := t != NULL_NODE && t != node;
            }
        }
    }

    if (s != NULL_NODE)
    {
      Call_54:
          call LockSupport_unpark(s.thread);
    }
}



procedure AQS_release(this: NonfairSync, arg: int) returns (result: bool);



implementation AQS_release(this: NonfairSync, arg: int) returns (result: bool)
{
  var h: Node;
  var dummy: bool;

  Call_55:
      call result := Sync_tryRelease(this, arg);

    if (result)
    {
      Atomic_56:
        atomic { // Non-mover
            h := this.head;
        }

      Atomic_57:
        atomic { // Non-mover
            assert h != NULL_NODE ==> h.alloc == Alloc;
            dummy := h != NULL_NODE && h.waitStatus != NO_WAIT_STATUS;
        }

        if (dummy)
        {
          Call_58:
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
      Atomic_59:
        atomic { // Non-mover
            node.thread := NULL_THREAD;
        }

      Atomic_60:
        atomic { // Non-mover
            assert node.alloc == Alloc;
            pred := node.prev;
        }

      Atomic_61:
        atomic { // Non-mover
            assert pred.alloc == Alloc;
            dummy_2 := pred.waitStatus == CANCELLED;
        }

        while (dummy_2)
        {
          Atomic_62:
            atomic { // Non-mover
                assert pred.alloc == Alloc;
                pred := pred.prev;
            }

          Atomic_63:
            atomic { // Non-mover
                assert node.alloc == Alloc;
                node.prev := pred;
            }

          Atomic_64:
            atomic { // Non-mover
                assert pred.alloc == Alloc;
                dummy_2 := pred.waitStatus == CANCELLED;
            }
        }

      Atomic_65:
        atomic { // Non-mover
            assert pred.alloc == Alloc;
            predNext := pred.next;
        }

      Atomic_66:
        atomic { // Non-mover
            assert node.alloc == Alloc;
            node.waitStatus := CANCELLED;
        }

      Atomic_67:
        atomic { // Non-mover
            guard := node == this.tail;
        }

        if (guard)
        {
          Call_68:
            atomic { // Non-mover
                assert true;
                // call guard := AQS_compareAndSetTail(this, node, pred);
                guard := this.tail == node;
                if (guard)
                {
                    this.tail := pred;
                }
            }

            if (guard)
            {
              Call_69:
                  call dummy := AQS_compareAndSetNext(pred, predNext, NULL_NODE);
            }
        }

        if (!guard)
        {
          Atomic_70:
            atomic { // Non-mover
                guard := pred != this.head;
            }

            if (guard)
            {
              Atomic_71:
                atomic { // Non-mover
                    assert pred.alloc == Alloc;
                    guard := pred.waitStatus == SIGNAL;
                }

                if (!guard)
                {
                  Call_72:
                      call guard := AQS_compareAndSetWaitStatus(pred, NO_WAIT_STATUS, SIGNAL);
                }

                if (guard)
                {
                  Atomic_73:
                    atomic { // Non-mover
                        assert pred.alloc == Alloc;
                        guard := pred.thread != NULL_THREAD;
                    }

                    if (guard)
                    {
                      Atomic_74:
                        atomic { // Non-mover
                            assert node.alloc == Alloc;
                            next := node.next;
                        }

                      Atomic_75:
                        atomic { // Non-mover
                            assert next.alloc == Alloc;
                            assert node.alloc == Alloc;
                            dummy_3 := next != NULL_NODE && next.waitStatus != CANCELLED;
                        }

                        if (dummy_3)
                        {
                          Call_76:
                              call dummy := AQS_compareAndSetNext(pred, predNext, next);
                        }
                    }
                }
            }

            if (!guard)
            {
              Call_77:
                  call AQS_unparkSuccessor(this, node);
            }

          Atomic_78:
            atomic { // Non-mover
                assert node.alloc == Alloc;
                node.next := node;
            }
        }
    }
}



procedure {:ispublic false} AQS_parkAndCheckInterrupt(this: NonfairSync) returns (result: bool);



implementation AQS_parkAndCheckInterrupt(this: NonfairSync) returns (result: bool)
{
  var currentThread: Thread;

  Call_79:
      call currentThread := Thread_currentThread();

  Call_80:
      call LockSupport_park(currentThread);

  Call_81:
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

  Try_82:
    try {
      Atomic_83:
        atomic { // Non-mover
            interrupted := false;
        }

        while (true)
        {
          Call_84:
            atomic { // Non-mover
                assert node.alloc == Alloc;
                assert true;
                // call p := Node_predecessor(node);
                p := node.prev;

                if (p == NULL_NODE)
                {
                    throw NullPointerException;
                }
            }

          Atomic_85:
            atomic { // Non-mover
                guard := p == this.head;
            }

            if (guard)
            {
              Call_86:
                  call guard := NonfairSync_tryAcquire(this, arg);

                if (guard)
                {
                  Call_87:
                      call AQS_setHead(this, node);

                  Atomic_88:
                    atomic { // Non-mover
                        p.next := NULL_NODE;
                    }

                  Atomic_89:
                    atomic { // Non-mover
                        result := interrupted;
                    }

                  Atomic_90:
                    atomic { // Non-mover
                        return;
                    }
                }
            }

          Call_91:
              call dummy := AQS_shouldParkAfterFailedAcquire(p, node);

            if (dummy)
            {
              Call_92:
                  call dummy := AQS_parkAndCheckInterrupt(this);

                if (dummy)
                {
                  Atomic_93:
                    atomic { // Non-mover
                        interrupted := true;
                    }
                }
            }
        }
}
    catch (RuntimeException){
      Call_94:
          call AQS_cancelAcquire(this, node);
    }
}



procedure {:ispublic true} AQS_acquire(this: NonfairSync, arg: int);
  modifies NonfairSync_head, Node_nextWaiter, Node_thread, Node_waitStatus;



implementation AQS_acquire(this: NonfairSync, arg: int)
{
  var guard: bool;
  var dummyNode: Node;

  Call_95:
      call guard := NonfairSync_tryAcquire(this, arg);

    if (!guard)
    {
      Call_96:
          call dummyNode := AQS_addWaiter(this, NULL_NODE);

      Call_97:
          call guard := AQS_acquireQueued(this, dummyNode, arg);

        if (guard)
        {
          Call_98:
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

  Atomic_99:
    atomic { // Non-mover
        assert pred.alloc == Alloc;
        s := pred.waitStatus;
    }

    if (s == SIGNAL || s == CONDITION)
    {
      Atomic_100:
        atomic { // Non-mover
            result := true;
        }
    }
    else
    {
        if (s == CANCELLED)
        {
          Atomic_101:
            atomic { // Non-mover
                pred_dup := pred;
            }

          Atomic_102:
            atomic { // Non-mover
                pred_dup := pred_dup.prev;
            }

          Atomic_103:
            atomic { // Non-mover
                node.prev := pred_dup;
            }

          Atomic_104:
            atomic { // Non-mover
                guard := pred_dup.waitStatus == CANCELLED;
            }

            while (guard)
            {
              Atomic_105:
                atomic { // Non-mover
                    pred_dup := pred_dup.prev;
                }

              Atomic_106:
                atomic { // Non-mover
                    node.prev := pred_dup;
                }

              Atomic_107:
                atomic { // Non-mover
                    guard := pred_dup.waitStatus == CANCELLED;
                }
            }

          Atomic_108:
            atomic { // Non-mover
                pred_dup.next := node;
            }

          Atomic_109:
            atomic { // Non-mover
                result := false;
            }
        }
        else
        {
          Call_110:
              call dummy := AQS_compareAndSetWaitStatus(pred, NO_WAIT_STATUS, SIGNAL);

          Atomic_111:
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

  Call_112:
      call currentThread := Thread_currentThread();

  Call_113:
      call Thread_interrupt(currentThread);
}



procedure {:ispublic false} {:isatomic true} AQS_compareAndSetState(this: NonfairSync, expect: int, update: int) returns (result: bool);
  modifies NonfairSync_state;



implementation AQS_compareAndSetState(this: NonfairSync, expect: int, update: int) returns (result: bool)
{
  Atomic_114:
    atomic { // Non-mover
        result := this.state == expect;
        if (result)
        {
            this.state := update;
        }
    }
}



procedure {:ispublic false} {:isatomic true} AQS_compareAndSetWaitStatus(node: Node, expect: NodeWaitStatus, update: NodeWaitStatus) returns (result: bool);
  modifies Node_waitStatus;



implementation AQS_compareAndSetWaitStatus(node: Node, expect: NodeWaitStatus, update: NodeWaitStatus) returns (result: bool)
{
  Atomic_117:
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
  Atomic_118:
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

  Call_119:
      call c := AQS_getState(this);

  Atomic_120:
    atomic { // Non-mover
        c := c - releases;
    }

  Call_121:
      call currentThread := Thread_currentThread();

  Call_122:
      call ownerThread := AOS_getExclusiveOwnerThread(this);

    if (currentThread != ownerThread)
    {
      Atomic_123:
        atomic { // Non-mover
            throw IllegalMonitorStateException;
        }
    }

  Atomic_124:
    atomic { // Non-mover
        result := false;
    }

    if (c == 0)
    {
      Atomic_125:
        atomic { // Non-mover
            result := true;
        }

      Call_126:
          call AOS_setExclusiveOwnerThread(this, NULL_THREAD);
    }

  Call_127:
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

  Atomic_128:
    atomic { // Non-mover
        result := false;
    }

  Call_129:
      call current := Thread_currentThread();

  Call_130:
      call c := AQS_getState(this);

    if (c == 0)
    {
      Call_131:
          call dummy := AQS_compareAndSetState(this, 0, acquires);

        if (dummy)
        {
          Call_132:
              call AOS_setExclusiveOwnerThread(this, current);

          Atomic_133:
            atomic { // Non-mover
                result := true;
            }
        }
    }
    else
    {
      Call_134:
          call ownerThread := AOS_getExclusiveOwnerThread(this);

        if (current == ownerThread)
        {
          Atomic_135:
            atomic { // Non-mover
                nextc := c + acquires;
            }

            if (nextc < 0)
            {
              Atomic_136:
                atomic { // Non-mover
                    throw Error;
                }
            }
            else
            {
              Call_137:
                  call AQS_setState(this, nextc);

              Atomic_138:
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
  Call_139:
      call result := Sync_nonfairTryAcquire(this, acquires);
}



procedure {:ispublic false} NonfairSync_lock(this: NonfairSync);
  modifies NonfairSync_head, Node_nextWaiter, Node_thread, Node_waitStatus;



implementation NonfairSync_lock(this: NonfairSync)
{
  var dummy: bool;
  var currentThread: Thread;

  Call_140:
      call dummy := AQS_compareAndSetState(this, 0, 1);

    if (dummy)
    {
      Call_141:
          call currentThread := Thread_currentThread();

      Call_142:
          call AOS_setExclusiveOwnerThread(this, currentThread);
    }
    else
    {
      Call_143:
          call AQS_acquire(this, 1);
    }
}



procedure {:ispublic false} {:isatomic true} LockSupport_park(thread: Thread);



implementation LockSupport_park(thread: Thread)
{
  Atomic_144:
    atomic { // Non-mover
        assume true;
    }
}



procedure {:ispublic false} {:isatomic true} LockSupport_unpark(thread: Thread);



implementation LockSupport_unpark(thread: Thread)
{
  Atomic_145:
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

  Call_146:
      call dummy := AQS_release(this.sync, 1);
}



procedure ReentrantLock_lock(this: ReentrantLock);
  modifies NonfairSync_head, Node_nextWaiter, Node_thread, Node_waitStatus;



implementation ReentrantLock_lock(this: ReentrantLock)
{
  Call_147:
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


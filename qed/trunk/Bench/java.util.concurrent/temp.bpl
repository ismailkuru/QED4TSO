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
        assert node.alloc == Alloc;
        assert con[node] == True;
        node.thread := NULL_THREAD;
    }

  Atomic_20:
    atomic { // Non-mover
        node.prev := NULL_NODE;
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
        // assert true; [Discharged]
        // call dummy := AQS_compareAndSetWaitStatus(node, SIGNAL, NO_WAIT_STATUS);
        dummy := node.waitStatus == SIGNAL;
        if (dummy)
        {
            node.waitStatus := NO_WAIT_STATUS;
        }
    }

  Atomic_35:
    atomic { // Non-mover
        assert node.alloc == Alloc;
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

            if (dummy_2)
            {
              Atomic_41:
                atomic { // Non-mover
                    s := t;
                }
            }

          Atomic_42:
            atomic { // Non-mover
                assert t.alloc == Alloc;
                assert con[t] == True;
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
        atomic { // Non-mover
            // assert true; [Discharged]
            // call LockSupport_unpark(s.thread);
            assume true;
        }
    }
}



procedure AQS_release(this: NonfairSync, arg: int) returns (result: bool);
  modifies NonfairSync_exclusiveOwnerThread, NonfairSync_state, lockedBy;



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
            assert node.alloc == Alloc;
            assert con[node] == True;
            node.thread := NULL_THREAD;
        }

      Atomic_50:
        atomic { // Non-mover
            assert node.alloc == Alloc;
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
                assert pred.alloc == Alloc;
                assert con[pred] == True;
                pred := pred.prev;
            }

          Atomic_53:
            atomic { // Non-mover
                assert node.alloc == Alloc;
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
            assert pred.alloc == Alloc;
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
                // assert true; [Discharged]
                // call guard := AQS_compareAndSetTail(this, node, pred);
                guard := this.tail == node;
                if (guard)
                {
                    this.tail := pred;
                }
            }

            if (guard)
            {
              Call_59:
                atomic { // Non-mover
                    assert pred.alloc == Alloc;
                    assert con[pred] == True;
                    // assert true; [Discharged]
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

                if (!guard)
                {
                  Call_62:
                    atomic { // Non-mover
                        // assert true; [Discharged]
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
                        assert pred.alloc == Alloc;
                        assert con[pred] == True;
                        guard := pred.thread != NULL_THREAD;
                    }

                    if (guard)
                    {
                      Atomic_64:
                        atomic { // Non-mover
                            assert node.alloc == Alloc;
                            assert con[node] == True;
                            next := node.next;
                        }

                      Atomic_65:
                        atomic { // Non-mover
                            dummy_3 := next != NULL_NODE && next.waitStatus != CANCELLED;
                        }

                        if (dummy_3)
                        {
                          Call_66:
                            atomic { // Non-mover
                                assert pred.alloc == Alloc;
                                assert con[pred] == True;
                                // assert true; [Discharged]
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
                assert node.alloc == Alloc;
                assert con[node] == True;
                node.next := node;
            }
        }
    }
}



procedure {:ispublic false} AQS_acquireQueued(this: NonfairSync, node: Node, arg: int) returns (result: bool);
  modifies Node_next, NonfairSync_state, lockedBy, NonfairSync_exclusiveOwnerThread, Thread_interrupted;



implementation AQS_acquireQueued(this: NonfairSync, node: Node, arg: int) returns (result: bool)
{
  var interrupted: bool;
  var p: Node;
  var guard: bool;
  var dummy: bool;
  var fresh_0: Thread;
  var fresh_1: Thread;

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
                assert node.alloc == Alloc;
                // assert true; [Discharged]
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
                atomic { // Non-mover
                    assert true;
                    // call dummy := AQS_parkAndCheckInterrupt(this);
                    // assert true; [Discharged]
                    // call currentThread := Thread_currentThread();
                    fresh_0 := Threads[tid];

                    // assert true; [Discharged]
                    // call LockSupport_park(currentThread);
                    assume true;

                    // assert true; [Discharged]
                    // call result := Thread_interrupted();
                    // assert true; [Discharged]
                    // call currentThread := Thread_currentThread();
                    fresh_1 := Threads[tid];

                    // assert true; [Discharged]
                    // call result := Thread_nativeIsInterrupted(currentThread, true);
                    dummy := fresh_1.interrupted == True;
                    if (dummy)
                    {
                        if (true)
                        {
                            fresh_1.interrupted := False;
                        }
                    }
                }

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
  modifies con, Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head, NonfairSync_tail, owner, Thread_interrupted, NonfairSync_state, lockedBy, NonfairSync_exclusiveOwnerThread;



implementation AQS_acquire(this: NonfairSync, arg: int)
{
  var guard: bool;
  var dummyNode: Node;
  var fresh_0: Thread;
  var fresh_1: Node;
  var fresh_2: bool;
  var fresh_3: Thread;
  var fresh_4: Node;
  var fresh_5: [NonfairSync]Node;
  var fresh_6: Node;
  var fresh_7: bool;
  var fresh_8: Node;
  var fresh_9: Node;

  Call_85:
      call guard := NonfairSync_tryAcquire(this, arg);

    if (!guard)
    {
      Call_86:
        atomic { // Non-mover
            assert true;
            // call dummyNode := AQS_addWaiter(this, NULL_NODE);
            havoc fresh_1;
            fresh_2 := false;
            havoc fresh_3;
            fresh_4 := New Node;
            owner[fresh_4] := tid;
            assume fresh_4 != NULL_NODE;
            fresh_4.nextWaiter := NULL_NODE;
            fresh_4.thread := Threads[tid];
            fresh_4.next := NULL_NODE;
            fresh_4.prev := NULL_NODE;
            fresh_4.waitStatus := NO_WAIT_STATUS;
            con[fresh_4] := True;
            havoc fresh_5;
            fresh_6 := fresh_5[this];
            fresh_4.prev := fresh_6;
            havoc fresh_7;
            if (this.tail == fresh_6 && this.tail != NULL_NODE)
            {
                this.tail := fresh_4;
                assert fresh_6.alloc == Alloc;
                assert con[fresh_6] == True;
                fresh_6.next := fresh_4;
                dummyNode := fresh_4;
                fresh_2 := true;
            }

            if (!fresh_2)
            {
                havoc fresh_8;
                if (this.tail == NULL_NODE)
                {
                    fresh_9 := New Node;
                    owner[fresh_9] := tid;
                    assume fresh_9 != NULL_NODE;
                    fresh_9.prev := NULL_NODE;
                    fresh_9.nextWaiter := NULL_NODE;
                    fresh_9.thread := NULL_THREAD;
                    fresh_9.waitStatus := NO_WAIT_STATUS;
                    con[fresh_9] := True;
                    fresh_9.next := fresh_4;
                    fresh_4.prev := fresh_9;
                    this.head := fresh_9;
                    this.tail := fresh_4;
                }
                else
                {
                    assert this.tail.alloc == Alloc;
                    assert con[this.tail] == True;
                    fresh_4.prev := this.tail;
                    this.tail := fresh_4;
                    fresh_4.prev.next := fresh_4;
                }

                dummyNode := fresh_4;
            }
        }

      Call_87:
          call guard := AQS_acquireQueued(this, dummyNode, arg);

        if (guard)
        {
          Call_88:
            atomic { // Non-mover
                // assert true; [Discharged]
                // call AQS_selfInterrupt();
                // assert true; [Discharged]
                // call currentThread := Thread_currentThread();
                fresh_0 := Threads[tid];

                // assert true; [Discharged]
                // call Thread_interrupt(currentThread);
                fresh_0.interrupted := True;
            }
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
                assert pred_dup.alloc == Alloc;
                assert con[pred_dup] == True;
                pred_dup := pred_dup.prev;
            }

          Atomic_93:
            atomic { // Non-mover
                assert node.alloc == Alloc;
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
                    assert pred_dup.alloc == Alloc;
                    assert con[pred_dup] == True;
                    pred_dup := pred_dup.prev;
                }

              Atomic_96:
                atomic { // Non-mover
                    assert node.alloc == Alloc;
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
                assert pred_dup.alloc == Alloc;
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
                // assert true; [Discharged]
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



procedure {:ispublic false} Sync_tryRelease(this: NonfairSync, releases: int) returns (result: bool);
  modifies NonfairSync_state, NonfairSync_exclusiveOwnerThread, lockedBy;



implementation Sync_tryRelease(this: NonfairSync, releases: int) returns (result: bool)
{
  var c: int;
  var currentThread: Thread;
  var ownerThread: Thread;

  Call_108:
    atomic { // Non-mover
        assert releases == 1;
        havoc c;
        havoc currentThread;
        havoc ownerThread;
        if (Threads[tid] != this.exclusiveOwnerThread)
        {
            assert monitorException[this] == True;
            throw IllegalMonitorStateException;
        }

        assert monitorException[this] == False;
        result := false;
        this.state := this.state - 1;
        if (this.state == 0)
        {
            result := true;
            this.exclusiveOwnerThread := NULL_THREAD;
            lockedBy[this] := 0;
        }
    }
}



procedure {:ispublic false} Sync_nonfairTryAcquire(this: NonfairSync, acquires: int) returns (result: bool);
  modifies NonfairSync_state, lockedBy, NonfairSync_exclusiveOwnerThread;



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
        current := Threads[tid];
        if (this.state == 0 || lockedBy[this] == tid)
        {
            c := this.state;
        }
        else
        {
            havoc c;
        }
    }

  Atomic_165:
    atomic { // Non-mover
        assert acquires == 1;
        assert monitorException[this] == False;
        assert current == Threads[tid];
        if (c == 0)
        {
            havoc dummy;
            if (this.state == 0)
            {
                // assert this.exclusiveOwnerThread == NULL_THREAD; [Discharged]
                // assert lockedBy[this] == 0; [Discharged]
                this.state := 1;
                lockedBy[this] := tid;
                this.exclusiveOwnerThread := Threads[tid];
                result := true;
            }
        }
        else
        {
            havoc ownerThread;
            if (Threads[tid] == this.exclusiveOwnerThread)
            {
                assert c == this.state;
                // assert this.state > 0; [Discharged]
                assert lockedBy[this] == tid;
                havoc nextc;
                if (this.state + 1 < 0)
                {
                    throw Error;
                }
                else
                {
                    this.state := this.state + 1;
                    result := true;
                }
            }
        }
    }
}



procedure {:ispublic false} NonfairSync_tryAcquire(this: NonfairSync, acquires: int) returns (result: bool);
  modifies NonfairSync_state, lockedBy, NonfairSync_exclusiveOwnerThread;



implementation NonfairSync_tryAcquire(this: NonfairSync, acquires: int) returns (result: bool)
{
  Call_128:
      call result := Sync_nonfairTryAcquire(this, acquires);
}



procedure {:ispublic false} NonfairSync_lock(this: NonfairSync);
  modifies NonfairSync_state, lockedBy, NonfairSync_exclusiveOwnerThread, con, Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head, NonfairSync_tail, owner;



implementation NonfairSync_lock(this: NonfairSync)
{
  var dummy: bool;
  var currentThread: Thread;

    if (*)
    {
      Call_129:
        atomic { // Non-mover
            assert monitorException[this] == False;
            havoc dummy;
            assume this.state == 0;
            this.state := 1;
            lockedBy[this] := tid;
            havoc currentThread;
            this.exclusiveOwnerThread := Threads[tid];
        }
    }
    else
    {
      Call_129_else:
        atomic { // Non-mover
            assert monitorException[this] == False;
            havoc dummy;
            assume this.state != 0;
        }

      Call_132:
          call AQS_acquire(this, 1);
    }
}



record ReentrantLock {
  sync: NonfairSync;
  alloc: AllocType;
}

procedure ReentrantLock_unlock(this: ReentrantLock);
  modifies NonfairSync_exclusiveOwnerThread, NonfairSync_state, lockedBy;



implementation ReentrantLock_unlock(this: ReentrantLock)
{
  var dummy: bool;

  Call_135:
      call dummy := AQS_release(this.sync, 1);
}



procedure ReentrantLock_lock(this: ReentrantLock);
  modifies con, Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head, NonfairSync_tail, owner, NonfairSync_state, lockedBy, NonfairSync_exclusiveOwnerThread;



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

var lockedBy: [NonfairSync]int;

var monitorException: [NonfairSync]boolean;

invariant (forall queue: NonfairSync :: monitorException[queue] == False && lockedBy[queue] == tid ==> queue.exclusiveOwnerThread == Threads[tid]);

invariant (forall queue: NonfairSync :: lockedBy[queue] == 0 <==> queue.exclusiveOwnerThread == NULL_THREAD);

invariant (forall queue: NonfairSync :: lockedBy[queue] == 0 <==> queue.state == 0);

invariant (forall queue: NonfairSync :: lockedBy[queue] != 0 <==> queue.state > 0);

invariant (forall queue: NonfairSync :: monitorException[queue] == False && queue.exclusiveOwnerThread == Threads[tid] ==> lockedBy[queue] == tid);

invariant (forall queue: NonfairSync :: monitorException[queue] == True ==> lockedBy[queue] != tid);

invariant (forall node: Node :: con[node] == True ==> node.alloc == Alloc);

invariant (forall node: Node :: con[node] == True ==> node != NULL_NODE);

invariant (forall node: Node :: node != NULL_NODE ==> node.alloc == Alloc);

invariant NULL_NODE.alloc == Null && NULL_NODE.next == NULL_NODE && NULL_NODE.prev == NULL_NODE && NULL_NODE.nextWaiter == NULL_NODE && NULL_NODE.thread == NULL_THREAD;

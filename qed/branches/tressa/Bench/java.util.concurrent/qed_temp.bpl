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

invariant (forall i: int :: i >= 0 ==> (Threads[i]).id == i);

invariant (forall i: int :: i <= 0 ==> (Threads[i]) == NULL_THREAD);

procedure {:ispublic false} Thread_interrupted() returns (result: bool);
  modifies Thread_interrupted;



implementation Thread_interrupted() returns (result: bool)
{
  var currentThread: Thread;

  Call_4:
    atomic { // Non-mover
        assert true;
        currentThread := Threads[tid];
    }

  Call_5:
    atomic { // Non-mover
        assert true;
        result := currentThread.interrupted == True;
        if (result)
        {
            if (true)
            {
                currentThread.interrupted := False;
            }
        }
    }
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
  Atomic_7:
    atomic { // Non-mover
        assert this.alloc == Alloc;
        this.nextWaiter := mode;
    }

  Atomic_8:
    atomic { // Non-mover
        assert this.alloc == Alloc;
        this.thread := thread;
    }

  Atomic_9:
    atomic { // Non-mover
        assert this.alloc == Alloc;
        this.next := NULL_NODE;
    }

  Atomic_10:
    atomic { // Non-mover
        assert owner[this] == tid;
        assert this.alloc == Alloc;
        this.prev := NULL_NODE;
    }

  Atomic_11:
    atomic { // Non-mover
        assert this.alloc == Alloc;
        this.waitStatus := NO_WAIT_STATUS;
    }
}



procedure {:ispublic false} Node_predecessor(this: Node) returns (result: Node);



implementation Node_predecessor(this: Node) returns (result: Node)
{
  Atomic_12:
    atomic { // Non-mover
        assert owner[this] == tid;
        assert this.alloc == Alloc;
        result := this.prev;
    }

    if (result == NULL_NODE)
    {
      Atomic_13:
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

procedure {:ispublic false} AQS_enq(this: NonfairSync, node: Node) returns (result: Node);
  modifies Node_alloc, Node_next, Node_prev, NonfairSync_tail, Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head, Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head;



implementation AQS_enq(this: NonfairSync, node: Node) returns (result: Node)
{
  var t: Node;
  var h: Node;
  var dummy: bool;

    while (true)
    {
        if (*)
        {
          Atomic_18:
            atomic { // Non-mover
                //assert owner[this.head] == tid;
                assert owner[node] == tid;
                havoc t;
                assume t == NULL_NODE;
                h := New Node;
                assert true;
                h.prev := NULL_NODE;
                h.next := NULL_NODE;
                h.nextWaiter := NULL_NODE;
                h.thread := NULL_THREAD;
                h.waitStatus := NO_WAIT_STATUS;
                assert h.alloc == Alloc;
                h.next := node;

                assert node.alloc == Alloc;
                node.prev := h;

                assert true;
                dummy := this.head == NULL_NODE;
                if (dummy)
                {
                    this.head := h;
                }
            }

          Atomic_153:
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
          Atomic_18_else:
            atomic { // Right-mover
                t := this.tail;
                assume t != NULL_NODE;

                assert owner[this] == tid;
                assert node.alloc == Alloc;
                node.prev := t;

                assert true;
                dummy := this.tail == t;
                if (dummy)
                {
                    this.tail := node;
                }

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
  Atomic_32:
    atomic { // Non-mover
        this.head := node;
    }

  Atomic_33:
    atomic { // Non-mover
        node.thread := NULL_THREAD;
    }

  Atomic_34:
    atomic { // Non-mover
        assert owner[node] == tid;
        node.prev := NULL_NODE;
    }
}



procedure {:ispublic false} AQS_addWaiter(this: NonfairSync, mode: Node) returns (result: Node);
  modifies Node_alloc, Node_prev, Node_next, NonfairSync_tail, Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head;



implementation AQS_addWaiter(this: NonfairSync, mode: Node) returns (result: Node)
{
  var node: Node;
  var pred: Node;
  var currentThread: Thread;
  var dummyNode: Node;
  var dummy: bool;
  var done: bool;

  Atomic_35:
    atomic { // Non-mover
        done := false;
    }

  Call_36:
    atomic { // Non-mover
        assert true;
        currentThread := Threads[tid];
    }

  Atomic_37:
    atomic { // Non-mover
        node := New Node;
    }

  Atomic_38:
    atomic { // Non-mover
        assume node != NULL_NODE;
    }

  Call_295:
      call Node_Node_2(node, currentThread, mode);

  Atomic_40:
    atomic { // Non-mover
        pred := this.tail;
    }

    if (pred != NULL_NODE)
    {
      Atomic_41:
        atomic { // Non-mover
            assert owner[node] == tid;
            assert node.alloc == Alloc;
            node.prev := pred;
        }

      Call_42:
        atomic { // Non-mover
            assert true;
            dummy := this.tail == pred;
            if (dummy)
            {
                this.tail := node;
            }
        }

        if (dummy)
        {
          Atomic_43:
            atomic { // Non-mover
                assert pred.alloc == Alloc;
                pred.next := node;
            }

          Atomic_44:
            atomic { // Non-mover
                result := node;
            }

          Atomic_45:
            atomic { // Non-mover
                done := true;
            }
        }
    }

    if (!done)
    {
      Call_296:
          call dummyNode := AQS_enq(this, node);

      Atomic_47:
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

  Call_48:
    atomic { // Non-mover
        assert node.alloc == Alloc;
        assert true;
        dummy := node.waitStatus == SIGNAL;
        if (dummy)
        {
            node.waitStatus := NO_WAIT_STATUS;
        }
    }

  Atomic_49:
    atomic { // Non-mover
        assert node.alloc == Alloc;
        s := node.next;
    }

  Atomic_50:
    atomic { // Non-mover
        assert s != NULL_NODE ==> s.alloc == Alloc;
        dummy := s == NULL_NODE || s.waitStatus == CANCELLED;
    }

    if (dummy)
    {
      Atomic_51:
        atomic { // Non-mover
            s := NULL_NODE;
        }

      Atomic_52:
        atomic { // Non-mover
            t := this.tail;
        }

      Atomic_53:
        atomic { // Non-mover
            guard := t != NULL_NODE && t != node;
        }

        while (guard)
        {
          Atomic_54:
            atomic { // Non-mover
                assert t.alloc == Alloc;
                dummy_2 := t.waitStatus != CANCELLED;
            }

            if (dummy_2)
            {
              Atomic_55:
                atomic { // Non-mover
                    s := t;
                }
            }

          Atomic_56:
            atomic { // Non-mover
                assert owner[t] == tid;
                assert t.alloc == Alloc;
                t := t.prev;
            }

          Atomic_57:
            atomic { // Non-mover
                guard := t != NULL_NODE && t != node;
            }
        }
    }

    if (s != NULL_NODE)
    {
      Call_58:
        atomic { // Non-mover
            assert true;
            assume true;
        }
    }
}



procedure AQS_release(this: NonfairSync, arg: int) returns (result: bool);



implementation AQS_release(this: NonfairSync, arg: int) returns (result: bool)
{
  var h: Node;
  var dummy: bool;

  Call_297:
      call result := Sync_tryRelease(this, arg);

    if (result)
    {
      Atomic_60:
        atomic { // Non-mover
            h := this.head;
        }

      Atomic_61:
        atomic { // Non-mover
            assert h != NULL_NODE ==> h.alloc == Alloc;
            dummy := h != NULL_NODE && h.waitStatus != NO_WAIT_STATUS;
        }

        if (dummy)
        {
          Call_298:
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
      Atomic_63:
        atomic { // Non-mover
            node.thread := NULL_THREAD;
        }

      Atomic_64:
        atomic { // Non-mover
            assert owner[node] == tid;
            assert node.alloc == Alloc;
            pred := node.prev;
        }

      Atomic_65:
        atomic { // Non-mover
            assert pred.alloc == Alloc;
            dummy_2 := pred.waitStatus == CANCELLED;
        }

        while (dummy_2)
        {
          Atomic_66:
            atomic { // Non-mover
                assert owner[pred] == tid;
                assert pred.alloc == Alloc;
                pred := pred.prev;
            }

          Atomic_67:
            atomic { // Non-mover
                assert owner[node] == tid;
                assert node.alloc == Alloc;
                node.prev := pred;
            }

          Atomic_68:
            atomic { // Non-mover
                assert pred.alloc == Alloc;
                dummy_2 := pred.waitStatus == CANCELLED;
            }
        }

      Atomic_69:
        atomic { // Non-mover
            assert pred.alloc == Alloc;
            predNext := pred.next;
        }

      Atomic_70:
        atomic { // Non-mover
            assert node.alloc == Alloc;
            node.waitStatus := CANCELLED;
        }

      Atomic_71:
        atomic { // Non-mover
            guard := node == this.tail;
        }

        if (guard)
        {
          Call_72:
            atomic { // Non-mover
                assert true;
                guard := this.tail == node;
                if (guard)
                {
                    this.tail := pred;
                }
            }

            if (guard)
            {
              Call_73:
                atomic { // Non-mover
                    assert pred.alloc == Alloc;
                    assert true;
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
          Atomic_74:
            atomic { // Non-mover
                guard := pred != this.head;
            }

            if (guard)
            {
              Atomic_75:
                atomic { // Non-mover
                    assert pred.alloc == Alloc;
                    guard := pred.waitStatus == SIGNAL;
                }

                if (!guard)
                {
                  Call_76:
                    atomic { // Non-mover
                        assert pred.alloc == Alloc;
                        assert true;
                        guard := pred.waitStatus == NO_WAIT_STATUS;
                        if (guard)
                        {
                            pred.waitStatus := SIGNAL;
                        }
                    }
                }

                if (guard)
                {
                  Atomic_77:
                    atomic { // Non-mover
                        assert pred.alloc == Alloc;
                        guard := pred.thread != NULL_THREAD;
                    }

                    if (guard)
                    {
                      Atomic_78:
                        atomic { // Non-mover
                            assert node.alloc == Alloc;
                            next := node.next;
                        }

                      Atomic_79:
                        atomic { // Non-mover
                            assert next != NULL_NODE ==> next.alloc == Alloc;
                            dummy_3 := next != NULL_NODE && next.waitStatus != CANCELLED;
                        }

                        if (dummy_3)
                        {
                          Call_80:
                            atomic { // Non-mover
                                assert pred.alloc == Alloc;
                                assert true;
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
              Call_299:
                  call AQS_unparkSuccessor(this, node);
            }

          Atomic_82:
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

  Call_83:
    atomic { // Non-mover
        assert true;
        currentThread := Threads[tid];
    }

  Call_84:
    atomic { // Non-mover
        assert true;
        assume true;
    }

  Call_300:
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

  Try_86:
    try {
      Atomic_87:
        atomic { // Non-mover
            interrupted := false;
        }

        while (true)
        {
          Call_301:
              call p := Node_predecessor(node);

          Atomic_89:
            atomic { // Non-mover
                guard := p == this.head;
            }

            if (guard)
            {
              Call_302:
                  call guard := NonfairSync_tryAcquire(this, arg);

                if (guard)
                {
                  Call_303:
                      call AQS_setHead(this, node);

                  Atomic_92:
                    atomic { // Non-mover
                        assert p.alloc == Alloc;
                        p.next := NULL_NODE;
                    }

                  Atomic_93:
                    atomic { // Non-mover
                        result := interrupted;
                    }

                  Atomic_94:
                    atomic { // Non-mover
                        return;
                    }
                }
            }

          Call_304:
              call dummy := AQS_shouldParkAfterFailedAcquire(p, node);

            if (dummy)
            {
              Call_305:
                  call dummy := AQS_parkAndCheckInterrupt(this);

                if (dummy)
                {
                  Atomic_97:
                    atomic { // Non-mover
                        interrupted := true;
                    }
                }
            }
        }
}
    catch (RuntimeException){
      Call_306:
          call AQS_cancelAcquire(this, node);
    }
}



procedure {:ispublic true} AQS_acquire(this: NonfairSync, arg: int);
  modifies Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head;



implementation AQS_acquire(this: NonfairSync, arg: int)
{
  var guard: bool;
  var dummyNode: Node;

  Call_307:
      call guard := NonfairSync_tryAcquire(this, arg);

    if (!guard)
    {
      Call_308:
          call dummyNode := AQS_addWaiter(this, NULL_NODE);

      Call_309:
          call guard := AQS_acquireQueued(this, dummyNode, arg);

        if (guard)
        {
          Call_310:
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

  Atomic_103:
    atomic { // Non-mover
        assert pred.alloc == Alloc;
        s := pred.waitStatus;
    }

    if (s == SIGNAL || s == CONDITION)
    {
      Atomic_104:
        atomic { // Non-mover
            result := true;
        }
    }
    else
    {
        if (s == CANCELLED)
        {
          Atomic_105:
            atomic { // Non-mover
                pred_dup := pred;
            }

          Atomic_106:
            atomic { // Non-mover
                assert owner[pred_dup] == tid;
                assert pred_dup.alloc == Alloc;
                pred_dup := pred_dup.prev;
            }

          Atomic_107:
            atomic { // Non-mover
                assert owner[node] == tid;
                assert node.alloc == Alloc;
                node.prev := pred_dup;
            }

          Atomic_108:
            atomic { // Non-mover
                assert pred_dup.alloc == Alloc;
                guard := pred_dup.waitStatus == CANCELLED;
            }

            while (guard)
            {
              Atomic_109:
                atomic { // Non-mover
                    assert owner[pred_dup] == tid;
                    assert pred_dup.alloc == Alloc;
                    pred_dup := pred_dup.prev;
                }

              Atomic_110:
                atomic { // Non-mover
                    assert owner[node] == tid;
                    assert node.alloc == Alloc;
                    node.prev := pred_dup;
                }

              Atomic_111:
                atomic { // Non-mover
                    assert pred_dup.alloc == Alloc;
                    guard := pred_dup.waitStatus == CANCELLED;
                }
            }

          Atomic_112:
            atomic { // Non-mover
                assert pred_dup.alloc == Alloc;
                pred_dup.next := node;
            }

          Atomic_113:
            atomic { // Non-mover
                result := false;
            }
        }
        else
        {
          Call_114:
            atomic { // Non-mover
                assert pred.alloc == Alloc;
                assert true;
                dummy := pred.waitStatus == NO_WAIT_STATUS;
                if (dummy)
                {
                    pred.waitStatus := SIGNAL;
                }
            }

          Atomic_115:
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

  Call_116:
    atomic { // Non-mover
        assert true;
        currentThread := Threads[tid];
    }

  Call_117:
    atomic { // Non-mover
        assert true;
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

  Call_123:
    atomic { // Non-mover
        assert true;
        c := this.state;
    }

  Atomic_124:
    atomic { // Non-mover
        c := c - releases;
    }

  Call_125:
    atomic { // Non-mover
        assert true;
        currentThread := Threads[tid];
    }

  Call_126:
    atomic { // Non-mover
        assert true;
        ownerThread := this.exclusiveOwnerThread;
    }

    if (currentThread != ownerThread)
    {
      Atomic_127:
        atomic { // Non-mover
            throw IllegalMonitorStateException;
        }
    }

  Atomic_128:
    atomic { // Non-mover
        result := false;
    }

    if (c == 0)
    {
      Atomic_129:
        atomic { // Non-mover
            result := true;
        }

      Call_130:
        atomic { // Non-mover
            assert true;
            this.exclusiveOwnerThread := NULL_THREAD;
        }
    }

  Call_131:
    atomic { // Non-mover
        assert true;
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

  Atomic_132:
    atomic { // Non-mover
        result := false;
    }

  Call_133:
    atomic { // Non-mover
        assert true;
        current := Threads[tid];
    }

  Call_134:
    atomic { // Non-mover
        assert true;
        c := this.state;
    }

    if (c == 0)
    {
      Call_135:
        atomic { // Non-mover
            assert true;
            dummy := this.state == 0;
            if (dummy)
            {
                this.state := acquires;
            }
        }

        if (dummy)
        {
          Call_136:
            atomic { // Non-mover
                assert true;
                this.exclusiveOwnerThread := current;
            }

          Atomic_137:
            atomic { // Non-mover
                result := true;
            }
        }
    }
    else
    {
      Call_138:
        atomic { // Non-mover
            assert true;
            ownerThread := this.exclusiveOwnerThread;
        }

        if (current == ownerThread)
        {
          Atomic_139:
            atomic { // Non-mover
                nextc := c + acquires;
            }

            if (nextc < 0)
            {
              Atomic_140:
                atomic { // Non-mover
                    throw Error;
                }
            }
            else
            {
              Call_141:
                atomic { // Non-mover
                    assert true;
                    this.state := nextc;
                }

              Atomic_142:
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
  Call_311:
      call result := Sync_nonfairTryAcquire(this, acquires);
}



procedure {:ispublic false} NonfairSync_lock(this: NonfairSync);
  modifies NonfairSync_exclusiveOwnerThread, NonfairSync_state, Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head;



implementation NonfairSync_lock(this: NonfairSync)
{
  var dummy: bool;
  var currentThread: Thread;

  Call_144:
    atomic { // Non-mover
        assert true;
        dummy := this.state == 0;
        if (dummy)
        {
            this.state := 1;
        }
    }

    if (dummy)
    {
      Call_145:
        atomic { // Non-mover
            assert true;
            currentThread := Threads[tid];
        }

      Call_146:
        atomic { // Non-mover
            assert true;
            this.exclusiveOwnerThread := currentThread;
        }
    }
    else
    {
      Call_312:
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

  Call_313:
      call dummy := AQS_release(this.sync, 1);
}



procedure ReentrantLock_lock(this: ReentrantLock);
  modifies Node_nextWaiter, Node_thread, Node_waitStatus, NonfairSync_head;



implementation ReentrantLock_lock(this: ReentrantLock)
{
  Call_314:
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

var owner: [Node]int;


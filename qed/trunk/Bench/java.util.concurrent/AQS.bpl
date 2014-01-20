
/* ================================================================================================Node ================================================================================================*/

record Node
{
	waitStatus: int;
	prev: Node;
	next: Node;
	nextWaiter: Node;
	thread: Thread;
}

// NULL_NODE
const NULL_NODE: Node;
invariant (IsNull(NULL_NODE.alloc));
invariant (NULL_NODE.next == NULL_NODE && NULL_NODE.prev == NULL_NODE);
  
const CANCELLED: int;	axiom (CANCELLED == 1);
const SIGNAL: int;	axiom (SIGNAL == -1);
const CONDITION: int;	axiom (CONDITION == -2);
const PROPAGATE: int;	axiom (PROPAGATE == -3);

const SHARED: Node;
const EXCLUSIVE: Node;
axiom (EXCLUSIVE == NULL_NODE && SHARED != NULL_NODE); // ==> SHARED != NULL_NODE

invariant (forall node: Node :: (node.waitStatus == 0) || (node.waitStatus == CANCELLED) || (node.waitStatus == SIGNAL) || (node.waitStatus == CONDITION) || (node.waitStatus == PROPAGATE));
invariant (forall node: Node :: (node.nextWaiter == SHARED) || (node.nextWaiter == EXCLUSIVE));

/* ================================================================================================Node constructors ================================================================================================*/

procedure Node_1() returns (this: Node)
{
	this := New Node;
	this.nextWaiter := EXCLUSIVE;
	this.thread := NULL_THREAD;
	this.next := NULL_NODE;
	this.prev := NULL_NODE;
	this.waitStatus := 0;
}

// From javadoc: used in addWaiter() method
// Kivanc note: This is what we really need!
procedure Node_2(thread: Thread, mode: Node) returns (this: Node)
{
	this := New Node;
	this.nextWaiter := mode;
	this.thread := thread;
	this.next := NULL_NODE;
	this.prev := NULL_NODE;
	this.waitStatus := 0;
}

// From javadoc: used by Conditions
// Kivanc note: We don't need it for now. (we are not interested with Conditions)
procedure Node_3(thread: Thread, waitStatus: int)  returns (this: Node)
{
	this := New Node;
	this.waitStatus := waitStatus;
	this.thread := thread;
	this.next := NULL_NODE;
	this.prev := NULL_NODE;
	this.nextWaiter := NULL_NODE;
	this.waitStatus := 0;
}

/* ================================================================================================AQS ================================================================================================*/

record AQS 
{
	head: Node;
	tail: Node;
	state: int;	
	exclusiveOwnerThread: Thread;
}


/**
     * Inserts node into queue, initializing if necessary. See picture above.
     * @param node the node to insert
     * @return node's predecessor
     */
procedure AQS_enq (this: AQS, node: Node) returns (result: Node)
{
	var t: Node, h: Node, guard: bool;
	
	while (true)
	{
		t := this.tail;
		if (t == NULL_NODE)
		{
			call h := Node_1();
			call guard :=  AQS_compareAndSetHead(this, h);
			if (guard)
			{
				this.tail := h;
			}
		}
		else
		{
			node.prev := t;
			call guard := AQS_compareAndSetTail(this, t, node);
			if (guard)
			{
				t.next := node;
				result := t;
				return;
			}
		}
	}
} // AQS_enq

/**
     * Creates and enqueues node for current thread and given mode.
     *
     * @param mode Node.EXCLUSIVE for exclusive, Node.SHARED for shared
     * @return the new node
     */
procedure AQS_addWaiter(this: AQS, mode: Node) returns (node: Node)
{
	var pred: Node, currentThread: Thread, dummy: Node, guard: bool;
	
	call currentThread := Thread_currentThread();
	
	call node := Node_2(currentThread, mode);
	pred := this.tail;
	if (pred != NULL_NODE)
	{
		node.prev := pred;
		call guard := AQS_compareAndSetTail(this, pred, node);
		if (guard)
		{
			pred.next := node;
			return;
		}
	}
	
	call dummy := AQS_enq(this, node);
} // AQS_addWaiter

/**
     * Sets head of queue to be node, thus dequeuing. Called only by
     * acquire methods.  Also nulls out unused fields for sake of GC
     * and to suppress unnecessary signals and traversals.
     *
     * @param node the node
     */
procedure AQS_setHead(this: AQS, node: Node)
{
	this.head := node;
	node.thread := NULL_THREAD;
	node.prev := NULL_NODE;
} // AQS_setHead

/**
     * Wakes up node's successor, if one exists.
     *
     * @param node the node
     */
procedure AQS_unparkSuccessor(this: AQS, node: Node)
{
	var s: Node, t: Node, guard: bool, ws: int, dummy: bool;
	
	ws := node.waitStatus;
	if (ws < 0) {
	  call dummy := AQS_compareAndSetWaitStatus(node, ws, 0);
	}
	
	s := node.next;
	guard := (s == NULL_NODE);
	if(!guard) {  guard := (s.waitStatus > 0); }

	if (guard) // find a non-cancelled successor
	{
		s := NULL_NODE;

		t := this.tail;
		while (t != NULL_NODE && t != node)
		{
			guard := (t.waitStatus <= 0);
			if (guard)
			{
				s := t;
			}
			t := t.prev;
		}
	}
	if (s != NULL_NODE)
	{
		call LockSupport_unpark(s.thread);
	}
} // AQS_unparkSuccessor

/**
     * Release action for shared mode -- signal successor and ensure
     * propagation. (Note: For exclusive mode, release just amounts
     * to calling unparkSuccessor of head if it needs signal.)
     */
procedure AQS_doReleaseShared (this: AQS)
{
	var h: Node, guard: bool, ws: int;

	while(true) {
		h := this.head;
		guard := (h != NULL_NODE);
		if(guard) {
			  guard := (h != this.tail);
		}
		if(guard) {
			  ws := h.waitStatus;
			  if(ws == SIGNAL) {
			  	call guard := AQS_compareAndSetWaitStatus(h, SIGNAL, 0);
				if(!guard) { continue; }
				call AQS_unparkSuccessor(this, h);
			  } else {
			    	guard := (ws == 0);
				if(guard) {
				      call guard := AQS_compareAndSetWaitStatus(h, 0, PROPAGATE);
				      guard := !guard;
				}
				if(guard) { continue; }
			  }
		}
		guard := (h == this.head);
		if(guard) { break; }
	}

} // AQS_doReleaseShared

/**
     * Sets head of queue, and checks if successor may be waiting
     * in shared mode, if so propagating if either propagate > 0 or
     * PROPAGATE status was set.
     *
     * @param node the node
     * @param propagate the return value from a tryAcquireShared
     */
procedure AQS_setHeadAndPropagate(this: AQS, node: Node, propagate: int)
{
	var h: Node, guard: bool, s: Node;

	h := this.head;
	call AQS_setHead(this, node);
	
	guard := (propagate > 0);
	if(!guard) { guard := (h == NULL_NODE); }
	if(!guard) { guard := (h.waitStatus  < 0); }

	if(guard) {
		  s := node.next;
		  guard := (s == NULL_NODE);
		  if(!guard) {
		  	     call guard := Node_isShared(s);
		  }
		  if(guard) {
		  	    call AQS_doReleaseShared(this);
		  }
	}
	
} // AQS_setHeadAndPropagate

/**
     * Cancels an ongoing attempt to acquire.
     *
     * @param node the node
     */
procedure AQS_cancelAcquire(this: AQS, node: Node)
{
	var guard: bool, pred: Node, predNext: Node, next: Node, dummy: bool, ws: int;
	
	if (node != NULL_NODE)
	{
		node.thread := NULL_THREAD;
		
		pred := node.prev;
		guard := (pred.waitStatus > 0);
		while (guard)
		{
			pred := pred.prev;
			node.prev := pred;
			guard := (pred.waitStatus > 0);
		}
		
		predNext := pred.next;
		node.waitStatus := CANCELLED;
		
		guard := (node == this.tail);
		if (guard)
		{
			call guard := AQS_compareAndSetTail(this, node, pred);
			
		}
		if (guard)
		{
			call dummy := AQS_compareAndSetNext(pred, predNext, NULL_NODE);
		} else {
			guard := (pred != this.head);
			if (guard)
			{
				ws := pred.waitStatus;
				guard := (ws == SIGNAL);
				if(!guard && ws <= 0) {
					  call guard := AQS_compareAndSetWaitStatus(pred, ws, SIGNAL);
				}
				if (guard)
				{
					guard := (pred.thread != NULL_THREAD);
				}
				
			}
			if (guard)
			{
				next := node.next;
				guard := (next != NULL_NODE);
				if(guard) {
					  guard := (next.waitStatus != CANCELLED);
				}
				if(guard) {
					call dummy := AQS_compareAndSetNext(pred, predNext, next);
				}
			} else {
				call AQS_unparkSuccessor(this, node);
			}
			node.next := node; // help GC
		}
	}
}

/**
     * Checks and updates status for a node that failed to acquire.
     * Returns true if thread should block. This is the main signal
     * control in all acquire loops.  Requires that pred == node.prev
     *
     * @param pred node's predecessor holding status
     * @param node the node
     * @return {@code true} if thread should block
     */
procedure AQS_shouldParkAfterFailedAcquire(this: AQS, preD: Node, node: Node) returns (result: bool)
{
	var ws: int, dummy: bool, pred: Node;

	pred := preD;

	ws := pred.waitStatus;
	if(ws == SIGNAL) {
	      result := true;
	      return;
	}
	if(ws > 0) { // pred was cancelled
	      while(ws > 0) {
	      	       pred := pred.prev;
		       node.prev := pred;
		       ws := pred.waitStatus;
	      }
	      pred.next := node;
	} else { // 0 or PROPAGATE
	      call dummy := AQS_compareAndSetWaitStatus(pred, ws, SIGNAL);
	}
	result := false;
} // AQS_shouldParkAfterFailedAcquire


procedure AQS_selfInterrupt()
{
	var currentThread: Thread;

	call currentThread := Thread_currentThread();
	call Thread_interrupt(currentThread);
} // AQS_selfInterrupt

procedure AQS_parkAndCheckInterrupt(this: AQS) returns (result: bool)
{
	var currentThread: Thread;
	
	call currentThread := Thread_currentThread();
	call LockSupport_park(currentThread);
	call result := Thread_interrupted();
} // AQS_parkAndCheckInterrupt

/**
     * Acquires in exclusive uninterruptible mode for thread already in
     * queue. Used by condition wait methods as well as acquire.
     *
     * @param node the node
     * @param arg the acquire argument
     * @return {@code true} if interrupted while waiting
     */
procedure AQS_acquireQueued(this: AQS, node: Node, arg: int) returns (interrupted: bool)
{
	var p: Node, guard: bool;

	try
	{
		interrupted := false;
		while (true)
		{
			call p := Node_predecessor(node);
			guard := (p == this.head);
			if (guard)
			{
				call guard := AQS_tryAcquire(this, arg);
				
			}
			if (guard)
			{
				call AQS_setHead(this, node);
				p.next := NULL_NODE; // help GC
				return;
			} 
			call guard := AQS_shouldParkAfterFailedAcquire(this, p, node);
			if (guard)
			{
				call interrupted := AQS_parkAndCheckInterrupt(this);
			}
		}
	} catch {
		call AQS_cancelAcquire(this, node);
	}
} // AQS_acquireQueued

/**
     * Acquires in shared uninterruptible mode.
     * @param arg the acquire argument
     */

procedure AQS_doAcquireShared(this: AQS, arg: int) returns (interrupted: bool)
{
	var p: Node, guard: bool, node: Node, r: int;

	call node := AQS_addWaiter(this, SHARED);

	try
	{
		interrupted := false;
		while (true)
		{
			call p := Node_predecessor(node);
			guard := (p == this.head);
			if (guard)
			{
				call r := AQS_tryAcquireShared(this, arg);
				if(r >= 0) {
				     call AQS_setHeadAndPropagate(this, node, r);
				     p.next := NULL_NODE; // help GC
				     if(interrupted) {
				     	call AQS_selfInterrupt();
				     }
				     return;
				}
			} 
			call guard := AQS_shouldParkAfterFailedAcquire(this, p, node);
			if (guard)
			{
				call interrupted := AQS_parkAndCheckInterrupt(this);
			}
		}
	} catch {
		call AQS_cancelAcquire(this, node);
	}
} // AQS_doAcquireShared

/**
     * Acquires in exclusive mode, ignoring interrupts.  Implemented
     * by invoking at least once {@link #tryAcquire},
     * returning on success.  Otherwise the thread is queued, possibly
     * repeatedly blocking and unblocking, invoking {@link
     * #tryAcquire} until success.  This method can be used
     * to implement method {@link Lock#lock}.
     *
     * @param arg the acquire argument.  This value is conveyed to
     *        {@link #tryAcquire} but is otherwise uninterpreted and
     *        can represent anything you like.
     */
procedure AQS_acquire(this: AQS, arg: int)
{
	var guard: bool, node: Node, dummy: bool;

	call guard := AQS_tryAcquire(this, arg);
	if(!guard){
		call node:= AQS_addWaiter(this, EXCLUSIVE);
		call dummy := AQS_acquireQueued(this, node, arg);
		call AQS_selfInterrupt();
	}
} // AQS_acquire

/**
     * Releases in exclusive mode.  Implemented by unblocking one or
     * more threads if {@link #tryRelease} returns true.
     * This method can be used to implement method {@link Lock#unlock}.
     *
     * @param arg the release argument.  This value is conveyed to
     *        {@link #tryRelease} but is otherwise uninterpreted and
     *        can represent anything you like.
     * @return the value returned from {@link #tryRelease}
     */
procedure AQS_release(this: AQS, arg: int) returns (result: bool)
{
	var h: Node, guard: bool, dummy: boolean;
	
	call guard := AQS_tryRelease(this, arg);
	if (guard)
	{
		h := this.head;
		guard := (h != NULL_NODE);
		if(guard) {
			guard := (h.waitStatus != 0);
		}
		if(guard) {
			  call AQS_unparkSuccessor(this, h);
		}
		result := true;
	}
	else
	{
		result := false;
	}
} // AQS_release

/**
     * Acquires in shared mode, ignoring interrupts.  Implemented by
     * first invoking at least once {@link #tryAcquireShared},
     * returning on success.  Otherwise the thread is queued, possibly
     * repeatedly blocking and unblocking, invoking {@link
     * #tryAcquireShared} until success.
     *
     * @param arg the acquire argument.  This value is conveyed to
     *        {@link #tryAcquireShared} but is otherwise uninterpreted
     *        and can represent anything you like.
     */
procedure AQS_acquireShared(this: AQS, arg: int)
{
	var r: int, dummy: bool;

	call r := AQS_tryAcquireShared(this, arg);
	if(r < 0){
		call dummy := AQS_doAcquireShared(this, arg);
	}
} // AQS_acquireShared

procedure AQS_releaseShared(this: AQS, arg: int) returns (result: bool)
{
	call result := AQS_tryReleaseShared(this, arg);
	if(result){
		call AQS_doReleaseShared(this);
	}
} // AQS_releaseShared

/* ================================================================================================Atomic methods ================================================================================================*/

procedure {:isatomic} Node_isShared(this: Node) returns (result: bool)
{
	result := (this.nextWaiter == SHARED);
}

procedure {:isatomic} Node_predecessor(this: Node) returns (result: Node)
{
	if (this.prev == NULL_NODE)
	{
	  throw NullPointerException;
	}
	result := this.prev;
}

procedure {:isatomic} AQS_getState(this: AQS) returns (result: int)
{
	result := this.state;
}

procedure {:isatomic} AQS_setState(this: AQS, newState: int)
{
	this.state := newState;
}

procedure {:isatomic} AQS_compareAndSetState(this: AQS, expect: int, update: int) returns (result: bool)
{
	result := (this.state == expect);
	if(result) { this.state := update; }
}

procedure {:isatomic} AQS_compareAndSetHead(this: AQS, update: Node) returns (result: bool)
{
	result := (this.head == NULL_NODE);
	if(result) { this.head := update; }
}

procedure {:isatomic} AQS_compareAndSetTail(this: AQS, expect: Node, update: Node) returns (result: bool)
{
	result := (this.tail == expect);
	if(result) { this.tail := update; }
}

procedure {:isatomic} AQS_compareAndSetWaitStatus(node: Node, expect: int, update: int) returns (result: bool)
{
	result := (node.waitStatus == expect);
	if(result) { node.waitStatus := update; }
}

procedure {:isatomic} AQS_compareAndSetNext(node: Node, expect: Node, update: Node) returns (result: bool)
{
	result := (node.next == expect);
	if(result) { node.next := update; }
}

procedure {:isatomic} AQS_getExclusiveOwnerThread(this: AQS) returns(thread: Thread)
{
	thread := this.exclusiveOwnerThread;
} // AQS_getExclusiveOwnerThread

procedure {:isatomic} AQS_setExclusiveOwnerThread(this: AQS, thread: Thread)
{
	this.exclusiveOwnerThread := thread;
} // AQS_getExclusiveOwnerThread

procedure {:isatomic} LockSupport_park(thread: Thread)
{
	assume true;
}

procedure {:isatomic} LockSupport_unpark(thread: Thread)
{
	assume true;
}



// implementing a Mutex

procedure {:ispublic} AQS_isHeldExclusively(this: AQS) returns (result: bool)
{
	var s: int;

	call s := AQS_getState(this);
	result := (s == 1);
} // AQS_isHeldExclusively

procedure AQS_tryAcquireShared(this: AQS, acquires: int) returns (result: int)
{
	assume true;
} // AQS_tryAcquireShared

procedure AQS_tryReleaseShared(this: AQS, releases: int) returns (result: bool)
{
	assume true;
} // AQS_tryReleaseShared

procedure AQS_tryAcquire(this: AQS, acquires: int) returns (result: bool)
{
	var currentThread: Thread;

	assert acquires == 1;
	call result := AQS_compareAndSetState(this, 0, 1);
	if(result) {
		   call currentThread := Thread_currentThread();
		   call AQS_setExclusiveOwnerThread(this, currentThread);
	}
	
} // AQS_tryAcquire

procedure AQS_tryRelease(this: AQS, releases: int) returns (result: bool)
{
	var currentThread: Thread, s: int;

	assert releases == 1;
	
	call s := AQS_getState(this);
	if(s == 0) {
	     throw IllegalMonitorStateException;
	}

	call AQS_setExclusiveOwnerThread(this, NULL_THREAD);
	call AQS_setState(this, 0);
	result := true;

} // AQS_tryRelease

record Lock
{
	Sync: AQS;
}

procedure Lock_lock(l: Lock)
{
	call AQS_acquire(l.Sync, 1);
}

procedure Lock_tryLock(l: Lock)
{
	var dummy: bool;

	call dummy := AQS_tryAcquire(l.Sync, 1);
}

procedure Lock_unlock(l: Lock)
{
	var dummy: bool;

	call dummy := AQS_release(l.Sync, 1);
}
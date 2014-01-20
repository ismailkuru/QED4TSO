// Some abbreviations
// AQS = AbstractQueuedSynchronizer
// AOS = AbstractOwnableSynchronizer

// =================================================================================================
// === Some NULL values modeled as constants.
// =================================================================================================

const unique NULL_NODE: Node;
const unique NULL_THREAD: Thread;

// =================================================================================================
// === End of NULL values.
// =================================================================================================

// =================================================================================================
// === Some Exceptions modeled as constants.
// =================================================================================================

const unique NullPointerException: Exception;
const unique Error: Exception;
const unique IllegalMonitorStateException: Exception;
const unique RuntimeException: Exception;

// axiom subtype(NullPointerException, RuntimeException);
// axiom subtype(IllegalMonitorStateException, RuntimeException);
// Note that in java Error is not a RuntimeException!
// axiom subtype(Error, RuntimeException);

// =================================================================================================
// == End of Exception modeling 
// =================================================================================================


// =================================================================================================
// === Start of modeling Thread class
// for now we only need id field.
// =================================================================================================

// =================================================================================================
// === Start of Thread as a record
// =================================================================================================
record Thread
{
	id: int;
	interrupted: boolean;
}

var Threads: [int]Thread;
invariant (Threads[0] == NULL_THREAD);
invariant (forall i: int :: (Threads[i]).id == i);

// =================================================================================================
// === End of Thread as a record
// =================================================================================================

// =================================================================================================
// === Modeling methods of Thread
// ================================================================================================= 

// This is the model of native isInterrupted() method of the Thread.java
procedure {:isatomic true} {:ispublic false} Thread_nativeIsInterrupted(this: Thread, clearInterrupted: bool) returns (result: bool)
{
	var guard: bool;
	result := (this.interrupted == True);
	if (result)
	{
		if (clearInterrupted)
		{
			this.interrupted := False;
		}
	}
}

// interrupt() method
procedure {:ispublic false} Thread_interrupt(this: Thread)
{
	this.interrupted := True;
}

// =================================================================================================
// === Modeling static methods of Thread
// ================================================================================================= 
procedure {:ispublic false} {:isatomic true} Thread_currentThread() returns (result: Thread) 
{
	result := Threads[tid];
}

procedure {:ispublic false} Thread_interrupted() returns (result: bool)
{
	var currentThread: Thread;
	// currentThread := Threads[tid];
	call currentThread := Thread_currentThread();
	call result := Thread_nativeIsInterrupted(currentThread, true);
}

// =================================================================================================
// === End of modeling Thread class.
// =================================================================================================

// =================================================================================================
// === Modeling Node class in the AQS (inner class in java)
// =================================================================================================

// =================================================================================================
// === Universal constants (enumeration defined inside the Node class)
// =================================================================================================
// === Define a new type = NodeWaitStatus to handle 3 of the enumerations: CANCELLED, SIGNAL, CONDITION
// === Note: I had to get rid of this modeling. NodeStatus will be modeled as integer. 
// this is because tryAcquire() calls setState() with an integer that is not known. Though
// it is most probably 1 (CANCELLED), since there is no way to be sure, I am just turning everything to
// integers again.
// === Note2: Never mind, I just mixed the state of the node and state of the AQS. So modeling with
// enumerations is still possible.
  
type NodeWaitStatus;
const unique CANCELLED: NodeWaitStatus;
const unique SIGNAL: NodeWaitStatus;
const unique CONDITION: NodeWaitStatus;
// Kivanc note: There is no explicit NO_WAIT_STATUS defined in java.util.concurrent.
// However since the wait status was defined as an integer there, in the code
// they do use the value of '0' (which is new) in the comparisons. Thus, we have one more
// enumeration.
const unique NO_WAIT_STATUS: NodeWaitStatus;
axiom (forall nws:NodeWaitStatus :: (nws == CANCELLED) || (nws == SIGNAL) || (nws == CONDITION) || (nws == NO_WAIT_STATUS));
// === End of NodeWaitStatus define.

const unique SHARED: Node;
// I didn't model EXCLUSIVE, since it was just equal to null. I just enter NULL_NODE where 
// EXCLUSIVE is called.
// =================================================================================================
// === End of Universal constants define.
// =================================================================================================

// =================================================================================================
// === Start of Node as a record
// =================================================================================================
record Node
{
	// This was modeled as an integer in java, however we have used enumerations.
	// So I am taking advantage of this feature.
	waitStatus: NodeWaitStatus;
	prev: Node;
	next: Node;
	nextWaiter: Node;
	thread: Thread;
}

// =================================================================================================
// === End of Node as a record
// =================================================================================================

// =================================================================================================
// === Start of Node methods
// =================================================================================================

// Empty constructor in java modeled as below:
// From javadoc: used in the creation of initial head or SHARED marker 
// Kivanc note: We have modeled SHARED marker differently (as a constant) so only use in the creation
// of the initial head.
// Below is commented out :: Reason : Was used in method AQS_enq(), and since it was modeled atomically to simplfy the proof, this is gone too.

procedure {:ispublic false} {:isatomic true} Node_Node(this: Node) 
{
	this.prev := NULL_NODE;
	this.next := NULL_NODE;
	this.nextWaiter := NULL_NODE;
	this.thread := NULL_THREAD;
	this.waitStatus := NO_WAIT_STATUS;
}


// From javadoc: used in addWaiter() method
// Kivanc note: This is what we really need!
procedure {:ispublic false} Node_Node_2(this: Node, thread: Thread, mode: Node)
{
	this.nextWaiter := mode;
	this.thread := thread;
	this.next := NULL_NODE;
	this.prev := NULL_NODE;
	this.waitStatus := NO_WAIT_STATUS;
}

procedure{:ispublic false} Node_predecessor(this: Node) returns (result: Node)
{
	result := this.prev;
	if (result == NULL_NODE)
	{
		throw NullPointerException;
	}	
}

// =================================================================================================
// === End of modeling Node class.
// =================================================================================================

// =================================================================================================
// === Modeling NonfairSync class
// Fair Sync will have all extended classes (AQS, AOS, Sync) modeled inside it.
// =================================================================================================
record NonfairSync 
{
	// Modeling AOS
	exclusiveOwnerThread: Thread;
	
	// Modeling AQS

	head: Node;
	tail: Node;
	state: int;	
}

// =================================================================================================
// === Start of NonfairSync's AOS related methods
// =================================================================================================
procedure {:ispublic false} AOS_setExclusiveOwnerThread(this: NonfairSync, t: Thread)
{
	this.exclusiveOwnerThread := t;
}

procedure {:ispublic false} AOS_getExclusiveOwnerThread(this: NonfairSync) returns (result: Thread)
{
	result := this.exclusiveOwnerThread;
}
// =================================================================================================
// === End of NonfairSync's AOS related methods.
// =================================================================================================

// =================================================================================================
// === Start of NonfairSync's AQS related methods
// =================================================================================================

procedure{:ispublic false} AQS_getState(this: NonfairSync) returns (result: int)
{
	result := this.state;
}

procedure{:ispublic false} AQS_setState(this: NonfairSync, newState: int)
{
	this.state := newState;
}
/*
procedure {:ispublic false} {:isatomic true} AQS_enq(this: NonfairSync, node: Node) returns (result: Node)
{
	var h: Node;
	var t: Node;
	
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
		// call Node_Node(h);
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
}*/

// ==========================================================================
// node: Node to be added to the queue.
// returns the node in the queue that comes before this node (older tail)
// (if queue was empty return the dummy header created)
// Note: Has unlimited rollbacks (i.e. tries until the node is added to the queue)
// ==========================================================================
// Below is commented out :: Reason :: Will be modeled atomically in order to simplify ReentrantLock

procedure{:ispublic false} AQS_enq(this: NonfairSync, node: Node) returns (result: Node)
{
	var t: Node;
	var h: Node;
	var dummy: bool;
	
	while (true)
	{
		t := this.tail;
		// If tail is null, this means that our queue is empty.
		if (t == NULL_NODE)
		{
			// We use a dummy header node in the beginning so create that dummy node.
			h := New Node;
			call Node_Node(h);
			// The next node (first node) is the current node and they are doubly linked.
			h.next := node;
			node.prev := h;
			// set the dummy node as head atomically, as expected in casSetHead, current head 
			// should be null
			call dummy :=  AQS_compareAndSetHead(this, h);
			// if the cas operation is successful, set the node as tail and return the dummy header.
			if (dummy)
			{
				this.tail := node;
				result := h;
				return;
			}
		}
		// The queue is not empty.
		else
		{
			// add node to the end of the queue (make it tail) with atomic operation.
			node.prev := t;
			call dummy := AQS_compareAndSetTail(this, t, node);
			// if successful, link node to the tail node and return the tail.
			if (dummy)
			{
				t.next := node;
				result := t;
				return;
			}
		}
	}
}


procedure{:ispublic false} AQS_setHead(this: NonfairSync, node: Node)
{
	this.head := node;
	node.thread := NULL_THREAD;
	node.prev := NULL_NODE;
}

procedure {:ispublic false} AQS_addWaiter(this: NonfairSync, mode: Node) returns (result: Node)
{
	var node: Node;
	var pred: Node;
	var currentThread: Thread;
	var dummyNode: Node;
	var dummy: bool;
	var done: bool;
	
	done := false;
	call currentThread := Thread_currentThread();
	
	node := New Node;
	assume node != NULL_NODE;
	call Node_Node_2(node, currentThread, mode);
	pred := this.tail;
	if (pred != NULL_NODE)
	{
		node.prev := pred;
		call dummy := AQS_compareAndSetTail(this, pred, node);
		if (dummy)
		{
			pred.next := node;
			result := node;
			done := true;
		}
	}
	
	if (!done)
	{
		call dummyNode := AQS_enq(this, node);
		result := node;
	}
}


// ==========================================================================
// node: We are going to unpark the successor of the node. (if any)
// Implementation algorithm taken directly from the java comments:
// Thread to unpark is held in successor, which is normally
// just the next node.  But if cancelled or apparently null,
// traverse backwards from tail to find the actual
// non-cancelled successor.
// ==========================================================================
procedure {:ispublic false} AQS_unparkSuccessor(this: NonfairSync, node: Node)
{
	// s holds the successor of the 'node'.
	var s: Node;
	// t holds the tail node.
	var t: Node;
	var dummy: bool;
	var dummy_2: bool;
	var guard: bool;
	
	call dummy := AQS_compareAndSetWaitStatus(node, SIGNAL, NO_WAIT_STATUS);
	s := node.next;
	dummy := (s == NULL_NODE || s.waitStatus == CANCELLED);
	if (dummy)
	{
		s := NULL_NODE;
		t := this.tail;
		
		guard := (t != NULL_NODE && t != node);
		while (guard)
		{
			dummy_2 := (t.waitStatus != CANCELLED);
			if (dummy_2)
			{
				s := t;
			}
			t := t.prev;
			guard := (t != NULL_NODE && t != node);
		}
	}
	if (s != NULL_NODE)
	{
		call LockSupport_unpark(s.thread);
	}
}

// ==========================================================================
// arg: argument given to release (most probably this is again -1)
// returns true if the release is successful, false otherwise.
// Notes: this directly calls tryRelease() from Sync. If the trial is successful
// than it also unparks the successor of the head node.
// ==========================================================================
procedure AQS_release(this: NonfairSync, arg: int) returns (result: bool)
{
	var h: Node;
	var dummy: bool;
	
	call result := Sync_tryRelease(this, arg);
	if (result)
	{
		h := this.head;
		dummy := (h != NULL_NODE && h.waitStatus != NO_WAIT_STATUS);
		if (dummy)
		{
			call AQS_unparkSuccessor(this, h);
		}
	}
}

// Honestly I didn't understand much of this method. Need to return and look more!
procedure {:ispublic false} AQS_cancelAcquire(this: NonfairSync, node: Node)
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
		node.thread := NULL_THREAD;
		
		pred := node.prev;
		dummy_2 := (pred.waitStatus == CANCELLED);
		while (dummy_2)
		{
			pred := pred.prev;
			node.prev := pred;
			dummy_2 := (pred.waitStatus == CANCELLED);
		}
		
		predNext := pred.next;
		node.waitStatus := CANCELLED;
		
		guard := (node == this.tail);
		if (guard)
		{
			call guard := AQS_compareAndSetTail(this, node, pred);
			if (guard)
			{
				call dummy := AQS_compareAndSetNext(pred, predNext, NULL_NODE);
			}
		}
		if (!guard)
		{
			guard := (pred != this.head);
			if (guard)
			{
				guard := (pred.waitStatus == SIGNAL);
				if (!guard)
				{
					call guard := AQS_compareAndSetWaitStatus(pred, NO_WAIT_STATUS, SIGNAL);
				}
				if (guard)
				{
					guard := (pred.thread != NULL_THREAD);
					if (guard)
					{
						next := node.next;
						dummy_3 := (next != NULL_NODE && next.waitStatus != CANCELLED);
						if (dummy_3)
						{
							call dummy := AQS_compareAndSetNext(pred, predNext, next);
						}
					}
				}
			}
			if (!guard)
			{
				call AQS_unparkSuccessor(this, node);
			}
			node.next := node;
			// help GC.
		}
	}
}

procedure {:ispublic false} AQS_parkAndCheckInterrupt(this: NonfairSync) returns (result: bool)
{
	var currentThread: Thread;
	call currentThread := Thread_currentThread();
	call LockSupport_park(currentThread);
	call result := Thread_interrupted();
}

procedure {:ispublic false} AQS_acquireQueued(this: NonfairSync, node: Node, arg: int) returns (result: bool)
{
	var interrupted: bool;
	var p: Node; 
	var guard: bool;
	var dummy: bool;

	try
	{
		interrupted := false;
		while (true)
		{
			call p := Node_predecessor(node);
			guard := (p == this.head);
			if (guard)
			{
				call guard := NonfairSync_tryAcquire(this, arg);
				if (guard)
				{
					call AQS_setHead(this, node);
					p.next := NULL_NODE;
					result := interrupted;
					return;
				} 
			}
			call dummy := AQS_shouldParkAfterFailedAcquire(p, node);
			if (dummy)
			{
				call dummy := AQS_parkAndCheckInterrupt(this);
				if (dummy)
				{
					interrupted := true;
				} 
			}
		}
	} catch (RuntimeException) {
		call AQS_cancelAcquire(this, node);
		// throw ex;
	}
}

procedure {:ispublic true} AQS_acquire(this: NonfairSync, arg: int)
{
	var guard: bool;
	var dummyNode: Node;
	
	call guard := NonfairSync_tryAcquire(this, arg);
	if (!guard)
	{
		// NODE_NULL here represents EXCLUSIVE!
		call dummyNode := AQS_addWaiter(this, NULL_NODE);
		call guard := AQS_acquireQueued(this, dummyNode, arg);
		if (guard)
		{
			call AQS_selfInterrupt();
		}
	}	
}

// =================================================================================================
// === Static methods
// =================================================================================================

procedure{:ispublic false} AQS_shouldParkAfterFailedAcquire(pred: Node, node: Node) returns (result: bool)
{
	var pred_dup: Node;
	var s: NodeWaitStatus;
	var dummy: bool;
	var guard : bool;
	
	s := pred.waitStatus;
	if (s == SIGNAL || s == CONDITION)
	{
		result := true;
	}
	else if (s == CANCELLED)
	{
		pred_dup := pred;
		pred_dup := pred_dup.prev;
		node.prev := pred_dup;
		
		guard := (pred_dup.waitStatus == CANCELLED);
		while (guard)
		{
			pred_dup := pred_dup.prev;
			node.prev := pred_dup;
			
			guard := (pred_dup.waitStatus == CANCELLED);
		}
		pred_dup.next := node;
		result := false;
	}
	else
	{
		call dummy := AQS_compareAndSetWaitStatus(pred, NO_WAIT_STATUS, SIGNAL);
		result := false;
	}
}

procedure {:ispublic false} AQS_selfInterrupt()
{
	var currentThread: Thread;
	call currentThread := Thread_currentThread();
	call Thread_interrupt(currentThread);
}

// =================================================================================================
// === Atomic methods
// =================================================================================================
// Kivanc note: Normally this calls Unsafe in java, however I modeled it atomically and did what would
// unsafe do.
procedure{:ispublic false} {:isatomic true} AQS_compareAndSetState(this: NonfairSync, expect: int, update: int) returns (result: bool)
{
	result := (this.state == expect);
	if (result)
	{
		this.state := update;
	}
}

// Kivanc note: Again this was a call to unsafe and modeled atomically.
// Below is commented out :: Reason: Only used in enq() method and enq() is modeled atomically for simplification.

procedure{:ispublic false} {:isatomic true} AQS_compareAndSetHead(this: NonfairSync, update: Node) returns (result: bool)
{
	result := (this.head == NULL_NODE);
	if (result)
	{
		this.head := update;
	}
}


// Kivanc note: Same modeling as casHead()
procedure{:ispublic false} {:isatomic true} AQS_compareAndSetTail(this: NonfairSync, expect: Node, update: Node) returns (result: bool)
{
	result := (this.tail == expect);
	if (result)
	{
		this.tail := update;
	}
}

// Kivanc note: Same as other cas operations.
procedure{:ispublic false} {:isatomic true} AQS_compareAndSetWaitStatus(node: Node, expect: NodeWaitStatus, update: NodeWaitStatus) returns (result: bool)
{
	result := (node.waitStatus == expect);
	if (result)
	{
		node.waitStatus := update;
	}
}

// Kivanc note: same as other cas operations.
procedure {:ispublic false} {:isatomic true} AQS_compareAndSetNext(node: Node, expect: Node, update: Node) returns (result: bool)
{
	result := (node.next == expect);
	if (result)
	{
		node.next := update;
	}
}

// =================================================================================================
// === End of NonfairSync's AQS related methods.
// =================================================================================================

// =================================================================================================
// === Start of NonfairSync's Sync related methods.
// =================================================================================================

// =================================================================================================
// releases: the value of releasing? (I think this is called with -1 all the time)
// returns true if releasing (completely) is successful, false otherwise.
// Note: This is the method that decides weather the current thread release the lock or not.
// =================================================================================================
procedure {:ispublic false} Sync_tryRelease(this: NonfairSync, releases: int) returns (result: bool)
{
	// c hold how many times the lock is locked by the owner thread.
	var c: int;
	var currentThread: Thread;
	var ownerThread: Thread; 
	
	call c := AQS_getState(this);
	c := c - releases;
	call currentThread := Thread_currentThread();
	call ownerThread := AOS_getExclusiveOwnerThread(this);
	
	// if current thread is not the owner of the lock, throw IllegalMonitorStateException.
	if (currentThread != ownerThread)
	{
		throw IllegalMonitorStateException;
	}
	
	// else if decrease the number of locks by one, if no lock is left, release the lock
	// completely by setting its owner to null.
	result := false;
	if (c == 0)
	{
		result := true;
		call AOS_setExclusiveOwnerThread(this, NULL_THREAD);
	}
	call AQS_setState(this, c);
}

procedure {:ispublic false} Sync_nonfairTryAcquire(this: NonfairSync, acquires: int) returns (result: bool)
{
	var current: Thread;
	var c: int;
	var nextc: int;
	var dummy: bool;
	var ownerThread: Thread;
	
	result := false;
	call current := Thread_currentThread();
	call c := AQS_getState(this);
	
	if (c == 0)
	{
		call dummy := AQS_compareAndSetState(this, 0, acquires);
		if (dummy)
		{
			call AOS_setExclusiveOwnerThread(this, current);
			result := true;
		}
	}
	else
	{
		call ownerThread := AOS_getExclusiveOwnerThread(this);
		if (current == ownerThread)
		{
			nextc := c + acquires;
			if (nextc < 0)
			{
				throw Error;
			}
			else
			{
				call AQS_setState(this, nextc);
				result := true;
			}
		}
	}
}

// =================================================================================================
// === End of NonfairSync's Sync related methods.
// =================================================================================================


// =================================================================================================
// === Start of NonfairSync's internal methods.
// =================================================================================================

// =================================================================================================
// acquires: the value of acquiring? (I think this is called with 1 all the time)
// returns true if acquiring is successful, false otherwise.
// =================================================================================================
procedure {:ispublic false} NonfairSync_tryAcquire(this: NonfairSync, acquires: int) returns (result: bool)
{
	call result := Sync_nonfairTryAcquire(this, acquires);
}

procedure {:ispublic false} NonfairSync_lock(this: NonfairSync)
{
	var dummy: bool;
	var currentThread: Thread;
	
	call dummy := AQS_compareAndSetState(this, 0, 1);
	if (dummy)
	{
		call currentThread := Thread_currentThread();
		call AOS_setExclusiveOwnerThread(this, currentThread);
	}
	else
	{
		call AQS_acquire(this, 1);
	}
}

// =================================================================================================
// === End of NonfairSync's internal methods.
// =================================================================================================

// =================================================================================================
// === End of NonfairSync modeling.
// =================================================================================================

// =================================================================================================
// === Modeling LockSupport atomically
// It is modeled by adding 2 boolean values to the thread class.
// one is the value of park and the other is the value of unpark.
// there are also two corresponding methods: park() and unpark()
// Note: I am not sure if this covers everything or not. Need to check back.
// =================================================================================================

// =================================================================================================
// thread: thread to park.
// Algorithm: if the thread is previously unparked, then ignore the call, just set the unpark
// field of thread False.
// else, set park value of the Thread true and wait until it is false (i.e. assume it is false)
// this value will be later set by unpark (if it is true)
// Note: I have ignored all blocking features in the real implementation. Normally with parking
// the thread is also set a blocked (i.e. on which object this thread is waiting). 
// =================================================================================================
// Extra note :: This method is modeled as no op in order to simplify the proof.
procedure {:ispublic false} {:isatomic true} LockSupport_park(thread: Thread)
{
	assume true;
}

// =================================================================================================
// thread: thread to unpark.
// Algorithm: if the thread is previously parked and waiting for an unpark call, set unpark value to
// False.
// else, set the unpark value of this thread to True so that the next park() method will not wait.
// =================================================================================================
// Extra note :: This method is modeled as no op in order to simplify the proof.
procedure {:ispublic false} {:isatomic true} LockSupport_unpark(thread: Thread)
{
	assume true;
}

// =================================================================================================
// === End of Modeling LockSupport
// =================================================================================================

// =================================================================================================
// === Start of modeling ReentrantLock (that uses a fair sync)
// =================================================================================================

// =================================================================================================
// === Reentrant lock is modeled as a record.
// We have only one member: a sync (in our case a fair sync)
// =================================================================================================

record ReentrantLock
{
	sync: NonfairSync;
}

procedure ReentrantLock_unlock(this: ReentrantLock)
{
	var dummy: bool;
	call dummy := AQS_release(this.sync, 1);
}

procedure ReentrantLock_lock(this: ReentrantLock)
{
	call NonfairSync_lock(this.sync);
}

// =================================================================================================
// === End of modeling ReentrantLock (that uses a fair sync)
// =================================================================================================



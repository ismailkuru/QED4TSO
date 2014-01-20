// =================================================================================================
// === Modelings done to please my version of QED :)
// =================================================================================================
//type boolean;
//const unique True: boolean;
//const unique False: boolean;
//axiom (forall b: boolean :: (b == True) || (b == False));

//const unique tid: int;
//type Exception;

// =================================================================================================
// == End of modelings done to please my version of QED
// =================================================================================================

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
	parked: boolean;
	unparked: boolean;
	interrupted: boolean;
}
// =================================================================================================
// === End of Thread as a record
// =================================================================================================

// =================================================================================================
// === Modeling methods of Thread
// ================================================================================================= 

// This is the model of native isInterrupted() method of the Thread.java
procedure {:isatomic true} {:ispublic false} Thread_nativeIsInterrupted(this: Thread, clearInterrupted: boolean) returns (result: boolean)
{
	var guard: bool;
	guard := (this.interrupted == True);
	if (guard)
	{
		result := True;
		if (clearInterrupted == True)
		{
			this.interrupted := False;
		}
	}
	else
	{
		result := False;
	}
}

// This is the real isInterrupted() methods of the Thread.java
procedure Thread_isInterrupted(this: Thread) returns (result: boolean)
{
	call result := Thread_nativeIsInterrupted(this, False);
}

// interrupt() method
procedure Thread_interrupt(this: Thread)
{
	this.interrupted := True;
}

// =================================================================================================
// === Modeling static methods of Thread
// ================================================================================================= 
procedure {:isatomic true} Thread_currentThread() returns (result: Thread) 
{
	havoc result;
	assume result.id == tid;
}

procedure  Thread_interrupted() returns (result: boolean)
{
	var currentThread: Thread;
	call currentThread := Thread_currentThread();
	call result := Thread_nativeIsInterrupted(currentThread, True);
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
	// waitStatus: int;
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
procedure {:ispublic false} Node_Node(this: Node) 
{
	this.prev := NULL_NODE;
	this.next := NULL_NODE;
	this.nextWaiter := NULL_NODE;
	this.thread := NULL_THREAD;
	this.waitStatus := NO_WAIT_STATUS;
	// this.waitStatus := 0;
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
	// this.waitStatus := 0;
}

// From javadoc: used by Conditions
// Kivanc note: We don't need it for now. (we are not interested with Conditions)
procedure {:ispublic false} Node_Node_3(this: Node, thread: Thread, waitStatus: NodeWaitStatus)
{
	this.waitStatus := waitStatus;
	this.thread := thread;
	this.next := NULL_NODE;
	this.prev := NULL_NODE;
	this.nextWaiter := NULL_NODE;
	this.waitStatus := NO_WAIT_STATUS;
	// this.waitStatus := 0;
}

procedure {:ispublic false} Node_isShared(this: Node) returns (result: boolean)
{
	var guard : bool;
	
	guard := (this.nextWaiter == SHARED);
	if (guard)
	{	
		result := True;
	}
	else
	{	
		result := False;
	}
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
// === Modeling FairSync class
// Fair Sync will have all extended classes (AQS, AOS, Sync) modeled inside it.
// =================================================================================================
record FairSync 
{
	// Modeling AOS
	exclusiveOwnerThread: Thread;
	
	// Modeling AQS

	head: Node;
	tail: Node;
	state: int;	
}

procedure {:ispublic false} FairSync_FairSync(this: FairSync)
{
	this.exclusiveOwnerThread := NULL_THREAD;
	this.head := NULL_NODE;
	this.tail := NULL_NODE;
	this.state := 0;
}

// =================================================================================================
// === Start of FairSync's AOS related methods
// =================================================================================================
procedure {:ispublic false} AOS_setExclusiveOwnerThread(this: FairSync, t: Thread)
{
	this.exclusiveOwnerThread := t;
}

procedure {:ispublic false} AOS_getExclusiveOwnerThread(this: FairSync) returns (result: Thread)
{
	result := this.exclusiveOwnerThread;
}
// =================================================================================================
// === End of FairSync's AOS related methods.
// =================================================================================================

// =================================================================================================
// === Start of FairSync's AQS related methods
// =================================================================================================

procedure{:ispublic false} AQS_getState(this: FairSync) returns (result: int)
{
	result := this.state;
}

procedure{:ispublic false} AQS_setState(this: FairSync, newState: int)
{
	this.state := newState;
}

// ==========================================================================
// node: Node to be added to the queue.
// returns the node in the queue that comes before this node (older tail)
// (if queue was empty return the dummy header created)
// Note: Has unlimited rollbacks (i.e. tries until the node is added to the queue)
// ==========================================================================
procedure{:ispublic false} AQS_enq(this: FairSync, node: Node) returns (result: Node)
{
	var t: Node;
	var h: Node;
	var dummy: boolean;
	
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
			if (dummy == True)
			{
				this.tail := node;
				result := h;
			}
		}
		// The queue is not empty.
		else
		{
			// add node to the end of the queue (make it tail) with atomic operation.
			node.prev := t;
			call dummy := AQS_compareAndSetTail(this, t, node);
			// if successful, link node to the tail node and return the tail.
			if (dummy == True)
			{
				t.next := node;
				result := t;
			}
		}
	}
}

procedure{:ispublic false} AQS_setHead(this: FairSync, node: Node)
{
	this.head := node;
	node.thread := NULL_THREAD;
	node.prev := NULL_NODE;
}

// ==========================================================================
// current: The thread we are trying to compare with the first (real) node's thread
// of the queue.
// returns true if they are same, false otherwise.
// Note: I didn't understand the meaning of the 'full' in front of the method. Maybe
// it means that the queue is not empty?
// ==========================================================================
procedure {:ispublic false} AQS_fullIsFirst(this: FairSync, current: Thread) returns (result: boolean)
{
	// h holds the header node.
	var h: Node;
	// s holds the second node in the queue. (i.e. first real node)
	var s: Node;
	// t holds the tail node.
	var t: Node;
	// tt holds the tail node's thread.
	var tt: Thread;
	// firstThread holds the first node's (s') thread.
	var firstThread: Thread;
	var guard : bool;
	
	firstThread := NULL_THREAD;
	h := this.head;
	if (h != NULL_NODE)
	{
		s := h.next;
		firstThread := s.thread;
	}
	
	// If there is a header and a real node (i.e. queue is not empty)
	// and the first node really links back to the header ??? Kivanc note: Why need to check?
	// and the first node's thread is not null
	guard := (h != NULL_NODE && s != NULL_NODE && s.prev == this.head && firstThread != NULL_THREAD);
	if (guard)
	{
		// if the first node's thread is the same with current thread, then return true
		// return false otherwise.
		guard := (firstThread == current);
		if (guard)
		{
			result := True;
		}
		else
		{
			result := False;
		}
	}
	// If any of the above conditions fail, 
	else
	{
		t := this.tail;
		
		guard := (t != NULL_NODE && t != this.head);
		// we don't want the current node to be the head (since it is dummy)
		// and also we don't want it to be null.
		while (guard)
		{
			// while these conditions meet, get the thread of that node, if it is not
			// null, set it as the first thread.
			tt := t.thread;
			if (tt != NULL_THREAD)
			{
				firstThread := tt;
			}
			// Then rollback to the previous element and try again for a more previous node.
			t := t.prev;
			
			guard := (t != NULL_NODE && t != this.head);
		}
		
		// If first thread found is null or the same as current thread return true,
		// otherwise return false.
		guard := firstThread == current || firstThread == NULL_THREAD;
		if (guard)
		{
			result := True;
		}
		else
		{
			result := False;
		}
	}
}

procedure {:ispublic false} AQS_isFirst(this: FairSync, current: Thread) returns (result: boolean)
{
	var h: Node;
	var s: Node;
	var guard : bool;
	
	h := this.head;
	if (h == NULL_NODE)
	{
		result := True;
	}
	else
	{
		s := h.next;
		guard := (s != NULL_NODE && s.thread == current);
		if (guard)
		{
			result := True;
		}
		else
		{
			call result := AQS_fullIsFirst(this, current); 
		}
	}
}

procedure {:ispublic false} AQS_addWaiter(this: FairSync, mode: Node) returns (result: Node)
{
	var node: Node;
	var pred: Node;
	var currentThread: Thread;
	var dummyNode: Node;
	var dummy: boolean;
	var done: boolean;
	
	done := False;
	call currentThread := Thread_currentThread();
	
	node := New Node;
	call Node_Node_2(node, currentThread, mode);
	pred := this.tail;
	if (pred != NULL_NODE)
	{
		node.prev := pred;
		call dummy := AQS_compareAndSetTail(this, pred, node);
		if (dummy == True)
		{
			pred.next := node;
			result := node;
			done := True;
		}
	}
	
	if (done == False)
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
procedure {:ispublic false} AQS_unparkSuccessor(this: FairSync, node: Node)
{
	// s holds the node after the 'node'.
	var s: Node;
	// t holds the tail node.
	var t: Node;
	var dummy: boolean;
	var guard: bool;
	
	call dummy := AQS_compareAndSetWaitStatus(node, SIGNAL, NO_WAIT_STATUS);
	s := node.next;
	if (s == NULL_NODE || s.waitStatus == CANCELLED)
	{
		s := NULL_NODE;
		t := this.tail;
		
		guard := (t != NULL_NODE && t != node);
		while (guard)
		{
			if (t.waitStatus != CANCELLED)
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
procedure AQS_release(this: FairSync, arg: int) returns (result: boolean)
{
	var h: Node;
	var dummy: boolean;
	
	call dummy := Sync_tryRelease(this, arg);
	if (dummy == True)
	{
		h := this.head;
		if (h != NULL_NODE && h.waitStatus != NO_WAIT_STATUS)
		{
			call AQS_unparkSuccessor(this, h);
		}
		result := True;
	}
	else
	{
		result := False;
	}
}

// Honestly I didn't understand much of this method. Need to return and look more!
procedure {:ispublic false} AQS_cancelAcquire(this: FairSync, node: Node)
{
	var guard: bool;
	var pred: Node;
	var predNext: Node;
	var next: Node;
	var guard2: boolean;
	
	guard := (node != NULL_NODE);
	if (guard)
	{
		node.thread := NULL_THREAD;
		
		pred := node.prev;
		while (pred.waitStatus == CANCELLED)
		{
			pred := pred.prev;
			node.prev := pred;
		}
		
		predNext := pred.next;
		node.waitStatus := CANCELLED;
		
		guard := (node == this.tail);
		if (guard)
		{
			call guard2 := AQS_compareAndSetTail(this, node, pred);
			guard := (guard2 == True);
			if (guard)
			{
				call guard2 := AQS_compareAndSetNext(pred, predNext, NULL_NODE);
			}
		}
		if (!guard)
		{
			guard := (pred != this.head);
			if (guard)
			{
				if (pred.waitStatus == SIGNAL)
				{
					guard := true;
				}
				else
				{
					call guard2 := AQS_compareAndSetWaitStatus(pred, NO_WAIT_STATUS, SIGNAL);
					guard := (guard2 == True);
				}
				if (guard)
				{
					guard := (pred.thread != NULL_THREAD);
					if (guard)
					{
						next := node.next;
						if (next != NULL_NODE && next.waitStatus != CANCELLED)
						{
							call guard2 := AQS_compareAndSetNext(pred, predNext, next);
						}
					}
				}
			}
			if (!guard)
			{
				call AQS_unparkSuccessor(this, node);
			}
			node.next := node;
		}
	}
}

procedure {:ispublic false} AQS_parkAndCheckInterrupt(this: FairSync) returns (result: boolean)
{
	var currentThread: Thread;
	call currentThread := Thread_currentThread();
	call LockSupport_park(currentThread);
	call result := Thread_interrupted();
}

procedure {:ispublic false} AQS_acquireQueued(this: FairSync, node: Node, arg: int) returns (result: boolean)
{
	var interrupted: boolean;
	var p: Node; 
	var guard: bool;
	var guard2: boolean;
	var e1: Exception;

	try
	{
		interrupted := False;
		while (true)
		{
			call p := Node_predecessor(node);
			guard := (p == this.head);
			if (guard)
			{
				call guard2 := FairSync_tryAcquire(this, arg);
				guard := (guard2 == True);
				if (guard)
				{
					call AQS_setHead(this, node);
					p.next := NULL_NODE;
					result := interrupted;
					return;
				} 
			}
			if (!guard)
			{
				call guard2 := AQS_shouldParkAfterFailedAcquire(p, node);
				guard := (guard2 == True);
				if (guard)
				{
					call guard2 := AQS_parkAndCheckInterrupt(this);
					guard := (guard2 == True);
					if (guard)
					{
						interrupted := True;
					} 
				}
			}
		}
	} catch (e1) {
		call AQS_cancelAcquire(this, node);
		throw e1;
	}
}

procedure {:ispublic true} AQS_acquire(this: FairSync, arg: int)
{
	var guard: bool;
	var dummy: boolean;
	var dummyNode: Node;
	
	call dummy := FairSync_tryAcquire(this, arg);
	guard := (dummy == True);
	if (!guard)
	{
		// NODE_NULL here represents EXCLUSIVE!
		call dummyNode := AQS_addWaiter(this, NULL_NODE);
		call dummy := AQS_acquireQueued(this, dummyNode, arg);
		guard := (dummy == True);
		if (guard)
		{
			call AQS_selfInterrupt();
		}
	}	
}

// =================================================================================================
// === Static methods
// =================================================================================================

procedure{:ispublic false} AQS_shouldParkAfterFailedAcquire(pred: Node, node: Node) returns (result: boolean)
{
	var pred_dup: Node;
	var s: NodeWaitStatus;
	// var s: int;
	var dummy: boolean;
	var guard : bool;
	
	s := pred.waitStatus;
	if (s == SIGNAL || s == CONDITION)
	// if (s < 0)
	{
		result := True;
	}
	else if (s == CANCELLED)
	// else if (s > 0)
	{
		pred_dup := pred;
		pred_dup := pred_dup.prev;
		node.prev := pred_dup;
		
		guard := (pred_dup.waitStatus == CANCELLED);
		// guard := (pred_dup.waitStatus > 0)
		while (guard)
		{
			pred_dup := pred_dup.prev;
			node.prev := pred_dup;
			
			guard := (pred_dup.waitStatus == CANCELLED);
			// guard := (pred_dup.waitStatus > 0)
		}
		pred_dup.next := node;
		result := False;
	}
	else
	{
		call dummy := AQS_compareAndSetWaitStatus(pred, NO_WAIT_STATUS, SIGNAL);
		// call dummy := AQS_compareAndSetWaitStatus(pred, 0, -1);
		result := False;
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
procedure{:ispublic false} {:isatomic true} AQS_compareAndSetState(this: FairSync, expect: int, update: int) returns (result: boolean)
{
	var guard : bool;
	
	guard := (this.state == expect);
	if (guard)
	{
		this.state := update;
		result := True;
	}
	else
	{
		result := False;
	}
}

// Kivanc note: Again this was a call to unsafe and modeled atomically.
procedure{:ispublic false} {:isatomic true} AQS_compareAndSetHead(this: FairSync, update: Node) returns (result: boolean)
{
	var guard : bool;
	
	guard := (this.head == NULL_NODE);
	if (guard)
	{
		this.head := update;
		result := True;
	}
	else
	{
		result := False;
	}
}

// Kivanc note: Same modeling as casHead()
procedure{:ispublic false} {:isatomic true} AQS_compareAndSetTail(this: FairSync, expect: Node, update: Node) returns (result: boolean)
{
	var guard : bool;
	
	guard := (this.tail == expect);
	if (guard)
	{
		this.tail := update;
		result := True;
	}
	else
	{
		result := False;
	}
}

// Kivanc note: Same as other cas operations.
procedure{:ispublic false} {:isatomic true} AQS_compareAndSetWaitStatus(node: Node, expect: NodeWaitStatus, update: NodeWaitStatus) returns (result: boolean)
// procedure{:ispublic false} {:isatomic true} AQS_compareAndSetWaitStatus(node: Node, expect: int, update: int) returns (result: boolean)
{
	var guard : bool;
	
	guard := (node.waitStatus == expect);
	if (guard)
	{
		node.waitStatus := update;
		result := True;
	}
	else
	{
		result := False;
	}
}

// Kivanc note: same as other cas operations.
procedure {:ispublic false} {:isatomic true} AQS_compareAndSetNext(node: Node, expect: Node, update: Node) returns (result: boolean)
{
	var guard: bool;
	
	guard := (node.next == expect);
	if (guard)
	{
		node.next := update;
		result := True;
	}
	else
	{
		result := False;
	}
}

// =================================================================================================
// === End of FairSync's AQS related methods.
// =================================================================================================

// =================================================================================================
// === Start of FairSync's Sync related methods.
// =================================================================================================

// =================================================================================================
// releases: the value of releasing? (I think this is called with -1 all the time)
// returns true if releasing (completely) is successful, false otherwise.
// Note: This is the method that decides weather the current thread release the lock or not.
// =================================================================================================
procedure {:ispublic false} Sync_tryRelease(this: FairSync, releases: int) returns (result: boolean)
{
	// c hold how many times the lock is locked by the owner thread.
	var c: int;
	var currentThread: Thread;
	var ownerThread: Thread; 
	
	call c := AQS_getState(this);
	c := c - releases;
	call currentThread := Thread_currentThread();
	call ownerThread := AOS_getExclusiveOwnerThread(this);
	
	// if current thread is not the owner of the lock, throw IllegalMonitorException.
	if (currentThread != ownerThread)
	{
		throw IllegalMonitorException;
	}
	
	// else if decrease the number of locks by one, if no lock is left, release the lock
	// completely by setting its owner to null.
	result := False;
	if (c == 0)
	{
		result := True;
		call AOS_setExclusiveOwnerThread(this, NULL_THREAD);
	}
	call AQS_setState(this, c);
}

// =================================================================================================
// === End of FairSync's Sync related methods.
// =================================================================================================


// =================================================================================================
// === Start of FairSync's internal methods.
// =================================================================================================

// =================================================================================================
// acquires: the value of acquiring? (I think this is called with 1 all the time)
// returns true if acquiring is successful, false otherwise.
// Note: This is the method that decides weather the current thread takes (prolongs) 
// the lock or not.
// =================================================================================================
procedure {:ispublic false} FairSync_tryAcquire(this: FairSync, acquires: int) returns (result: boolean)
{
	// current holds currentThread.
	var current: Thread;
	// c is the state of the AQS. (i.e. how many times the lock is acquired by the current thread)
	// for reentrant lock. If c == 0, it means that reentrant lock is unlocked.
	var c: int;
	
	var dummy: boolean;
	var dummyThread: Thread;
	var nextc: int;
	
	call current := Thread_currentThread();
	call c := AQS_getState(this);
	
	// If the lock is unlocked,
	if (c == 0)
	{
		// if current thread is the first thread in the waiting queue (I think this is due
		// to fair sync), and if acquires == 1 (i.e. you want to acquire the lock ?)
		// try to acquire it atomically, if it is a success, return true, else return false.
		call dummy := AQS_isFirst(this, current);
		if (dummy == True)
		{
			call dummy := AQS_compareAndSetState(this, 0, acquires);
			if (dummy == True)
			{
				call AOS_setExclusiveOwnerThread(this, current);
				result := True;
			}
			else
			{
				result := False;
			}
		}
	}
	// If the lock is already locked.
	else
	{
		// check if the current thread is the owner of the lock or not.
		// if it is the owner of the lock, then increase the locking level by 1.
		// return true, or return false otherwise.
		call dummyThread := AOS_getExclusiveOwnerThread(this);
		if (dummyThread == current)
		{
			nextc := c + acquires;
			if (nextc < 0)
			{
				throw Error;
			}
			call AQS_setState(this, nextc);
			result := True;
		}
		else
		{
			result := False;
		}
	}
}

procedure {:ispublic false} FairSync_lock(this: FairSync)
{
	call AQS_acquire(this, 1);
}

// =================================================================================================
// === End of FairSync's internal methods.
// =================================================================================================

// =================================================================================================
// === End of FairSync modeling.
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
procedure {:ispublic false} LockSupport_park(thread: Thread)
{
	var guard: bool;
	
	guard := (thread != NULL_THREAD);
	if (guard)
	{
		atomic 
		{
			guard := (thread.unparked == True);
			if (guard)
			{
				thread.unparked := False;
			}
			else
			{
				thread.parked := True;
				assume (thread.parked == False);
			}
		}
	}
}

// =================================================================================================
// thread: thread to unpark.
// Algorithm: if the thread is previously parked and waiting for an unpark call, set unpark value to
// False.
// else, set the unpark value of this thread to True so that the next park() method will not wait.
// =================================================================================================
procedure {:ispublic false} LockSupport_unpark(thread: Thread)
{
	var guard: bool;
	
	guard := (thread != NULL_THREAD);
	if (guard)
	{
		atomic
		{
			guard := (thread.parked == True);
			if (guard)
			{
				thread.parked := False;
			}
			else
			{
				thread.unparked := True;
			}
			
		}
	}
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
	sync: FairSync;
}

procedure ReentrantLock_ReentrantLock(this: ReentrantLock)
{
	call FairSync_FairSync(this.sync);
}

// =================================================================================================
// === Modeling ReentrantLock internal methods.
// =================================================================================================

procedure ReentrantLock_lock(this: ReentrantLock)
{
	call FairSync_lock(this.sync);
}

procedure ReentrantLock_unlock(this: ReentrantLock)
{
	call AQS_release(this.sync, 1);
}

// =================================================================================================
// === End of modeling ReentrantLock (that uses a fair sync)
// =================================================================================================


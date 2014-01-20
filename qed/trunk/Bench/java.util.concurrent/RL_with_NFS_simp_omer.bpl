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





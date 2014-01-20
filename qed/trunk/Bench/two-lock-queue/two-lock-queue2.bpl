
type Object;

record QueueItem
{
	next: QueueItem;
	value: Object;
}

const unique NULL_OBJECT: Object;
const unique NULL_QUEUE_ITEM: QueueItem;

var head: QueueItem;
var tail: QueueItem;
var headLock: Mutex;
var tailLock: Mutex;

procedure enqueue(value: Object)
{
	var node: QueueItem;
	var t: QueueItem;
	
	call node := NewQueueItem(value);
	
	call lock(tailLock);
		t := tail;
		t.next := node;
		tail := node;
	call unlock(tailLock);
}

procedure dequeue() returns (result: Object)
{
	var x: Object;
	var newHead: QueueItem;
	var node: QueueItem;
	
	call lock(headLock);
		node := head;
		newHead := node.next;
		if (newHead != NULL_QUEUE_ITEM)
		{
			x := newHead.value;
			head := newHead;
			// newHead.value := NULL_OBJECT;
			// Free node;
		} else {
		        x := NULL_OBJECT;
		}
	call unlock(headLock);
	
	result := x;
}


procedure {:ispublic false} NewQueueItem(val: Object) returns (this: QueueItem)
{
	this := New QueueItem;
	this.value := val;
	this.next := NULL_QUEUE_ITEM;
}

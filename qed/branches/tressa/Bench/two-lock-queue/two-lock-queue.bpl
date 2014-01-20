
const unique NULL_OBJECT: Object;
const unique NULL_QUEUE_ITEM: QueueItem;
const unique NULL_TWO_LOCK_QUEUE: TwoLockQueue;

record Object
{
	lock: boolean;
}

record QueueItem
{
	next: QueueItem;
	value: Object;
}

record TwoLockQueue
{
	head: QueueItem;
	tail: QueueItem;
	headLock: Object;
	tailLock: Object;
}

procedure TwoLockQueue_enqueue(this: TwoLockQueue, value: Object)
{
	var x_i: QueueItem;
	var tl: Object;
	var t: QueueItem;
	
	x_i := New QueueItem;
	assume x_i != NULL_QUEUE_ITEM;
	call QueueItem_QueueItem_2(x_i, value);
	
	tl := this.tailLock;
	
	call lock(tl);
		t := this.tail;
		t.next := x_i;
		this.tail := x_i;
	call unlock(tl);
}

procedure TwoLock_dequeue(this: TwoLockQueue) returns (result: Object)
{
	var x_d: Object;
	var hl: Object;
	var node: QueueItem;
	var newHead: QueueItem;
	var h: QueueItem;
	
	hl := this.headLock;
	
	call lock(hl);
		node := this.head;
		h := this.head;
		newHead := h.next;
		if (newHead != NULL_QUEUE_ITEM)
		{
			x_d := newHead.value;
			this.head := newHead;
			newHead.value := NULL_OBJECT;
			// Free node;
		}
	call unlock(hl);
	
	result := x_d;
}

procedure {:ispublic false} {:isatomic true} lock(obj: Object)
{
	assume obj.lock == False;
	obj.lock := True;
}

procedure {:ispublic false} {:isatomic true} unlock(obj: Object)
{
	assert obj.lock == True;
	obj.lock := False;
}

procedure {:ispublic false} QueueItem_QueueItem_2(this: QueueItem, val: Object)
{
	this.next := NULL_QUEUE_ITEM;
	this.value := val;
}

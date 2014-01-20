type Data;

record Object
{
	data: Data;
}

record QueueItem
{
	next: QueueItem;
	value: Object;
}

record NBQueue
{
	Head: QueueItem;
	Tail: QueueItem;
}

const unique NULL_OBJECT: Object;
const unique NULL_QUEUE_ITEM: QueueItem;
const unique NULL_NB_QUEUE: NBQueue;

invariant IsNull(NULL_OBJECT.alloc);
invariant IsNull(NULL_QUEUE_ITEM.alloc);
invariant IsNull(NULL_NB_QUEUE.alloc);

procedure {:isatomic true} {:ispublic false} CAS_tail(queue: NBQueue, expected: QueueItem, newValue: QueueItem) returns (result: bool)
{
	result := (queue.Tail == expected);
	if (result)
	{
		queue.Tail := newValue;
	}
}

procedure {:isatomic true} {:ispublic false} CAS_head(queue: NBQueue, expected: QueueItem, newValue: QueueItem) returns (result: bool)
{
	result := (queue.Head == expected);
	if (result)
	{
		queue.Head := newValue;
	}
}

procedure {:isatomic true} {:ispublic false} CAS_tail_next(queue: NBQueue, expected: QueueItem, newValue: QueueItem) returns (result: bool)
{
	result := (queue.Tail.next == expected);
	if (result)
	{
		queue.Tail.next := newValue;
	}
}

procedure {:ispublic false} CreateQueueItem(val: Object)
returns (this: QueueItem)
{
	this := New QueueItem;
	assume this != NULL_QUEUE_ITEM;
	this.next := NULL_QUEUE_ITEM;
	this.value := val;
}

procedure NBQueue_enqueue(this: NBQueue, value: Object)
{
	var node: QueueItem;
	var tail: QueueItem;
	var n: QueueItem;
	
	var guard: bool;
	
	call node := CreateQueueItem(value);
	
	while (true)
	{
		tail := this.Tail;
		n := tail.next;
		if (tail == this.Tail)
		{
			if (n == NULL_QUEUE_ITEM)
			{
				call guard := CAS_tail_next(this, n, node); 
				if (guard)
				{
					break;
				}
			}
			else
			{
				call guard := CAS_tail(this, tail, n);
			}
		}
	}
	
	call guard := CAS_tail(this, tail, node);
}


procedure NBQueue_dequeue(this: NBQueue) returns (result: Object)
{
	var head: QueueItem;
	var tail: QueueItem;
	var n: QueueItem;
	
	var guard: bool;
	
	result := NULL_OBJECT;
	while (true)
	{
		head := this.Head;
		tail := this.Tail;
		n := head.next;
		
		if (head == this.Head)
		{
			if (head == tail)
			{
				if (n == NULL_QUEUE_ITEM)
				{
					return;
				}
				else
				{
					call guard := CAS_tail(this, tail, n);
				}
			}
			else
			{
				result := n.value;
				call guard :=  CAS_head(this, head, n);
				if(guard)
				{
					return;
				}
			}
		}
		
	}
}



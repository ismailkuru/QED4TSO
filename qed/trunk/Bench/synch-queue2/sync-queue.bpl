type long = int;

type Data;
const unique nulld: Data;

function toData(QNode) returns (Data);
axiom (forall q1,q2: QNode :: q1 != q2 <==> toData(q1) != toData(q2));
axiom toData(nulln) == nulld;

procedure  {:isatomic} park(t: Thread)
{
	// t.parked := True;
	assume true;
}

procedure  {:isatomic} parkNanos(t: Thread, nanos: int)
{
	// t.parked := True;
	assume true;
}

procedure  {:isatomic} unpark(t: Thread)
{
	// t.parked := False;
	assume true;
}

///////////////////////////////////
// Exceptions
///////////////////////////////////

const unique NullPointerException: Exception;
const unique InterruptedException: Exception;

///////////////////////////////////
// Constants
///////////////////////////////////

const maxTimedSpins: int;
axiom maxTimedSpins == 32;

const maxUntimedSpins: int;
axiom maxUntimedSpins == 320;

const spinForTimeoutThreshold: long;
axiom spinForTimeoutThreshold == 1000;

///////////////////////////////////
// QNode
///////////////////////////////////

record QNode
{
	next: QNode;
	item: Data;
	waiter: Thread;
	isData: boolean;
}

const unique nulln: QNode;

procedure createQNode (item: Data, isData: boolean)
returns (qn: QNode)
{
	qn := New QNode;
	assume qn != nulln;
	
	qn.item := item;
	qn.isData := isData;
	qn.next := nulln;
	qn.waiter := NULL_THREAD;
}

procedure  {:isatomic} casNext(this:QNode, cmp: QNode, val: QNode)
returns (r: bool)
{
	r := (this.next == cmp);
	if(r)
	{
		this.next := val;
	}
}

procedure  {:isatomic} casItem(this:QNode, cmp: Data, val: Data)
returns (r: bool)
{
	r := (this.item == cmp);
	if(r)
	{
		this.item := val;
	}
}

procedure  tryCancel(this:QNode, cmp: Data)
{
	var g: bool;
	call g := casItem(this, cmp, toData(this));
}

procedure  isCancelled(this: QNode)
returns (r: bool)
{
	var it: Data;
	
	it := this.item;
	r := (it == toData(this));
}

procedure  isOfflist(this: QNode)
returns (r: bool)
{
	var nx: QNode;
	
	nx := this.next;
	r := (nx == this);
}

///////////////////////////////////
// TransferQueue
///////////////////////////////////

record TransferQueue
{
	head: QNode;
	tail: QNode;
	cleanMe: QNode;
}

procedure CreateTransferQueue ()
returns (tq: TransferQueue)
{
	var qn: QNode;
	
	tq := New TransferQueue;
	call qn := createQNode(nulld, False);
	tq.head := qn;
	tq.tail := qn;
}

procedure  {:isatomic} casHead(this:TransferQueue, h: QNode, nh: QNode)
returns (r: bool)
{
	r := (this.head == h);
	if(r)
	{
		this.head := nh;
	}
}

procedure  {:isatomic} casTail(this:TransferQueue, t: QNode, nt: QNode)
returns (r: bool)
{
	r := (this.tail == t);
	if(r)
	{
		this.tail := nt;
	}
}

procedure  advanceHead(this:TransferQueue, h: QNode, nh: QNode)
{
	var g: bool;
	
	call g := casHead(this, h, nh);
	if(g)
	{
		h.next := h; // forget old head
	}
}

procedure  advanceTail(this:TransferQueue, t: QNode, nt: QNode)
{
	var g: bool;
	call g := casTail(this, t, nt);
}

procedure  {:isatomic} casCleanMe(this:TransferQueue, cmp: QNode, val: QNode)
returns (r: bool)
{
	r := (this.cleanMe == cmp);
	if(r)
	{
		this.cleanMe := val;
	}
}

procedure {:ispublic} transfer(this:TransferQueue, e: Data, timed: bool, nanos: int)
returns (r: Data)
{
	var s: QNode;
	var g: bool;
	var isData: bool;
	var t,h: QNode;
	var tn: QNode;
	var x: Data;
	var m: QNode;
	
	isData := (e != nulld);
	
	while(true)
	{
		t:= this.tail;		// abstract t reaches tail
		h := this.head;		// abstract h reaches head
		
		if(t != nulln && h != nulln)	// local check
		{
			g := ((h == t) || toBool(t.isData) == isData);		// t.isData never changes, right-mover
			if(g)
			{
				tn := t.next;		// t reaches tn
				g := (t == this.tail);		// abstract read
				if(g)
				{
					if(tn != nulln)
					{
						call advanceTail(this, t, tn);		// assert t reaches tn, right-mover
					}
					else
					{
						if(timed && (nanos <= 0))	// local check
						{
							r := nulld;		// local
							return;
						}
						if(s == nulln)		// local check
						{
							call s := createQNode(e, toBoolean(isData));		// right mover
						}
						call g := casNext(t, nulln, s);		// assert t reaches tail
						if(g)
						{
							call advanceTail(this, t, s);	// assert t reaches s
							call x := awaitFulfill(this, s, e, timed, nanos);
							if(x == toData(s))
							{
								// TODO: call clean(this, t, s);
								r := nulld;
								return;
							}
							
							call g := isOfflist(s);		// should be a right mover
							if(!g)
							{
								call advanceHead(this, t, s);		// assert t reaches s
								if(x != nulld)
								{
									s.item := toData(s);	// cancels s, should be right mover
								}
								s.waiter := NULL_THREAD;		// NULL_THREAD never changes, so must be right mover
							}
							if(x != nulld)		// rest is local
							{
								r := x;
							}
							else
							{
								r := e;
							}
							return;
						}
					}
				}
			}
			else	// complementary mode
			{
				m := h.next;		// abstract h reaches m
				g := (t == this.tail && m != nulln);	// abstract read QNode_tail
				g := (g && h == this.head);				// abstract read QNode_head
				if(g)
				{
					x := m.item;		// hoist after, then part should be right-mover
					if((isData == (x != nulld)) || (x == toData(m)))
					{
						call advanceHead(this, h, m);		// assert h reaches m
					}
					else
					{
						call g := casItem(m, x, e);		// hoist after, then must be right-mover
						if(!g)
						{
							call advanceHead(this, h, m);		// assert h reaches m
						}
						else
						{
							call advanceHead(this, h, m); 	// assert h reaches m
							call unpark(m.waiter);
							if(x != nulld)
							{
								r := x;
							}
							else
							{
								r := e;
							}
							return;
						}
					}
				}
			}
		}
	}	
}

procedure awaitFulfill(this:TransferQueue, s: QNode, e: Data, timed: bool, nanos: long)
returns (r: Data)
{
	var lastTime: long;
	var w: Thread;
	var g: bool;
	var x: Data;
	var now: long;
	var spins: int;
	var h: QNode;
	var nanos_: long;
	
	nanos_ := nanos;
	
	if(timed)
	{
		havoc lastTime;
	}
	else
	{
		lastTime := 0;
	}
	
	call w := Thread_currentThread();
	
	h := this.head;			// abstract read
	g := (h.next == s);		// abstract read
	if(g)
	{
		if(timed)
		{
			spins := maxTimedSpins;
		}
		else
		{
			spins := maxUntimedSpins;
		}
	}
	else
	{
		spins := 0;
	}
	
	while(true)
	{
		g := toBool(w.interrupted);
		if(g)
		{
			call tryCancel(s, e);
		}
		x := s.item;		// hoist after and abstract else, then part should be right-mover
		if(x != e)
		{
			r := x;
			return;
		}
		
		g := true;
		if(timed)		// abstract to *
		{
			havoc now;
			nanos_ := nanos_ - (now - lastTime);
			lastTime := now;
			if(nanos_ <= 0)
			{
				call tryCancel(s, e);
				g := false;
			}
			
		}
		if(g) {
			if(spins > 0)
			{
				spins := spins - 1;
			}
			else
			{
				g := (s.waiter == NULL_THREAD);
				if(g)
				{
					s.waiter := w;
				}
				else
				{
					if(!timed)		// abstract to *
					{
						call park(w);
					}
					else
					{
						if(nanos > spinForTimeoutThreshold)
						{
							call parkNanos(w, nanos);
						}
					}
				}
			}
		}
	}
	
}

/*
procedure clean(this:TransferQueue, pred: QNode, s: QNode)
{
	var g: bool;
	var h, hn, t, tn, d, dn, sn, dp: QNode;

	s.waiter := NULL_THREAD;
	
	g := (pred.next == s);
	while(g)
	{
		h := this.head;
		hn := h.next;
		
		call g := isCancelled(hn);
		if(hn != null && g)
		{
			call advanceHead(this, h, hn);
		}
		else
		{
			t := tail;
			if(t == h)
			{
				return;
			}
			tn := t.next;
			g := (t != this.tail);
			if(!g)
			{
				if(tn != nulln)
				{
					call advanceTail(this, t, tn);
				}
				else
				{
					if(s != t)
					{
						sn := s.next;
						if(sn == s)
						{
							return;
						}
						call g := casNext(pred, s, sn)
						if(g)
						{
							return;
						}
					}
					else
					{
						dp := this.cleanMe;
						if(dp != nulln)
						{
							d := dp.next;
							if(d == nulln || d == dp)
							{
								call g := casCleanMe(this, dp, null);
							}
							else
							{
								call g:= isCancelled(d);
								if(!g)
								{
									call g := casCleanMe(this, dp, null);
								}
								else
								{
									
								}
							}
						}
					}
				}
			}
		}
	}
	
}
*/

///////////////////////////////////
// SynchronousQueue
///////////////////////////////////

record SynchronousQueue
{
	transferer: TransferQueue;
}

procedure CreateSynchronousQueue ()
returns (sq: SynchronousQueue)
{
	var tq: TransferQueue;
	
	sq := New SynchronousQueue;
	call tq := CreateTransferQueue();
	sq.transferer := tq;
}


procedure put (this: SynchronousQueue, o: Data)
{
	var e: Data;
	var g: bool;
	
	if(o == nulld)
	{
		throw NullPointerException;
	}
	
	call e := transfer(this.transferer, o, false, 0);
	if(e == nulld)
	{
		call g := Thread_interrupted();
		throw InterruptedException;
	}
}

procedure take (this: SynchronousQueue)
returns (e: Data)
{
	var g: bool;
	
	call e := transfer(this.transferer, nulld, false, 0);
	if(e != nulld)
	{
		return;
	}
	call g:= Thread_interrupted();
	throw InterruptedException;
}


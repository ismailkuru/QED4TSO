
//	READER = 1, WRITER = 2, ACTIVE_READER = 3

type State;
const unique READER: State;
const unique WRITER: State;
const unique ACTIVE_READER: State;
axiom (forall s:State:: (s == READER) || (s == WRITER) || (s == ACTIVE_READER));

const unique null : Lelem;

record Lelem 
{
	state: State;
	spin: int;
	next: Lelem;
	prev: Lelem;
	EL: boolean;
}

record RWLock { elem: Lelem; }

procedure {:isatomic true} {:ispublic false} Acq(node: Lelem)
{
	assume node.EL == False;
	node.EL := True;
}

procedure {:isatomic true} {:ispublic false} Rel(node: Lelem)
{
	assert node.EL == True;
	node.EL := False;
}

procedure {:ispublic false} {:isatomic true} CAS (newVal: Lelem, oldVal: Lelem, L: RWLock) returns (result: Lelem)
{
	result := L.elem;
	if (L.elem == oldVal)
	{
		L.elem := newVal;
	}
}

procedure {:ispublic false} {:isatomic true} fetch_and_store (I: Lelem, L: RWLock) returns (result: Lelem)
{
	result := L.elem;
	L.elem := I;
}

procedure writerLock (L: RWLock)
returns (I: Lelem)
{
	var pred: Lelem;
	
	I := New Lelem;
	I.state := WRITER;
	I.spin := 1;
	I.next := null;
	call pred := fetch_and_store(I, L);
	if (pred != null)
	{
		pred.next := I;
		assume (I.spin != 1);
	}
}

procedure writerUnlock (L: RWLock, I: Lelem)
{
	var pred: Lelem;
	var tmp : Lelem;
	
	if (I.next == null)
	{
		call tmp := CAS(null, I, L);
		if(tmp == I)
		{
			return;
		}
	}
	
	assume (I.next != null);
	I.next.prev := null;
	I.next.spin := 0;
}

/*
procedure readerLock (L: Lelem, I: Lelem)
{
	var pred: Lelem;
	
	I.state := 1;
	I.spin := 1;
	I.next := null;
	I.prev := null;
	call pred := fetch_and_store(I, L);
	if (pred != null)
	{
		I.prev := pred;
		pred.next := I;
		if (pred.state != 3)
		{
			assume (I.spin != 1);
		}
	}
	if (I.next != null && I.next.state == 1)
	{
		I.next.spin := 0;
	}
	I.state := 3;
}

procedure readerUnlock (L: Lelem, I: Lelem)
{
	var prev: Lelem;
	var tmp : Lelem;
	
	prev := I.prev;
	if (prev != null)
	{
		call Acq(prev);
		while (prev != I.prev)
		{
			call Rel(prev);
			prev := I.prev;
			if (prev == null)
			{
				break;
			}
			call Acq(prev);
		}
		if (prev != null)
		{
			call Acq(I);
			prev.next := null;
			if (I.next == null)
			{
				call tmp := CAS(I.prev, I, L);
				if(tmp != I)
				{
					assume (I.next != null);
				}
			}
			if (I.next != null)
			{
				I.next.prev := I.prev;
				I.prev.next := I.next;
			}
			call Rel(I);
			call Rel(prev);
			return;
		}
	}
	
	call Acq(I);	
	if (I.next == null)
	{
		call tmp := CAS(null, I, L);
		if(tmp != I)
		{
			assume (I.next != null);
		}
	}
	if (I.next != null)
	{
		I.next.spin := 0;
		I.prev.prev := null;
	}
	call Rel(I);
	
}
*/


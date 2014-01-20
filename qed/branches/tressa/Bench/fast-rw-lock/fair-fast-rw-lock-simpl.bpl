
//	READER = 1, WRITER = 2, ACTIVE_READER = 3

type State;
const unique READER: State;
const unique WRITER: State;
const unique ACTIVE_READER: State;
axiom (forall s:State:: (s == READER) || (s == WRITER) || (s == ACTIVE_READER));

const unique null : Lelem;
var L: Lelem;

record Lelem 
{
	state: State;
	spin: int;
	next: Lelem;
	prev: Lelem;
	EL: boolean;
}

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

procedure {:ispublic false} {:isatomic true} CAS (newVal: Lelem, oldVal: Lelem) returns (result: Lelem)
{
	result := L;
	if (L == oldVal)
	{
		L := newVal;
	}
}

procedure {:ispublic false} {:isatomic true} fetch_and_store (I: Lelem) returns (result: Lelem)
{
	result := L;
	L := I;
}
/*
procedure writerLock ()
returns (I: Lelem)
{
	var pred: Lelem;
	
	I := New Lelem;
	I.state := WRITER;
	I.spin := 1;
	I.next := null;
	call pred := fetch_and_store(I);
	if (pred != null)
	{
		pred.next := I;
		assume (I.spin != 1);
	}
}

procedure writerUnlock (I: Lelem)
{
	var pred: Lelem;
	var tmp : Lelem;
	
	if (I.next == null)
	{
		call tmp := CAS(null, I);
		if(tmp == I)
		{
			return;
		}
	}
	
	assume (I.next != null);
	I.next.prev := null;
	I.next.spin := 0;
}
*/

procedure readerLock () returns (I: Lelem)
{
	var pred: Lelem;
	var n: Lelem;
	var nextState: State;
	var predState: State;
	
	I := New Lelem;
	I.state := READER;
	I.spin := 1;
	I.next := null;
	I.prev := null;
	call pred := fetch_and_store(I);
	if (pred != null)
	{
		I.prev := pred;
		pred.next := I;
		predState := pred.state;
		if (predState != ACTIVE_READER)
		{
			assume (I.spin == 0);
		}
	}
	n := I.next;
	if (n != null)
	{
		nextState := I.next.state;
		if (nextState == READER)
		{
			I.next.spin := 0;
		}
	}
	I.state := ACTIVE_READER;
}

procedure readerUnlock (I: Lelem)
{
	var p: Lelem;
	var tmp : Lelem;
	var n: Lelem;
	var guard: Lelem;
	var pp: Lelem;
	
	n := I.next;
	p := I.prev;
	
	if (*)
	{
		assume p != null;
		call Acq(p);
		assume p == I.prev;		
		
		if (p != null)
		{
			call Acq(I);
			p.next := null;
			n := I.next;
			if (n == null)
			{
				pp := I.prev;
				call tmp := CAS(pp, I);
				if(tmp != I)
				{
					assume (I.next != null);
				}
			}
			n := I.next;
			if (n != null)
			{
				I.next.prev := I.prev;
				I.prev.next := I.next;
			}
			call Rel(I);
			call Rel(p);
			return;
		}
	} 
	else
	{
		assume p == null;
	}
	
	call Acq(I);	
	n := I.next;
	if (n == null)
	{
		call tmp := CAS(null, I);
		if(tmp != I)
		{
			assume (I.next != null);
		}
	}

	n := I.next;
	if (n != null)
	{
		I.next.spin := 0;
		I.next.prev := null;
	}
	call Rel(I);
	
}
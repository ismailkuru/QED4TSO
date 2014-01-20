/********************************************/
// Exceptions
/********************************************/


/********************************************/
// Atomic Integer
/********************************************/
type AtomicInteger = int;

/********************************************/
// Constants
/********************************************/

// constants
const NCPU: int;
const CAPACITY: int;
const FULL: int;
const SPINS: int;
const TIMED_SPINS: int;

axiom NCPU > 0 && CAPACITY > 0 && FULL > 0 && SPINS > 0 && TIMED_SPINS > 0;

/********************************************/
// Items
/********************************************/

record Object
{
  data: int; // dummy data, not used
}
const unique CANCEL: Object; // not null
const unique NULL_ITEM: Object; // not null

const unique null: Object;
invariant IsNull(null.alloc);

type V = Object; // map generic types to Object

/********************************************/
/* Node */
/********************************************/
record Node // extends AtomicReference
{
  value: Object; // of AtomicReference

  item: Object;
  waiter: Thread;
}

procedure Node(item: Object) returns (n: Node)
{
  n := New Node;
  n.item := item;
}

procedure {:isatomic} compareAndSetItem(n: Node, oldVal: Object, newVal: Object)
returns (r: bool)
{
  r := (n.item == oldVal);
  if(r)
  {
    n.item := newVal;
  }
}

procedure {:isatomic} compareAndSetValue(n: Node, oldVal: Object, newVal: Object)
returns (r: bool)
{
  r := (n.value == oldVal);
  if(r)
  {
    n.value := newVal;
  }
}


/********************************************/
/* Casting between Node and Object */
/********************************************/

function Node2Object(Node) returns (Object);
function Object2Node(Object) returns (Node);
axiom (forall n1,n2: Node :: {Node2Object(n1), Node2Object(n2)} n1 != n2 ==> Node2Object(n1) != Node2Object(n2));
axiom (forall o1,o2: Object :: {Object2Node(o1), Object2Node(o2)} o1 != o2 ==> Object2Node(o1) != Object2Node(o2));
axiom (forall n:Node, o:Object :: {Object2Node(o), Node2Object(n)} Object2Node(o) == n <==> Node2Object(n) == o);


/********************************************/
/* Slot */
/********************************************/

record Slot // extends AtomicReference
{
  value: Object; // of AtomicReference

  q0: long;
  q1: long;
  q2: long;
  q3: long;
  q4: long;
  q5: long;
  q6: long;
  q7: long;
  q8: long;
  q9: long;
  qa: long;
  qb: long;
  qc: long;
  qd: long;
  qe: long;
}

const unique NULL_SLOT: Slot;
invariant IsNull(NULL_SLOT.alloc);

var arena: [int]Slot;
invariant (forall i: int :: (i<0 && CAPACITY<=i) ==> (arena[i] == NULL_SLOT));

var max: AtomicInteger;

procedure Slot()
returns (s: Slot)
{
  s := New Slot;
}

procedure {:isatomic} compareAndSetSlot(s: Slot, oldVal: Object, newVal: Object)
returns (r: bool)
{
  r := (s.value == oldVal);
  if(r)
  {
    s.value := newVal;
  }
}

/********************************************/
// Methods
/********************************************/

procedure {:ispublic} exchange(x: V) returns (v: V)
{
  var g: bool;
  var xx: V;
  
  call g := Thread_interrupted();
  if(!g)
  {
    if(x == null) { xx := NULL_ITEM; } else { xx := x; }
    call  v := doExchange(xx, false, 0);
    if(v == NULL_ITEM)
    {
      v := null;
      return;
    }
    if(v != CANCEL)
    {
      return;
    }
    call g := Thread_interrupted();
  }
  throw InterruptedException;
}

procedure doExchange(item: Object, timed: bool, nanos: int)
returns (o: Object)
{
  var me, you: Node;
  var index: int;
  var y: Object;
  var g: bool;
  var m: int;
  var fails: int;
  var slot: Slot;
  var v: Object;

  call me := Node(item);
  call index := hashIndex();
  fails := 0;

  y := null;

  while(true)
  {
    slot := arena[index];
    if(*)
    {
      assume slot == NULL_SLOT;
      call createSlot(index);
    }
    else
    {
      y := slot.value;
      if(*)
      {
        assume y != null;
	call g := compareAndSetSlot(slot, y, null);
	assume g;
	you := Object2Node(y);
	call g := compareAndSetValue(you, null, item);
	if(*)
	{
	  assume g;
	  // unpark you.waiter
	  o := you.item;
	  return;
	}
      }
      else
      {
	if(*)
      	{
	  assume y == null;
          call g := compareAndSetSlot(slot, null, Node2Object(me));
	  assume g;
	  
	  if(index == 0)
	  {
	    call o := await(me, slot);
	    return;
	  }
	  else
	  {
	    call v := spinWait(me, slot);
	    if(v != CANCEL)
	    {
	      o := v;
	      return;
	    }
	    call me := Node(item);
	    if(*) // try shrinking max
	    {
	      atomic { max := max - 1; }
	    }
	  }	  
	}
	else
	{
	  fails := fails + 1;
	  if(fails > 1)
	  {
	    m := max;
	    if(*)
	    {
	      assume fails > 3 && m < FULL;
	      if(*)
	      {
	        atomic { assume m == max; max := m + 1; }
		index := m + 1;
	      }
	      else
	      {
	        index := index - 1;
		if(index < 0)
		{
		  index := m;
		}
	      }
	    }
	  }
	}
      }

    }
  } // end while(true)

  
} // end of doExchange


procedure await(node: Node, slot: Slot)
returns (v: Object)
{
  var w: Thread;
  var spins: int;
  var g: bool;

  call w := Thread_currentThread();
  spins := SPINS;

  while(true)
  {
    v := node.value;
    if(v != null)
    {
      return;
    }
    else if(spins > 0)
    {
      spins := spins - 1;
    }
    else if(node.waiter == NULL_THREAD)
    {
      node.waiter := w;
    }
    else
    {
      call g:= Thread_nativeIsInterrupted(w, false);
      if(g)
      {
        call tryCancel(node, slot);
      }
      // else park(node)
    }
  }
  
}

procedure spinWait(node: Node, slot: Slot)
returns (v: Object)
{
  var spins: int;

  spins := SPINS;

  while(true)
  {
    v := node.value;
    if(v != null)
    {
      return;
    }
    else if(spins > 0)
    {
      spins := spins - 1;
    }
    else
    {
      call tryCancel(node, slot);
    }
  }
  
}

procedure tryCancel(node: Node, slot: Slot)
{ 
  var g:  bool ;
  
  call g := compareAndSetValue(node, null, CANCEL);
  if(!g)
  {
   return;
  }
  if(slot.value == Node2Object(node))
  {
    call g := compareAndSetSlot(slot, Node2Object(node), null);
  }
}

// abstracted the actual hash computation
procedure {:isatomic} hashIndex()
returns(index: int)
{
  havoc index;
  assume 0 <= index && index < max;
}

procedure createSlot(index: int)
{
  var newSlot: Slot;
  var a: [int]Slot;

  call newSlot := Slot();
  a := arena;

  atomic {
    if(a[index] == NULL_SLOT)
    {
      a[index] := newSlot;
    }
  }
}

record Element {
       data: int;
       next: Element;
}

var Top: Element;
const null: Element;
axiom IsNull(null.alloc);

procedure pop() returns (x: int)
{
	var e: Element;
atomic {
	e := Top;
}

atomic {
	if(e == null) {
	  x := -1;
	} else {
	  Top := Top.next;
	  x := e.data;
	}
}
}

procedure push(x: int) {

	  var e: Element;

atomic {	  
	  e := New Element;
	  e.data := x;
	  e.next := null;
}

atomic {
	  e.next := Top;
}

atomic {
	  Top := e;
}
}
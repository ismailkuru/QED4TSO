
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

	e := Top;
	if(e == null) {
	  x := -1;
	} else {
	  Top := Top.next;
	  x := e.data;
	}
}

procedure push(x: int) {

	  var e: Element;
	  
	  e := New Element;
	  e.data := x;
	  e.next := null;

	  e.next := Top;
	  Top := e;
}
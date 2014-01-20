
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
	var t: Element;
while(true) {
atomic {
        t := Top;
	e := t;
}

atomic {
        if(t != Top) {
	     continue;
	}

	if(e == null) {
	  x := -1;
	} else {
	  Top := Top.next;
	  x := e.data;
	}
}
} // end while
}

procedure push(x: int) {

	var e: Element;
	var t: Element;
atomic {	  
	  e := New Element;
	  e.data := x;
	  e.next := null;
}

while(true) {
atomic {
t := Top;	  
e.next := t;
}

atomic {
          if(t != Top) {
	    continue;
	  }

	  Top := e;
}
} // end while
}

record Node
{
  data: int;
  next: Node;
}

const unique null: Node;
invariant IsNull(null.alloc);
//invariant null.next == null;

var TOP: Node;

const unique EMPTY: int;

type ntype = [Node]Node;
var Htop: [int]Node;
var Hnext: [int]ntype;
var time: int;

invariant TOP.owner == 0 && !IsDealloc(TOP.alloc);

procedure push(v: int)
{
  var timeSeq: [int]int, last: int;
  var t, n: Node;

  atomic {
    havoc timeSeq; // guess all time sequence now

    assume (forall i: int :: {timeSeq[i]} timeSeq[i] <= timeSeq[i+1]);
    last := 0;
  }
  
  n := New Node;
  n.data := v;

  while(true) {

    // t := TOP;		
    atomic {
      assume last >= 0;
      assume timeSeq[last] <= time;
      t := Htop[timeSeq[last]];
      last := last + 1;
    }

    // n.next := t;
    atomic {
      assert n.owner == tid;
      n.next := t;
    }

    // CAS
    atomic {
      assert IsAlloc(n.alloc) && n.owner == tid;
      if(TOP == t) {
	time := time + 1;
	Hnext[time] := Hnext[time-1];
        Htop[time] := n;
	TOP := n;

	n.owner := 0;
	
        break;
      }
    }

  } // while
}

procedure pop()
returns (v: int)
{
  var timeSeq: [int]int, last: int;
  var t, n: Node;

  atomic {
    havoc timeSeq; // guess all time sequence now

    assume (forall i: int :: {timeSeq[i]} timeSeq[i] <= timeSeq[i+1]);
    last := 0;
  }

  while(true)
  {

    // t := TOP;		
    atomic {
      assume last >= 0;
      assume timeSeq[last] <= time;
      t := Htop[timeSeq[last]];
      last := last + 1;
    }		

    if(t == null)
    {
      v := EMPTY;
      return;
    }

    // n := t.next;
    atomic {
      assert IsAlloc(t.alloc);
      assert t.owner == 0;
      assume last >= 0;
      assume timeSeq[last] <= time;
      n := Hnext[timeSeq[last]][t];
      last := last + 1;
    }	

    // CAS
    atomic {
      assert !IsDealloc(n.alloc) && n.owner == 0;
      if(TOP == t) {
	time := time + 1;
	Hnext[time] := Hnext[time-1];
        Htop[time] := n;
	TOP := n;
	
        break;
      }
    }
	
  } // while

  v := t.data;
}
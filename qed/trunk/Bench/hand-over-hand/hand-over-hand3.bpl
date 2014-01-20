
procedure {:isatomic true} {:ispublic false} Acq(node: Node)
{
	assume node.lock == False;
 	assume node.owner == 0;
	node.lock := True;
 	node.owner := tid;
}

procedure {:isatomic true} {:ispublic false} Rel(node: Node)
{
	assert node.owner==tid;
	assert node.lock == True;
	node.lock := False;
	node.owner := 0;
}

type Data = int;
record Node { next: Node; val: Data; lock: boolean; }

const unique null : Node;
invariant IsNull(null.alloc);

record List { head: Node; }
invariant (forall list:List :: {List_head[list]} list.head  != null);



procedure Delete(list : List, x : Data) returns (wasPresent: bool)
{
	var p:Node;
	var n:Node;
	var t:Node;

        p := list.head;
        call Acq(p);
     	while (*) {
	      atomic{
	      assert p!=null && p.owner==tid && p.alloc==Alloc;
 	      n := p.next;
	      }
	      atomic {
	      assert n==null || n.alloc==Alloc;
              assume n!=null && n.val<x;
	      }
	      call Acq(n);
	      call Rel(p);
	      p := n;
	}

	atomic {
	assert p.owner==tid;
	assert p!=null && p.alloc==Alloc;
	n := p.next;
	}
	atomic {
	assert n==null || n.alloc==Alloc;
	assume n==null || n.val>=x;
	}

	if(*)
	{
		atomic {
		assert n==null || n.alloc==Alloc;
		assume n!=null && n.val==x;
		}
		call Acq(n);
		p.next := n.next;
		call Rel(n);
		wasPresent := true;
	} else {
	        atomic {
		assert n==null || n.alloc==Alloc;
	        assume n==null || n.val!=x;
		}
		wasPresent := false;
	}

	call Rel(p);
	//Free n;
}



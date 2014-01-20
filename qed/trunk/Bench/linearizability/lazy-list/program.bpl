record Node {
key: int;
next: Node;
marked: boolean;
alloc: AllocType;
owner: TID;
}

type nextType = [Node]Node;

type keyType = [Node]int;

type markedType = [Node]boolean;

type allocType = [Node]AllocType;

var Hnext: [int]nextType;

var Hmarked: [int]markedType;

var Halloc: [int]allocType;

var Hcount: int;

const unique null: Node;

const unique Head: Node;

const unique Tail: Node;

const E: int;

axiom MIN_INT < E && E < MAX_INT;

procedure contains(e: int) returns (wasPresent: bool);



implementation contains(e: int) returns (wasPresent: bool)
{
  var pred: Node;
  var curr: Node;
  var qseq: [int]int;
  var qcount: int;
  var ex: Exception;

  Atomic_1:
    atomic  {  // Non-mover
        assume e == E;
        havoc qseq, qcount, pred, curr;
        assume 1 <= qcount;
        assume (forall i: int :: { qseq[i] } 1 <= i && i <= qcount ==> 0 <= qseq[i] && qseq[i] <= Hcount);
        assume (forall i: int, j: int :: { qseq[i], qseq[j] } 1 <= i && i <= j && j <= qcount ==> qseq[i] <= qseq[j]);
        assume (exists m:Node :: m.key == e && ReachBetweenSet(Hnext[qseq[qcount]], curr, Tail)[m] && (forall i: int :: { qseq[i] } 1 <= i && i <= qcount ==> Hmarked[qseq[i]][m] == False && ReachBetweenSet(Hnext[qseq[i]], Head, Tail)[m]));
        assume curr.key <= e;
    }

    while (*)
    {
      Atomic_10:
        atomic  {  // Non-mover
            assume curr.key < e;
            assume e == E;
            assert 1 <= qcount;
            assert 0 <= qseq[qcount] && qseq[qcount] <= Hcount;
            assert (exists m:Node :: m.key == e && Hmarked[qseq[qcount]][m] == False && ReachBetweenSet(Hnext[qseq[qcount]], Head, Tail)[m] && ReachBetweenSet(Hnext[qseq[qcount]], curr, Tail)[m]);
            pred := curr;
            assume qseq[qcount] <= qseq[qcount + 1] && qseq[qcount + 1] <= Hcount;
            qcount := qcount + 1;
            curr := Hnext[qseq[qcount]][pred];
            assert (exists m:Node :: m.key == e && Hmarked[qseq[qcount]][m] == False && ReachBetweenSet(Hnext[qseq[qcount]], Head, Tail)[m] && ReachBetweenSet(Hnext[qseq[qcount]], curr, Tail)[m]);
	    assert curr.key <= e;
        }
    }

  Atomic_22:
    atomic  {  // Non-mover
        assume curr.key >= e;
        assume e == E;
        wasPresent := curr.key == e && curr.marked == False;
        assert wasPresent <==> true;
    }
}



procedure add(e: int) returns (wasPresent: bool);
  modifies Node_alloc, Node_marked, Node_next;



implementation add(e: int) returns (wasPresent: bool)
{
  var pred: Node;
  var curr: Node;
  var tmp: Node;
  var ex: Exception;

    while (true)
    {
      Atomic_26:
        atomic  {  // Non-mover
            assume MIN_INT < e && e < MAX_INT;
            assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, pred, Tail)[Tail];
            assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, curr, Tail)[Tail];
            assert pred == Head || !ReachBetweenSet(Node_next, pred, Head)[Head];
            assert !ReachBetweenSet(Node_next, curr, Head)[Head];
            assert pred != Tail && curr != Head;
            assert pred.key < e && e <= curr.key;
            assume Hnext[Hcount] == Node_next;
            assume Hmarked[Hcount] == Node_marked;
            assume Halloc[Hcount] == Node_alloc;
            if (pred.next == curr && pred.marked == False)
            {
                wasPresent := curr.key == e;
                assume e == E ==> wasPresent;
                if (!wasPresent)
                {
                    tmp := New Node;
                    tmp.marked := False;
                    assume tmp.key == e;
                    tmp.next := curr;
                    pred.next := tmp;
                    Hcount := Hcount + 1;
                    Hnext[Hcount] := Node_next;
                    Hmarked[Hcount] := Node_marked;
                    Halloc[Hcount] := Node_alloc;
                }

                return;
            }
        }
    }
}



procedure remove(e: int) returns (wasPresent: bool);
  modifies Node_marked, Node_next;



implementation remove(e: int) returns (wasPresent: bool)
{
  var pred: Node;
  var curr: Node;
  var ex: Exception;

    while (true)
    {
      Atomic_28:
        atomic  {  // Non-mover
            assume MIN_INT < e && e < MAX_INT;
            assert IsAlloc(pred.alloc) && ReachBetweenSet(Node_next, pred, Tail)[Tail];
            assert IsAlloc(curr.alloc) && ReachBetweenSet(Node_next, curr, Tail)[Tail];
            assert pred == Head || !ReachBetweenSet(Node_next, pred, Head)[Head];
            assert !ReachBetweenSet(Node_next, curr, Head)[Head];
            assert pred != Tail && curr != Head;
            assert pred.key < e && e <= curr.key;
            assume Hnext[Hcount] == Node_next;
            assume Hmarked[Hcount] == Node_marked;
            assume Halloc[Hcount] == Node_alloc;
            if (pred.next == curr && pred.marked == False)
            {
                wasPresent := curr.key == e;
                assume wasPresent ==> e != E;
                if (wasPresent)
                {
                    curr.marked := True;
                    pred.next := curr.next;
                    Hcount := Hcount + 1;
                    Hnext[Hcount] := Node_next;
                    Hmarked[Hcount] := Node_marked;
                    Halloc[Hcount] := Node_alloc;
                }

                return;
            }
        }
    }
}



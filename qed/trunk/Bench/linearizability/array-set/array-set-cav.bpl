type KeySpace = int;

/*
record Location {
       key: KeySpace;
       gen: int;
}
*/

const unique null: KeySpace;
axiom null == 0;

var length: int;

type keyType = [int]KeySpace;
type genType = [int]int;
var key: keyType;
var gen: genType;
var Hkey: [int]keyType;
var Hgen: [int]genType;
var time: int;

procedure Member(x: KeySpace) returns (r: bool)
{
  var mylength, i: int;
  var v: KeySpace;
  var timeSeq: [int]int, last: int;
  
  atomic {
    havoc timeSeq; // guess all time sequence now

    assume (forall k: int :: {timeSeq[k]} timeSeq[k] <= timeSeq[k+1]);
    last := 0;
  }

  assume x > 0;

  i := 0;
  mylength := length;
  while(i < mylength) {
    while(i != mylength) {
      i := i + 1;

      atomic {
        // v := key[i];
	assume last >= 0;
	assume timeSeq[last] <= time;
      	v := Hkey[timeSeq[last]][i];
      	last := last + 1;
      }

      if(v == x) {
        r := true;
        return;
      }
    }
    mylength := length;
  }
  r := false;
  return;
}

procedure Insert(x: KeySpace)
{
  var mylength, i: int;
  var added: bool;
  var holes: [int]int;
  var nholes: int;
  var v: KeySpace;

  assume x > 0;

  added := false;
  nholes := 0;

  mylength := length;
  i := 1;
  while(i <= mylength) {
    v := key[i];
    if(v == null) { 
      nholes := nholes + 1;
      holes[nholes] := i;
    }
    i := i + 1;
  }

  while(!added && nholes > 0) {
    atomic {
      added := (key[holes[nholes]] == null);
      if(added) {
        atomic {
	  key[holes[nholes]] := x;
	  time := time + 1;
	  Hkey[time] := Hkey[time-1][holes[nholes] := x];
	  Hgen[time] := Hgen[time-1];
	}
      }
    }
    nholes := nholes - 1;
  }

  while(!added) {
    atomic {
      length := length + 1;
      i := length;
    }
    atomic {
      added := (key[i] == null);
      if(added) {
        atomic {
	  key[i] := x;
	  time := time + 1;
	  Hkey[time] := Hkey[time-1][i := x];
	}
      }
    }
  }
  assert added;
}

procedure Delete(x: KeySpace)
{
  var mylength, i: int;
  var todo: [int]int;
  var mygen: [int]int;
  var ntodo: int;
  var removed: bool;
  var v: KeySpace;
  var g: int;

  assume x > 0;

  ntodo := 0;

  mylength := length;
  i := 1;
  while(i <= mylength) {
    g := gen[i];
    v := key[i];
    if(v == null) { 
      ntodo := ntodo + 1;
      todo[ntodo] := i;
      mygen[ntodo] := g;
    }
    i := i + 1;
  }

  i := 0;
  while(i <= ntodo) {
    atomic {
      removed := (gen[todo[i]] == mygen[i]);
      if(removed) {
	atomic {
	  key[todo[i]] := null;
	  time := time + 1;
	  Hkey[time] := Hkey[time-1][todo[i] := null];
	  Hgen[time] := Hgen[time-1];
	}
	atomic {
	  gen[todo[i]] := gen[todo[i]] + 1;
	  time := time + 1;
	  Hkey[time] := Hkey[time-1];
	  Hgen[time] := Hgen[time-1];
	  Hgen[time][todo[i]] := Hgen[time][todo[i]] + 1;
	}
      }
    }
    i := i + 1;
  }

  assert removed;
}
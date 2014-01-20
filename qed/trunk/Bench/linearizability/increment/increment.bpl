

/************* Original
var x: int;

procedure inc() {
  var t,k: int;  

  while(true) {
    t := x;
    k := t + 1;
    
    atomic {
      if(x == t) {
      	   x := k;
           break;
      }
    }
  } // end while
}
*************/

var time: int; // current time
var Hx: [int]int; // history of writes to x (maps time to value)
invariant time >= 0;

procedure inc() {
  var t,k: int;  
  var timeSeq: [int]int, last: int;
  var myx: int; // my view of x
  
  atomic {
    havoc timeSeq; // guess all time sequence now
    assume (forall i: int :: {timeSeq[i]} timeSeq[i] <= timeSeq[i+1]);
    last := 0;
  }

  while(true) {
    atomic {
      // begin read x
      assume last >= 0;
      assume timeSeq[last] <= time;
      myx := Hx[timeSeq[last]];
      last := last + 1;
     // end read x

      t := myx;
    }
    k := t + 1;
    
    atomic {
      // begin read x
      assume last >= 0;
      assume timeSeq[last] == time;
      myx := Hx[timeSeq[last]];
      last := last + 1;
     // end read x

      if(myx == t) {
           // begin write x
      	   time := time + 1;
      	   Hx[time] := k;
     	   // end write x
           break;
      }
    }
  } // end while
}

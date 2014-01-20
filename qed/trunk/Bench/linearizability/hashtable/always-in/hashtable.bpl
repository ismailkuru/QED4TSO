
type Address;
type EValue;

// ADR function
function ADR(EValue) returns (Address);
axiom (forall v, w: EValue :: {ADR(v), ADR(w)} v != w ==> ADR(v) != ADR(w));

// old functions
function isold(EValue) returns (bool);
function makeold(EValue) returns (EValue);
axiom (forall v: EValue :: {makeold(v)} isold(makeold(v)) == true);
axiom (forall v,w: EValue :: {makeold(v),makeold(w)} v != null && v != del && w != null && w != del && v != w ==> makeold(v) != makeold(w));

const null: EValue;
const del: EValue;
const done: EValue;
axiom (makeold(null) == done && makeold(del) == done);
axiom (isold(done) == true); // already implied

const P: TID; // number of processes
axiom P == Tid;

// hashing function
function key(Address, int, int) returns (int);
axiom (forall a: Address, l: int, n: int :: {key(a,l,n)} 0 <= key(a,l,n) && key(a,l,n) < l);
axiom (forall a: Address, l: int, k: int, m: int :: {key(a,l,k), key(a,l,m)} 0 <= k && k < m && m < l ==> key(a,l,k) != key(a,l,m));

record Hashtable {
  size: int;
  bound: int;
  occ: int;
  dels: int;
  table: [int]EValue;
}

var currInd: int;
const H: [int]Hashtable;
var prot: [int]int; 
var busy: [int]int;
const next: [int]int;

axiom (forall i,j:int :: {H[i],H[j]} i != j ==> H[i] != H[j]);
axiom (forall i:int :: {next[i]} i != next[i]);
axiom (forall i,j:int :: {next[i],next[j]} i != j ==> next[i] != next[j]);

invariant (forall i: int :: {busy[i]}{prot[i]} busy[i] >= 0 && prot[i] >= 0);
procedure inc_busy(i: int)
{
inc_busy: atomic { busy[i] := busy[i] + 1; }
}
procedure dec_busy(i: int)
{
dec_busy: atomic { assert busy[i] >= 1; busy[i] := busy[i] - 1; }
}
procedure inc_prot(i: int)
{
inc_prot: atomic { prot[i] := prot[i] + 1; }
}
procedure dec_prot(i: int)
{
dec_prot: atomic { assert prot[i] >= 1; prot[i] := prot[i] - 1; }
}

procedure find(a: Address) returns (r: EValue)
{
  var n,l: int;
  var h: Hashtable;

  h := H[currInd];
  n := 0;
  l := h.size;
  r := null;
  while(true) {
    r := h.table[key(a, l, n)];

    assume r != makeold(del) && r != makeold(null);

    atomic { n := n + 1; }

    if(r == null || a == ADR(r)) { break; }
  }

}

procedure delete(a: Address) returns (suc: bool)
{
  var r: EValue;
  var k, n,l: int;
  var h: Hashtable;

  h := H[currInd];
  suc := false;
  n := 0;
  l := h.size;

  while(true) {
    k := key(a, l, n);
    r := h.table[k];
  
    assume !isold(r);
 
    if(a == ADR(r)) {
      atomic {
        if(r == h.table[k]) {
	  h.table[k] := del;
	  suc := true;
	}
      } 
    } else {
       atomic { n := n + 1; }
    }
    
    if(suc == true || r == null) { break; }
  }

  if(suc == true) { atomic { h.dels := h.dels + 1; } }

}

procedure insert(v: EValue) returns (suc: bool)
{
  var r: EValue;
  var k, n,l: int;
  var a: Address;
  var h: Hashtable;

  h := H[currInd];
  suc := false;
  n := 0;
  l := h.size;
  a := ADR(v);

  while(true) {
    k := key(a, l, n);
    r := h.table[k];

    assume !isold(r);
   
    if(r == null) {
      atomic {
        if(r == h.table[k]) {
	  h.table[k] := v;
	  suc := true;
	}
      } 
    } else {
       atomic { n := n + 1; }
    }
    
    if(suc == true || a == ADR(r)) { break; }
  }

  if(suc == true) { atomic { h.occ := h.occ + 1; } }

}


procedure migrate()
{
  var i: int;
  var h: Hashtable;
  var g: bool;
  var v: EValue;
  var from, to: Hashtable;
  var move: int;
  var a: Address;
  var k,m,n: int;
  var w: EValue;
  var b: bool;
  var index: int;

  index := currInd;

  // begin newTable
  atomic {
    havoc i;
    assume i > 0;
    assume next[index] == i;

    assume prot[i] == 0;
    prot[i] := 1;
  }
  atomic { 
    assume busy[i] == 0;
    busy[i] := 1;
  }
  // end newTable

  // i := next[index];
  // assume i > 0; // this was set before

  call inc_prot(i);

  if(index != currInd) {
    call dec_prot(i);
  } else {
    call inc_busy(i);
    h := H[i];
    if(index == currInd) {
      from := H[index];
      to := h;
      // begin moveContents(H[index],h)
      while(currInd == index) {
	havoc move;
	assume move >= 0;	

        v := from.table[move];
	assume !isold(v);
	assume v != makeold(del) && v != makeold(null);

	atomic {
	  g := v == from.table[move];
	  if(g) {
	    from.table[move] := makeold(v);
	  }
	}
	if(g) {
	  if(v != null) {
	    // begin moveElement(v, to)
	    a := ADR(v);
	    m := to.size;
	    n := 0;
	    b := false;
	    while(true) {
	      k := key(a, m, n);
	      w := to.table[k];
	      if(w == null) {
	        atomic {
		  if(to.table[k] == null) {
		    to.table[k] := v;
		    b := true;
		  }
		}
	      }
	      if(b == true || a == ADR(w) || currInd != index) { break; }
	    }
	    if(b == true) {
	      atomic { to.occ := to.occ + 1; }
	    }
	    // end moveElement 
	    from.table[move] := done;
	  }
	}
      }
      // end moveContents      
      atomic {
        g := index == currInd;
	if(g) {
	  currInd := i;
	}
      }
      if(g) {
          call dec_busy(index);
          call dec_prot(index);
      }
    }
  }
}
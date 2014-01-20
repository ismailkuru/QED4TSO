var Aval : [int]int;
var Actr : [int]int;
const MAX : int;
const RN : int, LN : int;

procedure {:atomic true} {:ispublic false} oracle_right() returns (r : int);
	  ensures 0 < r && r <= MAX+1;
	  ensures (forall x : int :: r <= x ==> Aval[x] == RN);

procedure {:atomic true} {:ispublic false} oracle_left() returns (r : int);
	  ensures 0 <= r && r <= MAX;
	  ensures (forall x : int :: x <= r ==> Aval[x] == LN);


procedure {:atomic true} {:ispublic false} cas(i : int, old_val : int, old_ctr : int, val : int, ctr : int) returns (r : bool);
	  requires 0 <= i && i <= MAX+1;
	  ensures (r == false && (forall x : int :: Aval[x] == old(Aval[x]) && Actr[x] == old(Actr[x])))
	  	  ||
		  (r == true && (forall x : int :: ((x == i) && old(Aval[x]) == old_val && old(Actr[x]) == old_ctr && Aval[x] == val && Actr[x] == ctr) || (Aval[x] == old(Aval[x]) && Actr[x] == old(Actr[x]))));
	  modifies Aval, Actr;

procedure {:atomic false} {:ispublic true} rightpush(v : int) returns (r : bool)
	  modifies Aval, Actr;
{
	var k : int;
	var prev_val : int, prev_ctr : int, cur_val : int, cur_ctr : int;
	var cas_prev : bool, cas_cur : bool;

	while (true) {
		    call k := oracle_right();
		    prev_val := Aval[k-1];
		    prev_ctr := Actr[k-1];
		    cur_val := Aval[k];
		    cur_ctr := Actr[k];
		    
		    if (prev_val != RN && cur_val == RN) {
		       if (k == MAX+1) {
		       	  r := false;
			  return;
		       }
		       call cas_prev := cas(k-1, prev_val, prev_ctr, prev_val, prev_ctr+1);		       
		       if(cas_prev) {
		       		    call cas_cur := cas(k, cur_val, cur_ctr, cur_val, cur_ctr+1);
				    if(cas_cur) {
				    		r := true;
						return;
				    }		       
		       		    
		       }
		    }
	}
}


procedure {:atomic false} {:ispublic true} rightpop() returns (v : int, r : bool)
	  modifies Aval, Actr;
{
	var k : int;
	var next_val : int, next_ctr : int, cur_val : int, cur_ctr : int;
	var cas_next : bool, cas_cur : bool;

	while (true) {
		    call k := oracle_right();
		    cur_val := Aval[k-1];
		    cur_ctr := Actr[k-1];
		    next_val := Aval[k];
		    next_ctr := Actr[k];
		    
		    if (cur_val != RN && next_val == RN) {
		       if (cur_val == LN && Aval[k-1] == cur_val && Actr[k-1] == cur_ctr) {
		       	  r := false;
			  return;
		       }
		       call cas_next := cas(k, next_val, next_ctr, RN, next_ctr+1);		       
		       if(cas_next) {
		       		    call cas_cur := cas(k-1, cur_val, cur_ctr, RN, cur_ctr+1);
				    if(cas_cur) {
				    		v := cur_val;
				    		r := true;
						return;
				    }		       
		       		    
		       }
		    }
	}
}

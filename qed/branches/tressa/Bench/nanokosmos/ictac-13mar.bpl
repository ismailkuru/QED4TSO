const unique tid: int;
// var Tid: int;

var Mem_own: [int]int;
var Mem_ver: [int]int;
var Mem_val: [int]int;

var rlog_addr: [int,int]int;
var rlog_ver: [int,int]int;
var rIdx: [int]int;

var wlog_addr: [int,int]int;
var wlog_oldv: [int,int]int;
var wIdx: [int]int;

// var blocked: [int,int]bool;
var blocked: [int][int]bool;
var auxStart: [int,int]int;

procedure OpenForRead(a: int)
 returns ()
 modifies rlog_ver, rlog_addr, rIdx;
{
	var nd_ver: int;
	rlog_addr[tid,rIdx[tid]] := a;
	atomic {
		assert a==rlog_addr[tid,rIdx[tid]];
		havoc nd_ver;
		assume nd_ver<=Mem_ver[a];
		rlog_ver[tid,rIdx[tid]] := nd_ver;
	}
	rIdx[tid] := rIdx[tid]+1;
}

procedure TxRead(a: int) 
 returns (v: int)
 modifies auxStart;
{
	var firstRead: bool;
	var nd_val: int;
	var flat_block: [int]bool;
	
	atomic {
		assert rlog_addr[tid,rIdx[tid]-1]==a &&
		       rlog_ver[tid,rIdx[tid]-1]<=Mem_ver[a];
		flat_block := blocked[a];
		if (flat_block[tid]) {
			if ((Mem_own[a]==0 || Mem_own[a]==tid) &&
			    (Mem_ver[a]==rlog_ver[tid,rIdx[tid]-1])) {
				v := Mem_val[a];
				havoc firstRead;
				assume firstRead == (forall j:int :: (j<rIdx[tid]-1 ==> rlog_addr[tid,j]!=a) &&
				                                      (j<wIdx[tid] ==> wlog_addr[tid,j]!=a));
				if (firstRead) { auxStart[tid,a] := v; }
			} else { havoc v; havoc nd_val; auxStart[tid,a] := nd_val; havoc firstRead; }
		} else { havoc v; havoc nd_val; auxStart[tid,a] := nd_val; havoc firstRead; }
		havoc flat_block;
	}
}

procedure OpenForWrite(addr: int) 
 returns (success: bool)
 modifies wlog_addr, wlog_oldv, wIdx, Mem_own, blocked;
{
	var blkmirror: [int]bool;
	var flat_block: [int]bool;
  if (*) {
		atomic {
			flat_block := blocked[addr];
			havoc blkmirror;
			// assume (forall t:int, addr:int :: (addr==a && t!=tid) || (blkmirror[t,addr]==blocked[t,addr]));
			assume blkmirror[tid]==flat_block[tid];
			assume (forall t:int :: t!=tid ==> (flat_block[t]==false));
			assume Mem_own[addr]==0 || Mem_own[addr]==tid;
		  Mem_own[addr] := tid; 
			blocked[addr] := blkmirror;
			havoc blkmirror, flat_block;
		}
		flat_block := blocked[addr];
		if (flat_block[tid]) {	success := true; }
		else { success := false; }
		havoc flat_block;
    wlog_addr[tid,wIdx[tid]] := addr;
		atomic {
			assert Mem_own[addr]==tid;
			wlog_oldv[tid,wIdx[tid]] := Mem_val[addr];
		}
		wIdx[tid] := wIdx[tid]+1;
	} else {
/*		atomic {
			assume Mem_own[addr]!=0 && Mem_own[addr]!=tid;
		} */
		success := false;
	}
}

/* procedure TxWrite(a: int, v: int)
 returns ()
 modifies Mem_val;
{
	atomic {
		assert Mem_own[a]==tid;
		Mem_val[a] := v;
	}
} */

procedure ValidateRead(a: int, index: int) 
 returns (success: bool)
 modifies blocked;
{
	var nd_blk: bool;
	var flat_block: [int]bool;
  atomic {
		assert rlog_ver[tid,index]<=Mem_ver[a];
		if (*) { success := false; }
		else {
			success := true;
			assume (Mem_ver[a]==rlog_ver[tid,index]) && 
						 (Mem_own[a]==0 || Mem_own[a]==tid);
			flat_block := blocked[a];
			assume flat_block[tid];
			havoc nd_blk;
			flat_block[tid] := nd_blk;
			blocked[a] := flat_block;
			havoc flat_block;
		}
	}
}

procedure CloseUpdate(a: int)
 returns ()
 modifies Mem_ver, Mem_own;
{
  if (Mem_own[a]==tid) {
		atomic {
			assert Mem_own[a]==tid;
			Mem_ver[a] := Mem_ver[a]+1; Mem_own[a] := 0;
		}
  }
}

procedure ValidateReads() 
 returns (success: bool)
 modifies blocked;
{
  var i, addr: int;
	var validated: bool;
  i := 0;
  while (i<rIdx[tid]) {
    addr := rlog_addr[tid,i];
		call validated := ValidateRead(addr,i);
    if (!validated) {
      success := false;
      i := rIdx[tid];
    }
    i := i+1;
  }
  success := true;
}

procedure UndoUpdates()
 returns ()
 modifies Mem_val, blocked;
{
  var i: int;
  var addr, oldValue: int;
	var blkmirror: [int]bool;
	var flat_block: [int]bool;
	var lastwrite: [int]bool;
	
  i := wIdx[tid];
  while (i>0) {
    i := i-1;
    addr := wlog_addr[tid,i];
    oldValue := wlog_oldv[tid,i];
		atomic {
			assert Mem_own[addr]==tid;
			flat_block := blocked[addr];
			havoc blkmirror;
			assume blkmirror[tid]==flat_block[tid];
			assume (forall t:int :: t!=tid ==> !flat_block[t]);
			Mem_val[addr] := oldValue;
			blocked[addr] := blkmirror;
			havoc blkmirror, flat_block;
		}
  }
}

procedure CloseUpdates()
 returns ()
 modifies Mem_ver, Mem_own;
{
  var i: int;
  var addr: int;
  i := 0;
  while (i<wIdx[tid]) {
    addr := wlog_addr[tid,i];
    call CloseUpdate(addr);
    i := i+1;
  }
}

procedure Transact() 
 returns (success: bool)
 modifies Mem_own, Mem_val, Mem_ver, rlog_addr, rlog_ver, rIdx, 
  wlog_addr, wlog_oldv, wIdx, auxStart, blocked;
{
	var i, val: int;
	var actionList_addr: [int]int;
	var actionList_val: [int]int;
	var actionCnt: int;

  success := true;
	rIdx[tid] := 0; wIdx[tid] := 0;
	havoc actionCnt, actionList_val, actionList_addr;
	i := 0;

  while (success && i<actionCnt) {
    if (actionList_val[i]==0) {
      call OpenForRead(actionList_addr[i]);
			call val := TxRead(actionList_addr[i]);
    } else {
      call success := OpenForWrite(actionList_addr[i]);
      if (success) { 
//			call TxWrite(actionList_addr[i], actionList_val[i]);	
				atomic {
					assert Mem_own[actionList_addr[i]]==tid;
					Mem_val[actionList_addr[i]] := actionList_val[i];
				}
			}	
		}
		i := i+1;
  }

  if (success) { call success := ValidateReads(); }
  if (!success) { call UndoUpdates(); }
  call CloseUpdates();
}



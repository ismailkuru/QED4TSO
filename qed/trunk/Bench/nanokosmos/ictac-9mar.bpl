const unique tid: int;

var Mem_own: [int]int;
var Mem_ver: [int]int;
var Mem_val: [int]int;

var rlog_addr: [int,int]int;
var rlog_ver: [int,int]int;
var rIdx: [int]int;

var wlog_addr: [int,int]int;
var wlog_oldv: [int,int]int;
var wIdx: [int]int;

procedure OpenForRead(a: int)
 returns ()
 modifies rlog_ver, rlog_addr, rIdx;
{
	rlog_ver[tid,rIdx[tid]] := Mem_ver[a];
	rlog_addr[tid,rIdx[tid]] := a;
	rIdx[tid] := rIdx[tid]+1;
}

procedure TxRead(a: int) 
 returns (v: int)
{
	v := Mem_val[a];
}

procedure OpenForWrite(a: int) 
 returns (success: bool)
 modifies wlog_addr, wlog_oldv, wIdx, Mem_own;
{
  if (*) {
		atomic {
			assume Mem_own[a]==0 || Mem_own[a]==tid;
		  Mem_own[a] := tid; 
		}
		success := true;
    wlog_addr[tid,wIdx[tid]] := a;
		wlog_oldv[tid,wIdx[tid]] := Mem_val[a];
		wIdx[tid] := wIdx[tid]+1;
	} else {
		atomic {
			assume Mem_own[a]!=0 && Mem_own[a]!=tid;
		}
		success := false;
	}
}

procedure TxWrite(a: int, v: int)
 returns ()
 modifies Mem_val;
{
	Mem_val[a] := v;
}

procedure ValidateRead(a: int, index: int) 
 returns (success: bool)
{
  atomic {
		success :=  
      (Mem_ver[a]==rlog_ver[tid,index]) && 
      (Mem_own[a]==0 || Mem_own[a]==tid);
	}
}

procedure CloseUpdate(a: int)
 returns ()
 modifies Mem_ver, Mem_own;
{
  if (Mem_own[a]==tid) {
		atomic {
			Mem_ver[a] := Mem_ver[a]+1; Mem_own[a] := 0;
		}
  }
}

procedure ValidateReads() 
 returns (success: bool)
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
 modifies Mem_val;
{
  var i: int;
  var addr, oldValue: int;
  i := wIdx[tid];
  while (i>0) {
    i := i-1;
    addr := wlog_addr[tid,i];
    oldValue := wlog_oldv[tid,i];
    Mem_val[addr] := oldValue;
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
  wlog_addr, wlog_oldv, wIdx;
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
      if (success) { call TxWrite(actionList_addr[i], actionList_val[i]);	}
		}
		i := i+1;
  }

  if (success) { call success := ValidateReads(); }
  if (!success) { call UndoUpdates(); }
  call CloseUpdates();
}


/*
------------------------------------------------------------------------
OpenForRead(a: int) 
{
  [ 
		havoc rlog[tid][rIdx[tid]].ver; 
		assume rlog[tid][rIdx[tid]].ver<=Mem[a].version 
	];
	rlog[tid][rIdx[tid]].addr := a;
	rIdx[tid] := rIdx[tid]+1
}

ValidateRead(a: int, index: int) 
 returns (success: bool)
{
  [ 
    assert rlog[tid][index].ver <= Mem[a].version;
		if (*) { success := false }
    else {
			success := true;
			assume (Mem[a].version==reads[tid][index].ver && 
			        (Mem[a].owner==0 || Mem[a].owner==tid));
			assume blocked[tid][a];
			havoc blocked[tid][a]
		}
  ]
}

UndoUpdates()
{
  var i: int;
  var addr, oldValue: int;
  i := wIdx[tid];
  while (i > 0) {
    i := i - 1;
    addr := wlog[tid][i].addr;
    oldValue := wlog[tid][i].oldValue;
    [
      assert Mem[addr].owner == tid;
      assume forall t:Tid. t != tid ==> !blocked[t][addr];
      foreach t in Tid do if (t!=tid) { havoc blocked[t][addr] };
      Mem[addr].value := oldValue
    ]
  }
}

TxRead(a: int) 
 returns (v: int)
{
	[
		if (blocked[tid][a]) { 
			val := Mem[a].value;
			firstRead := forall j:int. j<i ==> actionList[j].addr!=a;
			if (firstRead) { auxStart[tid][a] := val }	
		} else { havoc val }
	]
}

OpenForWrite(a: int)
 returns (success: bool)
{
  if (*) {
	  [ 
			assume Mem[a].owner==0 || Mem[a].owner==tid;
		  Mem[a].owner := tid 
		];
		success := true;
    wlog[tid][wIdx[tid]].addr := a;
		[
			assert Mem[a].owner==tid;
			wlog[tid][wIdx[tid]].oldV := Mem[a].value
		];
		wIdx[tid] := wIdx[tid]+1
	} else {
		[ assume Mem[a].owner!=0 && Mem[a].owner!=tid ];
		success := false
	}
}

TxWrite(a: int, v: int)
{
	[
		assert Mem[a].owner == tid;
		assume (forall t:Tid. t!=tid ==> !blocked[t][a]);
		foreach t in Tid do if (t!=tid) { havoc blocked[t][a] };
		Mem[a].value := v
	]
}


Transact() 
 returns (success: bool)
{
	var i: int;
	var actionList: [int];
	var actionCnt: int;

  success := true;
	rIdx[tid] := 0; wIdx[tid] := 0;
	havoc actionCnt, actionList;
	i := 0;

  while (success && i<actionCnt) {
    if (actionList[i].val==0) {
      OpenForRead(actionList[i].addr);
			val := TxRead(actionList[i].addr);
    } else {
      success := OpenForWrite(actionList[i].addr);
      if (success) { TxWrite(actionList[i].addr, actionList[i].val)	}
		};
		i := i+1
  };

  if (success) { success := ValidateReads() };
  if (!success) { UndoUpdates() };
  CloseUpdates()
}

*/


//Transactional Mutual Exclusion Proof:
//slightly modified to account for the lack of break, continue and throw exception
//lOrec, lNest are thread local; reads and writes of these do not need synchronization.
const unique tid: int;

var Mem: [int]int;
var gOrec: int;
var lOrec: [int]int;
var lNest: [int]int;


function isEven (n: int) 
 returns (bool)
{
 n%2 == 0
}

//API

procedure TMBegin()
 returns ()
 modifies lNest, lOrec;
{
	var lnest, lorec: int;
	var trying: bool;
	
	lnest := lNest[tid]+1;
	lNest[tid] := lnest;
	if (lnest == 1) {
		trying := true;
		while (trying) {
			lorec := gOrec;
			lOrec[tid] := lorec;
			if (isEven (lOrec[tid])) {
				trying := false;
			}
		}
	}	
}

procedure TMEnd()
 returns ()
 modifies gOrec, lNest;
{
	var lnest: int;
	var gorec: int;
	
	lnest := lNest[tid]-1;
	lNest[tid] := lnest;
	if (lNest[tid] == 0) {
		if (!isEven (lOrec[tid])) {
			gorec := gOrec+1;
			gOrec := gorec;
		}
	}
}

procedure TMRead(addr: int) 
 returns (tmp:int, res: bool)
{
	var lorec: int;
	
	res := true;
	tmp := Mem[addr];
	lorec := lOrec[tid];
	if (gOrec != lorec) {
		res := false;
	}
}

procedure TMWrite(addr: int, val: int) 
 returns (res:bool)
 modifies gOrec, lOrec, Mem;
{
	var casflag: bool;
	var lorec: int;
	
	res := true;
	if (isEven (lOrec[tid])) {
		atomic {
			casflag := (gOrec == lOrec[tid]); 
			if (casflag){
				gOrec := lOrec[tid]+1;
			}
		}
		if (casflag) {
			lorec := lOrec[tid]+1;
			lOrec[tid] := lorec;
			Mem[addr] := val;
		} else {
			res := false;
		}
	} else {
		Mem[addr] := val;
	}
}



var fr_ver: [int]int;
var fr_val: [int]int;
var to_ver: [int]int;
var to_val: [int]int;

procedure {:isatomic false} {:ispublic true} Copy(addr : int)
 requires true;
{
 // var pSucc : bool;
 var ConsistentProphecy: bool;
 var WillSucceed: bool;
 var version, value: int;
 var success : bool;
 var hVer, pVer: int;

 atomic { havoc hVer; assume hVer<=fr_ver[addr]; }
 
 atomic {
  assert hVer<=fr_ver[addr]; 
  ConsistentProphecy := (pVer>=fr_ver[addr]);
  if (ConsistentProphecy) {
   version := hVer;
   WillSucceed := (pVer==hVer);
   if (WillSucceed) { value := fr_val[addr]; }
   else { havoc value; }
  } else { havoc version, value; }
  havoc ConsistentProphecy, WillSucceed;
 }
 
 atomic {
  assume pVer==fr_ver[addr];
  havoc pVer;
  if (version==fr_ver[addr]) {
   to_ver[addr] := fr_ver[addr];
   to_val[addr] := fr_val[addr];
  } 
 }
}

procedure {:isatomic true} {:ispublic true} Update(addr: int, v: int)
{
 fr_ver[addr] := fr_ver[addr]+1;
 fr_val[addr] := v;
}
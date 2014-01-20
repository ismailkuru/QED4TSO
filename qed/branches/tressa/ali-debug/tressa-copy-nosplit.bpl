
var fr_ver: [int]int;
var fr_val: [int]int;
var to_ver: [int]int;
var to_val: [int]int;

procedure {:isatomic false} {:ispublic true} Copy(addr : int)
 requires true;
{
 // var pSucc : bool;
 var version, value: int;
 var success : bool;
 var hVer, pVer: int;

 atomic { hVer := fr_ver[addr]; }
 
 atomic {
  assume hVer<=fr_ver[addr]; version := hVer;
  if (pVer>=fr_ver[addr] && pVer==hVer) {
   value := fr_val[addr];
  }
  else { havoc value; }
  tressa pVer>=fr_ver[addr];
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
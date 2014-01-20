
var fr_ver: [int]int;
var fr_val: [int]int;
var to_ver: [int]int;
var to_val: [int]int;

var pver: [int]int;

procedure {:isatomic false} {:ispublic true} Copy(addr : int)
 requires true;
{
 var p : bool;
 var version, value: int;
 var pvertid: int;

 
 atomic {
  havoc version, value; 
  if (*) { assume p && (version==fr_ver[addr]) && (pver[tid]==fr_ver[addr]); value := fr_val[addr]; } 
  else { assume !p || (version!=fr_ver[addr]) || (pver[tid]!=fr_ver[addr]); }
  tressa p ==> (version==pver[tid]) && (pver[tid]==fr_ver[addr]);
 }
 
 atomic {
  if (version == fr_ver[addr]) {
   assume p; havoc p;
   assume pver[tid]==fr_ver[addr]; havoc pvertid; pver[tid] := pvertid;
   to_val[addr] := value;
   to_ver[addr] := version+1;
  }
  else { assume !p; havoc p; }
 }
}

procedure {:isatomic true} {:ispublic true} Update(addr: int, v: int)
{
 assume (forall t:int :: pver[t]==fr_ver[addr]); havoc pver; 
 fr_ver[addr] := fr_ver[addr]+1;
 fr_val[addr] := v;
}
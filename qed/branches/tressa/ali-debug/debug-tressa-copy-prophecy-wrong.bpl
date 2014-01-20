
var fr_ver: [int]int;
var fr_val: [int]int;
var to_ver: [int]int;
var to_val: [int]int;

procedure {:isatomic false} {:ispublic true} Copy(addr : int)
 requires true;
{
 var p : bool;
 var version, value: int;
 
 atomic {
  if (p) { version := fr_ver[addr]; value := fr_val[addr]; }
  else { havoc version, value; }
  tressa p ==> ((value==fr_val[addr]) && (version==fr_ver[addr]));
 }
 
 atomic {
  if (version == fr_ver[addr]) {
   assume p; havoc p;
   to_val[addr] := value;
   to_ver[addr] := version+1;
  }
  else { assume !p; havoc p; }
 }
}

procedure {:isatomic true} {:ispublic true} Update(addr: int, v: int)
{
 fr_ver[addr] := fr_ver[addr]+1;
 fr_val[addr] := v;
}
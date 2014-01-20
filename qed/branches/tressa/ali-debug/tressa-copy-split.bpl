
var fr_ver: [int]int;
var fr_val: [int]int;
var to_ver: [int]int;
var to_val: [int]int;

procedure {:isatomic false} {:ispublic true} Copy(addr : int)
 requires true;
{
 var p : bool;
 var version, value: int;
 var success : bool;
 
 success := false;
 
 if (*) {
  atomic { 
   havoc version, value;
  }
  
  atomic {
   if (version==fr_ver[addr]) {
    to_val[addr] := value;
    to_ver[addr] := version+1;
    success := true;
   }
   assume !success;
  }
 } else {
  atomic {
   havoc version, value;
   assume version<=fr_ver[addr];
   assume (version==fr_ver[addr]) ==> (value==fr_val[addr]);
  }
  
  atomic {
   if (version == fr_ver[addr]) {
    to_val[addr] := value;
    to_ver[addr] := version+1;
    success := true;
   }
   assume success;
  }
 }
}

procedure {:isatomic true} {:ispublic true} Update(addr: int, v: int)
{
 fr_ver[addr] := fr_ver[addr]+1;
 fr_val[addr] := v;
}
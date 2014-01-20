
record Obj
{
  val: int;
  ver: int;
}

procedure Copy(fr: Obj, to: Obj)
{
  var version: int;
  var value: int;

  atomic {
    version := fr.ver;
    value := fr.val;
  }

  atomic {
    if(version == fr.ver)
    {
      to.val := value;
      to.ver := to.ver + 1;
    }
  }
}

procedure Wrt(to: Obj, newVal: int)
{
  atomic {
    to.val := newVal;
    to.ver := to.ver + 1;
 }
}
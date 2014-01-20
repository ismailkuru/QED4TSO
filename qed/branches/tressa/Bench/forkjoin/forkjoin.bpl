record myrec {
  a: int;
  c : int;
  b: bool;
}

var r:myrec;
var x : int;

procedure deneme()
modifies x;
{
  var i: int;
  var k: bool;
  var t: int;

    //fork (t) {
            r := New myrec;
            r.a := r.a + 1;
			r.a := r.a - r.a;
            k := r.b;
            Free r;
    //}
	
	//r.c := r.a - 1;
    //join t;
	
	//x := x + 1;
	
	//x := 0;
}



record myrec {
a : int;
b : bool;
}

procedure deneme (r:myrec) {
	var i : int;
	var k:bool;
	
	r := New myrec;
	r.a :=  r.a + 1;
	k :=  r.b;
	Free r;

}
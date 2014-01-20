
var y: int;

procedure test()
{
var t: int;
var b: bool;

t := y;

cobegin{
t := y;
if(b) {
return;
}
}

atomic{
while(true) {
	if(y == t) {
	   if(*) {
	     y := t + 1;
	     //b := true;
	   } else {
	     assume true;//b := false;
	   }
	} else {
	     assume true;//b := false;
	}
}
}

}
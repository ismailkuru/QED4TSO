var y: int;

procedure {:isatomic false} {:ispublic true} UndoUpdate()
{
 var x: int;
 
 x := x+1;
 y := y+(y-x);
}                                                             


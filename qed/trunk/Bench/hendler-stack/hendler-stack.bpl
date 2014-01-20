
const EMPTY: int;
axiom EMPTY == 0;

type Op;
const unique POP: Op;
const unique PUSH: Op;
axiom (forall op:Op :: op == POP || op == PUSH);

record Cell
{
 pnext: Cell;
 pdata: int;
}

record ThreadInfo
{
 id: int;
 op: Op;
 cell: Cell;
 // no need for spin
}

const unique NULL_THREADINFO: ThreadInfo;
invariant IsNull(NULL_THREADINFO.alloc);

const unique NULL_CELL: Cell;
invariant IsNull(NULL_CELL.alloc);

var ptop: Cell;
var location: [int]ThreadInfo;
var collision: [int]int;


procedure StackOp(p: ThreadInfo)
{
 var g: bool;

 call g := TryPerformStackOp(p);

 if(!g)
 {
  call LesOP(p);
 }
}

procedure LesOP(p: ThreadInfo)
{
 var him: int,
     pos: int, 
     q: ThreadInfo,
     g: bool;

 while(true)
 {
  location[tid] := p;
  havoc pos;
  
  atomic {
   him := collision[pos];
   collision[pos] := tid;
  }

  if(him != EMPTY)
  {
   q := location[him];
   g := (q != NULL_THREADINFO && q.id == him && q.op != p.op);
   if(g)
   {
    // CAS
    atomic {
     g := (location[tid] == p);
     if(g)
     {
       location[tid] := NULL_THREADINFO;
     }
    }

    if(g) // if CAS succeeds
    {
     call g := TryCollision(p,q);
     if(g)
     {
       return;
     }
     else
     {
       call g := TryPerformStackOp(p);
       if(g)
       {
        return;
       }
     }
    }
    else // if CAS fails
    {
     call FinishCollision(p);
     return;
    }
   }
  }

  // delay

  // CAS
  atomic {
   g := (location[tid] == p);
   if(g)
   {
     location[tid] := NULL_THREADINFO;
   }
  }

  if(!g) // if CAS fails
  {
   call FinishCollision(p);
  }

  call g := TryPerformStackOp(p);
  if(!g)
  {
    return;
  }
 
 }//end while
} // end procedure


procedure {:isatomic} TryPerformStackOp(p: ThreadInfo)
returns (r: bool)
{
 if(*)
 {
  r := false; // non deterministic failure
  return;
 }
 
 if(p.op == PUSH)
 {
  p.cell.pnext := ptop;
  ptop := p.cell;
 }
 else // POP
 {
  if(ptop == NULL_CELL)
  {
   p.cell := NULL_CELL;
  }
  else
  {
   p.cell := ptop;
   ptop := ptop.pnext;
  }
 }
 r := true;
} // end procedure


procedure TryCollision(p: ThreadInfo, q: ThreadInfo)
returns (r: bool)
{
 if(p.op == PUSH)
 {
  // CAS
  atomic {
   r := (location[tid] == q);
   if(r)
   {
     location[tid] := p;
   }
  }
 }
 else // POP
 {
  atomic {
   r := (location[tid] == q);
   if(r)
   {
     p.cell := q.cell;
     location[tid] := NULL_THREADINFO;
   }
  }
 }
} // end procedure

procedure FinishCollision(p: ThreadInfo)
{
 if(p.op == POP)
 {
  p.cell := location[tid].cell;
  location[tid] := NULL_THREADINFO;
 }
} // end procedure


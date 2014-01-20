

type ref;
const unique null : ref;

record Monitor
{
	held : bool;
}

record NaiveSQ
{
	putting : bool;
	item : ref;
	monitor : Monitor;
}

procedure {:isatomic true} {:ispublic false} acquire(monitor:Monitor)
modifies Monitor_held;
{
  assume monitor.held == false;
  monitor.held := true;
}

procedure {:isatomic true} {:ispublic false} release(monitor:Monitor)
modifies Monitor_held;
{
  assert monitor.held == true;
  monitor.held := false;
}

procedure {:isatomic false} {:ispublic true} take(q:NaiveSQ) returns (e:ref)
  modifies NaiveSQ_putting, NaiveSQ_item, Monitor_held;
{
	var itm:ref;
	
	while(*)
	{
		call acquire(q.monitor);
		itm := q.item;
		assume (itm == null);
		call release(q.monitor);
	}
		
	call acquire(q.monitor);
	
	itm := q.item;
	assume (itm != null);
	
	e := itm;
	q.item := null;
	
	call release(q.monitor);
	return;
}

procedure {:isatomic false} {:ispublic true} put(q:NaiveSQ, e:ref)
modifies NaiveSQ_putting, NaiveSQ_item, Monitor_held;
{
	var itm:ref;
	var ptng:bool;
	
	if(e == null)
	{
		return;
	}
	
	while(*)
	{
		call acquire(q.monitor);
		ptng := q.putting;
		assume (ptng == true);
		call release(q.monitor);
	}
	
	call acquire(q.monitor);
	
	ptng := q.putting;
	assume (ptng == false);
	
	q.putting := true;
	q.item := e;
	
	call release(q.monitor);
	
	while(*)
	{
		call acquire(q.monitor);
		itm := q.item;
		assume (itm != null);
		call release(q.monitor);
	}
	
	call acquire(q.monitor);
	
	itm := q.item;
	assume (itm == null);
	
	q.putting := false;
	
	call release(q.monitor);
	return;
}



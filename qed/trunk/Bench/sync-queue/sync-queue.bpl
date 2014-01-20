

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
	
	call acquire(q.monitor);
	
	while(*){
		itm := q.item;
		if(itm == null)
		{
			call release(q.monitor);
			call acquire(q.monitor);
		} else {
			break;
		}
	}
	
	e := q.item;
	q.item := null;
	
	call release(q.monitor);
	return;
}

procedure {:isatomic false} {:ispublic true} put(q:NaiveSQ, e:ref)
modifies NaiveSQ_putting, NaiveSQ_item, Monitor_held;
{
	var itm:ref;
	var ptng:bool;
	
	call acquire(q.monitor);
	
	if(e == null)
	{
		call release(q.monitor);
		return;
	}
	
	while(*){
		ptng := q.putting;
		if(ptng == true)
		{
			call release(q.monitor);
			call acquire(q.monitor);
		} else {
			break;
		}
	}
	
	q.putting := true;
	q.item := e;
	
	while(*){
		itm := q.item;
		if(itm == null)
		{
			call release(q.monitor);
			call acquire(q.monitor);
		} else {
			break;
		}
	}
	
	q.putting := false;
	
	call release(q.monitor);
	return;
}



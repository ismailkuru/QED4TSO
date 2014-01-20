
const unique MonitorException: Exception;
const unique NULL_OBJECT: Object;
const unique NULL_CV: CV;

procedure {:ispublic false} {:isatomic true} Monitor_exit(obj: Object)
{
	assert obj.lock == True;
	obj.lock := False;
}

procedure {:ispublic false} {:isatomic true} Monitor_enter(obj: Object)
{
	assume obj.lock == False;
	obj.lock := True;
}

record Object
{
	lock: boolean;
}

procedure {:isatomic true} {:ispublic false} Object_lock(obj: Object)
{
	assume obj.lock == False;
	obj.lock := True;
}

procedure {:isatomic true} {:ispublic false} Object_unlock(obj: Object)
{
	assert obj.lock == True;
	obj.lock := False;
}

record CV
{
	syncLock: Object;
	m: Object;
}

record RW
{
	syncRoot: Object;
	i: int;
	readWaiters: int;
	writeWaiters: int;
	wq: CV;
}

procedure RW_acquireWriterLock(this: RW)
{
	var temp: int;
	var guard: bool;
	var cv: CV;
	cv := this.wq;
			
	call Object_lock(this.syncRoot);
		temp := this.writeWaiters;
		temp := temp + 1;
		this.writeWaiters := temp;
		
		guard := true;
	call Object_unlock(this.syncRoot);
	
	while (guard)
	{
		call Monitor_enter(cv.m);
		guard := this.i != 0;
		if (!guard)
		{
			break;
		}
		
		call Object_lock(cv.syncLock);
		call Monitor_exit(cv.m);
		call Object_unlock(cv.syncLock);
	}
		
	temp := this.writeWaiters;
	temp := temp - 1;
	this.writeWaiters := temp;
	this.i := -1;
	
	call Object_unlock(this.syncRoot);
}

procedure RW_acquireReaderLock(this: RW)
{
	var temp: int;
	var guard: bool;
	
	call Object_lock(this.syncRoot);
		temp := this.readWaiters;
		temp := temp + 1;
		this.readWaiters := temp;
		
		guard := (this.writeWaiters > 0);
	
		if (guard)
		{
			call Object_unlock(this.syncRoot);
			call Object_lock(this.syncRoot);
		}
		
		guard := true;
	call Object_unlock(this.syncRoot);
	
	while (guard)
	{
		call Object_lock(this.syncRoot);
		guard := (this.i < 0);
		if (!guard)
		{
			break;
		}		
		call Object_unlock(this.syncRoot);
	}
		
	temp := this.readWaiters;
	temp := temp - 1;
	this.readWaiters := temp;
		
	temp := this.i;
	temp := temp + 1;
	this.i := temp;
		
	call Object_unlock(this.syncRoot);
}

procedure RW_releaseWriterLock(this: RW)
{
	call Object_lock(this.syncRoot);
		this.i := 0;
	call Object_unlock(this.syncRoot);
}

procedure RW_releaseReaderLock(this: RW)
{
	var temp: int;
	
	call Object_lock(this.syncRoot);
		temp := this.i;
		temp := temp - 1;
		this.i := temp;
	call Object_unlock(this.syncRoot);
}

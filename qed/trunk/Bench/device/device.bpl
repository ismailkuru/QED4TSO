var device: [int]int,  cache : [int]int,  currsize : int,  newsize : int,  lock : bool;

procedure {:isatomic true} {:ispublic false} acquire()
modifies lock;
{
	assume lock == false;
	lock := true;
}

procedure {:isatomic true} {:ispublic false} release()
modifies lock;
{
	assert lock == true;
	lock := false;
}

procedure {:isatomic false} {:ispublic true} Read (start:int, size:int) returns (buffer : [int]int, bytesread:int)
    modifies cache,lock,newsize,currsize;
    // requires start >= 0 && size > 0;
{
	var i, j, tmp: int;
	
	call acquire();
	i := currsize;
    if (start + size <= i) {
		call release();
		
		bytesread := size;

		goto COPY_TO_BUFFER;
    }else if (newsize > i) {
		call release();
	
		if(start <= i) {
			bytesread := i - start;
		} else {
			bytesread := 0;
		}
		goto COPY_TO_BUFFER;
    } else {
		newsize := start + size;
		call release();
		goto READ_DEVICE;
	}
	
READ_DEVICE:
	while(i < start + size) {
		cache[i] := device[i];
		i := i + 1;	
	}
	
	bytesread := size;
	
	call acquire();
		tmp := newsize;
		currsize := tmp;
	call release();

COPY_TO_BUFFER:
	j := 0;
	while(j < bytesread) {
		buffer[j] := cache[start + j];
		j := j + 1;	
	}
	bytesread := size;
	return;
}
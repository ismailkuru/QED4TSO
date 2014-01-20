
type ref;

const unique null : ref;

var obj:ref;
var lock:bool;
var flag:int;
const unique EMPTY:int;
const unique FULL:int;
const unique INIT:int;

invariant (flag == FULL || flag == INIT || flag == EMPTY);

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


procedure {:isatomic true} {:ispublic false} long_init_procedure() returns (ret:ref)
{
	var o : ref;
	havoc o;
	assume o != null;
	ret := o;
}


procedure {:isatomic false} {:ispublic true} Read() returns (stt:int, ret:ref)
  modifies lock, flag, obj;
{
	var f : int;

    call acquire();
	f := flag;
    if (f == INIT) {
        call release();
        stt := INIT; ret := null;
        return;
    }
    else if (f == FULL) {
       	call release();
        stt := FULL; ret := obj;
        assert ret != null && ret == obj;
        return;
    }
    assert (flag == EMPTY);
    flag := INIT;
    call release();

    call obj := long_init_procedure();
    assert (obj != null);

    call acquire();
        flag := FULL;
    call release();

    stt := FULL; ret := obj;
    assert ret != null && ret == obj;
    return;
}



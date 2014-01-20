record Node {
addr: int;
value: int;
idx: int;
alloc: AllocType;
owner: TID;
}

record WriteBuffer {
writebuffer: [int]Node;
head: int;
tail: int;
alloc: AllocType;
owner: TID;
}

var Mem: [int]int;

var ThreadWriteBuffers: [TID]WriteBuffer;

invariant (forall wb: WriteBuffer :: wb.head <= wb.tail);

invariant (forall tid: TID, i: int, j: int :: { ThreadWriteBuffers[tid].writebuffer[i], ThreadWriteBuffers[tid].writebuffer[j] } i != j ==> ThreadWriteBuffers[tid].writebuffer[i] != ThreadWriteBuffers[tid].writebuffer[j]);

invariant (forall tid1: TID, tid2: TID :: { ThreadWriteBuffers[tid1], ThreadWriteBuffers[tid2] } tid1 != tid2 ==> ThreadWriteBuffers[tid1] != ThreadWriteBuffers[tid2]);

function UpdateMemSEG(Memory: [int]int, bf: [int]Node, idx: int, idx2: int, Amap: [Node]int, Vmap: [Node]int) returns ([int]int);

axiom (forall addr: int, i: int, ix: int, update: int, M: [int]int, bf: [int]Node, vmap: [Node]int, amap: [Node]int :: i <= ix && i <= update && update < ix && amap[bf[update]] == addr && (forall ls: int :: i <= ls && ls < ix && amap[bf[ls]] == addr ==> ls <= update) ==> UpdateMemSEG(M, bf, i, ix, amap, vmap)[addr] == vmap[bf[update]]);

axiom (forall addr: int, i: int, ix: int, M: [int]int, bf: [int]Node, vmap: [Node]int, amap: [Node]int :: i <= ix && (forall update: int :: i <= update && update < ix ==> amap[bf[update]] != addr) ==> UpdateMemSEG(M, bf, i, ix, amap, vmap)[addr] == M[addr]);

procedure {:isatomic true} drain();
  modifies WriteBuffer_head;



implementation drain()
{
  var node: Node;
  var bufferOfThread: WriteBuffer;
  var oldHead: int;
  var newHead: int;
  var ex: Exception;

  Atomic_4:
    atomic  {  // Non-mover
        bufferOfThread := ThreadWriteBuffers[tid];
        oldHead := bufferOfThread.head;
        havoc newHead;
        assume oldHead <= newHead && newHead <= bufferOfThread.tail;
        bufferOfThread.head := newHead;
        Mem := UpdateMemSEG(Mem, bufferOfThread.writebuffer, oldHead, newHead, Node_addr, Node_value);
    }
}



const unique xAddr: int;

const unique yAddr: int;

const unique zAddr: int;

const unique mAddr: int;

const unique kAddr: int;

const unique vAddr: int;

procedure {:isatomic true} testDrain();



implementation testDrain()
{
  var buf: [int]Node;
  var ex: Exception;

  Atomic_5:
    atomic  {  // Non-mover
        assume (forall i: int, j: int :: i != j ==> buf[i] != buf[j]);
        assume buf[0].value == 5;
        assume buf[0].addr == xAddr;
        assume buf[1].value == 6;
        assume buf[1].addr == mAddr;
        assume buf[2].value == 9;
        assume buf[2].addr == vAddr;
        assume buf[3].value == 12;
        assume buf[3].addr == mAddr;
        assume buf[4].value == 13;
        assume buf[4].addr == kAddr;
        assume buf[5].value == 21;
        assume buf[5].addr == mAddr;
        Mem[zAddr] := 7;
        Mem := UpdateMemSEG(Mem, buf, 0, 6, Node_addr, Node_value);
        /* assert Mem[xAddr] == 5; [Discharged] */
        /* assert Mem[vAddr] == 9; [Discharged] */
        /* assert Mem[kAddr] == 13; [Discharged] */
        /* assert Mem[mAddr] == 21; [Discharged] */
        assert false;
        /* assert Mem[zAddr] == 7; [Discharged] */
    }
}



procedure {:isatomic true} readTID(thread: TID, addr: int) returns (result: int);



implementation readTID(thread: TID, addr: int) returns (result: int)
{
  var bufferOfthread: WriteBuffer;
  var node: Node;
  var idx: int;
  var ex: Exception;

  Atomic_6:
    atomic  {  // Non-mover
        bufferOfthread := ThreadWriteBuffers[thread];
        havoc node;
        if (*)
        {
            assume node.idx >= bufferOfthread.head && node.idx < bufferOfthread.tail && bufferOfthread.writebuffer[node.idx].addr == addr && (forall nodeRecent: Node :: nodeRecent.idx > node.idx && nodeRecent.idx <= bufferOfthread.tail ==> nodeRecent.addr != node.addr && nodeRecent.addr != addr);
            assume (forall nodeLessRecent: Node :: nodeLessRecent.idx >= bufferOfthread.head && nodeLessRecent.idx < bufferOfthread.tail && nodeLessRecent.addr == node.addr ==> node.idx >= nodeLessRecent.idx);
            result := bufferOfthread.writebuffer[node.idx].value;
        }
        else
        {
            assume (forall nodeNotFound: Node :: nodeNotFound.idx >= bufferOfthread.head && nodeNotFound.idx < bufferOfthread.tail && nodeNotFound.addr != node.addr);
            result := Mem[node.addr];
        }
    }
}



procedure {:isatomic true} drainTID(thread: TID);
  modifies WriteBuffer_head;



implementation drainTID(thread: TID)
{
  var node: Node;
  var bufferOfThread: WriteBuffer;
  var oldHead: int;
  var newHead: int;
  var ex: Exception;

  Atomic_7:
    atomic  {  // Non-mover
        bufferOfThread := ThreadWriteBuffers[thread];
        oldHead := bufferOfThread.head;
        havoc newHead;
        assume oldHead <= newHead && newHead <= bufferOfThread.tail;
        bufferOfThread.head := newHead;
        Mem := UpdateMemSEG(Mem, bufferOfThread.writebuffer, oldHead, newHead, Node_addr, Node_value);
    }
}



procedure {:isatomic true} writeTID(thread: TID, value: int, addr: int);
  modifies WriteBuffer_tail;



implementation writeTID(thread: TID, value: int, addr: int)
{
  var bufferOfthread: WriteBuffer;
  var node: Node;
  var ex: Exception;

  Atomic_8:
    atomic  {  // Non-mover
        bufferOfthread := ThreadWriteBuffers[thread];
        node := bufferOfthread.writebuffer[bufferOfthread.tail];
        assume node.idx == bufferOfthread.tail;
        assume node.addr == addr;
        assume node.value == value;
        bufferOfthread.tail := bufferOfthread.tail + 1;
        /* assert ThreadWriteBuffers[thread].writebuffer[bufferOfthread.tail - 1].value == value; [Discharged] */
        /* assert ThreadWriteBuffers[thread].writebuffer[bufferOfthread.tail - 1].addr == addr; [Discharged] */
    }
}



const unique th1: TID;

const unique th2: TID;

const unique th3: TID;

const unique th4: TID;

procedure {:isatomic true} readLatestSameThread();



implementation readLatestSameThread()
{
  var toWriteAddr: int;
  var toRead: int;
  var ex: Exception;

  Atomic_9:
    atomic  {  // Non-mover
      Atomic_780:
         // Non-mover
          assume Mem[toWriteAddr] == 100;

      Call_10:
          call writeTID(th2, 2, toWriteAddr);

      Call_11:
          call writeTID(th2, 3, toWriteAddr);

      Call_12:
          call writeTID(th2, 4, toWriteAddr);

      Call_13:
          call writeTID(th2, 5, toWriteAddr);

      Call_14:
          call toRead := readTID(th2, toWriteAddr);

      Atomic_781:
         // Non-mover
          assert toRead == 5;
    }
}



procedure {:isatomic true} readLatestDifThread();



implementation readLatestDifThread()
{
  var toWriteAddr: int;
  var toRead: int;
  var ex: Exception;

  Atomic_19:
    atomic  {  // Non-mover
      Atomic_782:
         // Non-mover
          assume Mem[toWriteAddr] == 100;

      Call_20:
          call writeTID(th2, 2, toWriteAddr);

      Call_21:
          call writeTID(th2, 3, toWriteAddr);

      Call_22:
          call writeTID(th3, 7, toWriteAddr);

      Call_23:
          call writeTID(th3, 8, toWriteAddr);

      Call_24:
          call toRead := readTID(th3, toWriteAddr);

      Atomic_783:
         // Non-mover
          assert toRead == 8;

      Call_25:
          call toRead := readTID(th2, toWriteAddr);

      Atomic_784:
         // Non-mover
          assert toRead == 3;
    }
}



procedure {:isatomic true} drainTest();



implementation drainTest()
{
  var toWriteAddr: int;
  var toRead: int;
  var buf: [int]Node;
  var bufferOfthread: WriteBuffer;
  var bufferOfthread1: WriteBuffer;
  var ex: Exception;

  Atomic_32:
    atomic  {  // Non-mover
      Atomic_785:
         // Non-mover
          bufferOfthread := ThreadWriteBuffers[th3];
          bufferOfthread1 := ThreadWriteBuffers[th2];
          assume Mem[toWriteAddr] == 100;

      Call_33:
          call writeTID(th2, 2, toWriteAddr);

      Call_34:
          call writeTID(th2, 3, toWriteAddr);

      Call_35:
          call writeTID(th3, 7, toWriteAddr);

      Call_36:
          call writeTID(th3, 8, toWriteAddr);

      Atomic_786:
         // Non-mover
          Mem := UpdateMemSEG(Mem, bufferOfthread.writebuffer, bufferOfthread.head, bufferOfthread.tail - 1, Node_addr, Node_value);
          assert Mem[toWriteAddr] == 8;

      Call_37:
          call toRead := readTID(th2, toWriteAddr);

      Atomic_787:
         // Non-mover
          assert toRead == 3;
          Mem := UpdateMemSEG(Mem, bufferOfthread1.writebuffer, bufferOfthread1.head, bufferOfthread1.tail, Node_addr, Node_value);
          assert Mem[toWriteAddr] == 3;
    }
}



var {:isaux} ownerMap: [int]TID;

const unique toRd: int;

const unique toRecv: int;

const unique toSend: int;

const unique senderThread: TID;

const unique recvThread: TID;

procedure {:isatomic true} absdrain(addrFlag: int, addrX: int);
  modifies WriteBuffer_head;



implementation absdrain(addrFlag: int, addrX: int)
{
  var node: Node;
  var bufferOfThread: WriteBuffer;
  var oldHead: int;
  var newHead: int;
  var ex: Exception;

  Atomic_44:
    atomic  {  // Non-mover
        bufferOfThread := ThreadWriteBuffers[tid];
        oldHead := bufferOfThread.head;
        havoc newHead;
        assume oldHead <= newHead && newHead <= bufferOfThread.tail;
        bufferOfThread.head := newHead;
        havoc Mem;
        assume Mem[addrFlag] == UpdateMemSEG(Mem, bufferOfThread.writebuffer, oldHead, newHead, Node_addr, Node_value)[addrFlag];
        assume Mem[addrX] == UpdateMemSEG(Mem, bufferOfThread.writebuffer, oldHead, newHead, Node_addr, Node_value)[addrX];
    }
}



procedure {:ispublic false} send(addrFlag: int, addrX: int);
  modifies Mem, WriteBuffer_tail, WriteBuffer_head;



implementation send(addrFlag: int, addrX: int)
{
  var flagLocal: int;
  var bufferOfthread: WriteBuffer;
  var node: Node;
  var idx: int;
  var ex: Exception;
  var fresh_0: WriteBuffer;
  var fresh_1: Node;
  var fresh_2: WriteBuffer;
  var fresh_3: Node;
  var fresh_4: WriteBuffer;
  var fresh_5: WriteBuffer;
  var fresh_6: WriteBuffer;
  var newHead: int;
  var newHead1: int;
  var newHead2: int;

  Atomic_45:
    atomic  {  // Non-mover
        assert senderThread == tid;
        havoc flagLocal;
        /* assert ThreadWriteBuffers[recvThread].tail == ThreadWriteBuffers[recvThread].head; [Discharged] */
        /* assert Mem[addrFlag] == toSend && ownerMap[addrFlag] == senderThread && ownerMap[addrX] == senderThread && flagLocal == toSend; [Discharged] */
        /* assert senderThread == tid; [Discharged] */
        assume flagLocal == toSend;
    }

    while (*)
    {
      Call_47:
        atomic  {  // Non-mover
            assert senderThread == tid;
            /* assert Mem[addrFlag] == toSend && ownerMap[addrFlag] == senderThread && ownerMap[addrX] == senderThread && flagLocal == toSend; [Discharged] */
            /* assert Mem[addrFlag] == flagLocal; [Discharged] */
            /* assert ThreadWriteBuffers[senderThread].head == ThreadWriteBuffers[senderThread].tail; [Discharged] */
            /* assert ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].addr != addrFlag && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].addr != addrX; [Discharged] */
            /* assert ThreadWriteBuffers[recvThread].tail == ThreadWriteBuffers[recvThread].head; [Discharged] */
            havoc Mem;
            havoc newHead;
            assume fresh_4 == ThreadWriteBuffers[senderThread];
            assume fresh_4.head <= fresh_4.tail;
            assume fresh_4.head <= newHead && newHead <= fresh_4.tail;
            assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_4.writebuffer, fresh_4.head, fresh_4.head + 1, Node_addr, Node_value)[addrFlag];
            assume Mem[addrX] == UpdateMemSEG(Mem, fresh_4.writebuffer, fresh_4.head, fresh_4.head + 1, Node_addr, Node_value)[addrX];
        }
    }

  Call_48:
    atomic  {  // Non-mover
        assert ThreadWriteBuffers[recvThread].tail == ThreadWriteBuffers[recvThread].head;
        assert ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].value == toRd;
        assert ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].tail - 1].value == toRd;
        assert ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].addr == addrX;
        assert ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].tail - 1].addr == addrX;
        assert ThreadWriteBuffers[senderThread].head < ThreadWriteBuffers[senderThread].tail && ThreadWriteBuffers[senderThread].tail == ThreadWriteBuffers[senderThread].head + 1;
        assert Mem[addrFlag] == toSend && ownerMap[addrFlag] == senderThread && ownerMap[addrX] == senderThread && flagLocal == toSend;
        assert senderThread == tid;
        /* assert true; [Discharged] */
        /* call write(addrX, toRd); */
        fresh_0 := ThreadWriteBuffers[tid];
        fresh_1 := fresh_0.writebuffer[fresh_0.tail];
        assume fresh_1.idx == fresh_0.tail;
        assume fresh_1.addr == toRd;
        assume fresh_1.value == addrX;
        fresh_0.tail := fresh_0.tail + 1;
    }

    while (*)
    {
      Call_49:
        atomic  {  // Non-mover
            assert senderThread == tid;
            /* assert Mem[addrFlag] == toSend && ownerMap[addrFlag] == senderThread && ownerMap[addrX] == senderThread && flagLocal == toSend; [Discharged] */
            /* assert ThreadWriteBuffers[senderThread].head < ThreadWriteBuffers[senderThread].tail ==> ThreadWriteBuffers[senderThread].tail == ThreadWriteBuffers[senderThread].head + 1; [Discharged] */
            /* assert ThreadWriteBuffers[senderThread].head < ThreadWriteBuffers[senderThread].tail ==> ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].addr == addrX; [Discharged] */
            /* assert ThreadWriteBuffers[senderThread].head < ThreadWriteBuffers[senderThread].tail ==> ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].value == toRd; [Discharged] */
            /* assert ThreadWriteBuffers[senderThread].head == ThreadWriteBuffers[senderThread].tail ==> Mem[addrX] == toRd; [Discharged] */
            /* assert ThreadWriteBuffers[recvThread].tail == ThreadWriteBuffers[recvThread].head; [Discharged] */
            havoc Mem;
            havoc newHead;
            assume fresh_5 == ThreadWriteBuffers[senderThread];
            assume fresh_5.head <= fresh_5.tail;
            assume fresh_5.head <= newHead && newHead <= fresh_5.tail;
            assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_5.writebuffer, fresh_5.head, fresh_5.head + 1, Node_addr, Node_value)[addrFlag];
            assume Mem[addrX] == UpdateMemSEG(Mem, fresh_5.writebuffer, fresh_5.head, fresh_5.head + 1, Node_addr, Node_value)[addrX];
        }
    }

  Call_50:
    atomic  {  // Non-mover
        assert ThreadWriteBuffers[recvThread].tail == ThreadWriteBuffers[recvThread].head;
        assert ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].tail - 1].addr == addrFlag;
        assert ThreadWriteBuffers[senderThread].tail == ThreadWriteBuffers[senderThread].head + 1 ==> ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].addr == addrFlag && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].value == toRecv && Mem[addrX] == toRd;
        assert ThreadWriteBuffers[senderThread].tail == ThreadWriteBuffers[senderThread].head + 2 ==> ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].tail - 1].addr == addrFlag && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].tail - 1].value == toRecv && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].addr == addrX && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].value == toRd;
        /* assert ThreadWriteBuffers[senderThread].tail == ThreadWriteBuffers[senderThread].head + 2 ==> ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].tail - 1].addr == addrFlag && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].tail - 1].value == toRecv && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].addr == addrX && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].value == toRd; [Discharged] */
        assert ThreadWriteBuffers[senderThread].head < ThreadWriteBuffers[senderThread].tail;
        assert Mem[addrFlag] == toSend && ownerMap[addrFlag] == senderThread && ownerMap[addrX] == senderThread && flagLocal == toSend;
        assert senderThread == tid;
        /* assert true; [Discharged] */
        /* call write(addrFlag, toRecv); */
        fresh_2 := ThreadWriteBuffers[tid];
        fresh_3 := fresh_2.writebuffer[fresh_2.tail];
        assume fresh_3.idx == fresh_2.tail;
        assume fresh_3.addr == toRecv;
        assume fresh_3.value == addrFlag;
        fresh_2.tail := fresh_2.tail + 1;
    }

    while (*)
    {
      Call_51:
        atomic  {  // Non-mover
            assert senderThread == tid;
            /* assert ThreadWriteBuffers[senderThread].head + 2 == ThreadWriteBuffers[senderThread].tail ==> Mem[addrFlag] == toSend && ownerMap[addrFlag] == senderThread && ownerMap[addrX] == senderThread && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].value == toRd && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].addr == addrX && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].tail - 1].value == toRecv && flagLocal == toSend && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].tail - 1].addr == addrFlag; [Discharged] */
            /* assert ThreadWriteBuffers[senderThread].head + 1 == ThreadWriteBuffers[senderThread].tail ==> Mem[addrFlag] == toSend && ownerMap[addrFlag] == senderThread && ownerMap[addrX] == senderThread && Mem[addrX] == toRd && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].value == toRecv && flagLocal == toSend && ThreadWriteBuffers[senderThread].writebuffer[ThreadWriteBuffers[senderThread].head].addr == addrFlag; [Discharged] */
            /* assert ThreadWriteBuffers[senderThread].head == ThreadWriteBuffers[senderThread].tail ==> Mem[addrFlag] == toRecv && ownerMap[addrFlag] == recvThread && Mem[addrX] == toRd && ownerMap[addrX] == recvThread; [Discharged] */
            /* assert ThreadWriteBuffers[recvThread].head == ThreadWriteBuffers[recvThread].tail; [Discharged] */
            havoc Mem;
            havoc newHead;
            assume fresh_6 == ThreadWriteBuffers[senderThread];
            assume fresh_6.head <= fresh_6.tail;
            assume fresh_6.head <= newHead && newHead <= fresh_6.tail;
            assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_6.writebuffer, fresh_6.head, fresh_6.head + 1, Node_addr, Node_value)[addrFlag];
            assume Mem[addrX] == UpdateMemSEG(Mem, fresh_6.writebuffer, fresh_6.head, fresh_6.head + 1, Node_addr, Node_value)[addrX];
            assume fresh_6.head == fresh_6.tail ==> ownerMap[addrFlag] == recvThread && ownerMap[addrX] == recvThread;
        }
    }
}



procedure {:ispublic false} recieve(addrFlag: int, addrX: int) returns (result: int);
  modifies Mem, WriteBuffer_tail, WriteBuffer_head;



implementation recieve(addrFlag: int, addrX: int) returns (result: int)
{
  var flagLocal: int;
  var bufferOfthread: WriteBuffer;
  var node: Node;
  var idx: int;
  var ex: Exception;
  var fresh_0: WriteBuffer;
  var fresh_1: Node;
  var fresh_2: WriteBuffer;
  var fresh_3: Node;
  var fresh_4: WriteBuffer;
  var fresh_5: WriteBuffer;
  var fresh_6: WriteBuffer;
  var newHead: int;
  var newHead1: int;
  var newHead2: int;

  Atomic_52:
    atomic  {  // Non-mover
        assert recvThread == tid;
        havoc flagLocal;
        /* assert ThreadWriteBuffers[senderThread].head == ThreadWriteBuffers[senderThread].tail; [Discharged] */
        /* assert Mem[addrFlag] == toRecv && ownerMap[addrFlag] == recvThread && ownerMap[addrX] == recvThread && flagLocal == toRecv && Mem[addrX] == toRd; [Discharged] */
        /* assert recvThread == tid; [Discharged] */
        assume flagLocal == toRecv;
    }

    while (*)
    {
      Call_54:
        atomic  {  // Non-mover
            assert recvThread == tid;
            /* assert Mem[addrFlag] == toRecv && ownerMap[addrFlag] == recvThread && ownerMap[addrX] == recvThread && flagLocal == toRecv && Mem[addrX] == toRd; [Discharged] */
            /* assert Mem[addrFlag] == flagLocal; [Discharged] */
            /* assert ThreadWriteBuffers[recvThread].head == ThreadWriteBuffers[recvThread].tail; [Discharged] */
            /* assert ThreadWriteBuffers[recvThread].writebuffer[ThreadWriteBuffers[recvThread].head].addr != addrFlag && ThreadWriteBuffers[recvThread].writebuffer[ThreadWriteBuffers[recvThread].head].addr != addrX; [Discharged] */
            /* assert ThreadWriteBuffers[senderThread].head == ThreadWriteBuffers[senderThread].tail; [Discharged] */
            havoc Mem;
            havoc newHead;
            assume fresh_4 == ThreadWriteBuffers[recvThread];
            assume fresh_4.head <= fresh_4.tail;
            assume fresh_4.head <= newHead && newHead <= fresh_4.tail;
            assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_4.writebuffer, fresh_4.head, fresh_4.head + 1, Node_addr, Node_value)[addrFlag];
            assume Mem[addrX] == UpdateMemSEG(Mem, fresh_4.writebuffer, fresh_4.head, fresh_4.head + 1, Node_addr, Node_value)[addrX];
        }
    }

  Call_55:
    atomic  {  // Non-mover
        assert ThreadWriteBuffers[senderThread].head == ThreadWriteBuffers[senderThread].tail;
        assert result == Mem[addrX];
        assert ThreadWriteBuffers[recvThread].writebuffer[ThreadWriteBuffers[recvThread].head].addr != addrX && ThreadWriteBuffers[recvThread].writebuffer[ThreadWriteBuffers[recvThread].head].addr != addrFlag;
        assert ThreadWriteBuffers[recvThread].head == ThreadWriteBuffers[recvThread].tail;
        assert Mem[addrFlag] == toRecv && ownerMap[addrFlag] == recvThread && ownerMap[addrX] == recvThread && Mem[addrX] == toRd;
        assert recvThread == tid;
        /* assert true; [Discharged] */
        /* call result := read(addrX); */
        fresh_0 := ThreadWriteBuffers[tid];
        havoc fresh_1;
        if (*)
        {
            assume fresh_1.idx >= fresh_0.head && fresh_1.idx < fresh_0.tail && fresh_0.writebuffer[fresh_1.idx].addr == addrX && (forall nodeRecent: Node :: nodeRecent.idx > fresh_1.idx && nodeRecent.idx <= fresh_0.tail ==> nodeRecent.addr != fresh_1.addr && nodeRecent.addr != addrX);
            assume (forall nodeLessRecent: Node :: nodeLessRecent.idx >= fresh_0.head && nodeLessRecent.idx < fresh_0.tail && nodeLessRecent.addr == fresh_1.addr ==> fresh_1.idx >= nodeLessRecent.idx);
            result := fresh_0.writebuffer[fresh_1.idx].value;
        }
        else
        {
            assume (forall nodeNotFound: Node :: nodeNotFound.idx >= fresh_0.head && nodeNotFound.idx < fresh_0.tail && nodeNotFound.addr != fresh_1.addr);
            result := Mem[fresh_1.addr];
        }
    }

    while (*)
    {
      Call_56:
        atomic  {  // Non-mover
            assert recvThread == tid;
            /* assert Mem[addrFlag] == toRecv && ownerMap[addrFlag] == recvThread && ownerMap[addrX] == recvThread && flagLocal == toRecv && Mem[addrX] == toRd; [Discharged] */
            /* assert Mem[addrFlag] == flagLocal; [Discharged] */
            /* assert ThreadWriteBuffers[recvThread].head == ThreadWriteBuffers[recvThread].tail; [Discharged] */
            /* assert ThreadWriteBuffers[recvThread].writebuffer[ThreadWriteBuffers[recvThread].head].addr != addrFlag && ThreadWriteBuffers[recvThread].writebuffer[ThreadWriteBuffers[recvThread].head].addr != addrX; [Discharged] */
            /* assert ThreadWriteBuffers[senderThread].head == ThreadWriteBuffers[senderThread].tail; [Discharged] */
            havoc Mem;
            havoc newHead;
            assume fresh_5 == ThreadWriteBuffers[recvThread];
            assume fresh_5.head <= fresh_5.tail;
            assume fresh_5.head <= newHead && newHead <= fresh_5.tail;
            assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_5.writebuffer, fresh_5.head, fresh_5.head + 1, Node_addr, Node_value)[addrFlag];
            assume Mem[addrX] == UpdateMemSEG(Mem, fresh_5.writebuffer, fresh_5.head, fresh_5.head + 1, Node_addr, Node_value)[addrX];
        }
    }

  Call_57:
    atomic  {  // Non-mover
        assert ThreadWriteBuffers[senderThread].head == ThreadWriteBuffers[senderThread].tail;
        assert ThreadWriteBuffers[recvThread].writebuffer[ThreadWriteBuffers[recvThread].tail - 1].value == toSend;
        assert ThreadWriteBuffers[recvThread].writebuffer[ThreadWriteBuffers[recvThread].tail - 1].addr == addrFlag;
        assert ThreadWriteBuffers[recvThread].head < ThreadWriteBuffers[recvThread].tail && ThreadWriteBuffers[recvThread].tail == ThreadWriteBuffers[recvThread].head + 1;
        assert Mem[addrFlag] == toRecv && ownerMap[addrFlag] == recvThread && ownerMap[addrX] == recvThread && flagLocal == toRecv && Mem[addrX] == toRd;
        assert recvThread == tid;
        /* assert true; [Discharged] */
        /* call write(addrFlag, toSend); */
        fresh_2 := ThreadWriteBuffers[tid];
        fresh_3 := fresh_2.writebuffer[fresh_2.tail];
        assume fresh_3.idx == fresh_2.tail;
        assume fresh_3.addr == toSend;
        assume fresh_3.value == addrFlag;
        fresh_2.tail := fresh_2.tail + 1;
    }

    while (*)
    {
      Call_58:
        atomic  {  // Non-mover
            assert recvThread == tid;
            /* assert ThreadWriteBuffers[recvThread].head + 1 == ThreadWriteBuffers[recvThread].tail ==> Mem[addrFlag] == toRecv && ownerMap[addrFlag] == recvThread && ownerMap[addrX] == recvThread && Mem[addrX] == toRd && ThreadWriteBuffers[recvThread].writebuffer[ThreadWriteBuffers[recvThread].head].value == toSend && flagLocal == toRecv && ThreadWriteBuffers[recvThread].writebuffer[ThreadWriteBuffers[recvThread].head].addr == addrFlag; [Discharged] */
            /* assert ThreadWriteBuffers[recvThread].head == ThreadWriteBuffers[recvThread].tail ==> Mem[addrFlag] == toSend && ownerMap[addrFlag] == senderThread && Mem[addrX] == toRd && ownerMap[addrX] == senderThread; [Discharged] */
            havoc Mem;
            havoc newHead;
            assume fresh_6 == ThreadWriteBuffers[recvThread];
            assume fresh_6.head <= fresh_6.tail;
            assume fresh_6.head <= newHead && newHead <= fresh_6.tail;
            assume Mem[addrFlag] == UpdateMemSEG(Mem, fresh_6.writebuffer, fresh_6.head, fresh_6.head + 1, Node_addr, Node_value)[addrFlag];
            assume Mem[addrX] == UpdateMemSEG(Mem, fresh_6.writebuffer, fresh_6.head, fresh_6.head + 1, Node_addr, Node_value)[addrX];
            /* assert ThreadWriteBuffers[recvThread].head == ThreadWriteBuffers[recvThread].tail ==> Mem[addrFlag] == toSend && ownerMap[addrFlag] == senderThread && Mem[addrX] == toRd && ownerMap[addrX] == senderThread; [Discharged] */
        }
    }
}



const MAX_INT: int;

const MIN_INT: int;

function ThreadLocal(TID) returns (bool);

axiom (forall t: TID :: { ThreadLocal(t) } ThreadLocal(t) <==> t == tid);

type AllocType;

const unique Alloc: AllocType;

const unique Dealloc: AllocType;

const unique Null: AllocType;

axiom (forall a: AllocType :: a == Alloc || a == Dealloc || a == Null);

function IsAlloc(AllocType) returns (bool);

axiom (forall a: AllocType :: { IsAlloc(a) } IsAlloc(a) <==> a == Alloc);

function IsDealloc(AllocType) returns (bool);

axiom (forall a: AllocType :: { IsDealloc(a) } IsDealloc(a) <==> a == Dealloc);

function IsNull(AllocType) returns (bool);

axiom (forall a: AllocType :: { IsNull(a) } IsNull(a) <==> a == Null);

record Mutex {
owner: TID;
alloc: AllocType;
}

procedure {:isatomic} {:skipmc} lock(m: Mutex);
  modifies Mutex_owner;



implementation lock(m: Mutex)
{
  var ex: Exception;

  lock:
    atomic  {  // Non-mover
        assume m.owner == 0;
        m.owner := tid;
    }
}



procedure {:isatomic} {:skipmc} trylock(m: Mutex) returns (succ: bool);
  modifies Mutex_owner;



implementation trylock(m: Mutex) returns (succ: bool)
{
  var ex: Exception;

  trylock:
    atomic  {  // Non-mover
        succ := m.owner == 0;
        if (succ <==> true)
        {
            m.owner := tid;
        }
    }
}



procedure {:isatomic} {:skipmc} unlock(m: Mutex);
  modifies Mutex_owner;



implementation unlock(m: Mutex)
{
  var ex: Exception;

  unlock:
    atomic  {  // Non-mover
        assert m.owner == tid;
        m.owner := 0;
    }
}



type TID = int;

const unique tid: TID;

const unique tidx: TID;

axiom 0 < tid && 0 < tidx && tid != tidx;

const Tid: TID;

axiom 0 < Tid && tid <= Tid && tidx <= Tid;

record Thread {
id: TID;
interrupted: boolean;
alloc: AllocType;
owner: TID;
}

var Threads: [int]Thread;

const unique NULL_THREAD: Thread;

axiom IsNull(NULL_THREAD.alloc);

type Exception;

const unique ExReturn: Exception;

const unique ExSkip: Exception;

const unique ExBreak: Exception;

const unique ExContinue: Exception;

const unique NullPointerException: Exception;

const unique InterruptedException: Exception;

const unique Error: Exception;

const unique IllegalMonitorStateException: Exception;

const unique RuntimeException: Exception;

axiom subtype(NullPointerException, RuntimeException);

axiom subtype(IllegalMonitorStateException, RuntimeException);

function subtype(Exception, Exception) returns (bool);

axiom (forall e: Exception :: subtype(e, e));

axiom (forall e1: Exception, e2: Exception, e3: Exception :: { subtype(e1, e2), subtype(e2, e3) } subtype(e1, e2) && subtype(e2, e3) ==> subtype(e1, e3));

type boolean;

const unique True: boolean;

const unique False: boolean;

axiom (forall b: boolean :: b == True || b == False);

function toBool(boolean) returns (bool);

axiom (toBool(True) <==> true) && (toBool(False) <==> false);

function toBoolean(bool) returns (boolean);

axiom toBoolean(true) == True && toBoolean(false) == False;

type long = int;

function ReachBetween<T>(f: [T]T, x: T, y: T, z: T) returns (bool);

function ReachAvoiding<T>(f: [T]T, x: T, y: T, z: T) returns (bool);

function ReachBetweenSet<T>(f: [T]T, x: T, z: T) returns ([T]bool);

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetweenSet(f, x, z)[y] } ReachBetweenSet(f, x, z)[y] <==> ReachBetween(f, x, y, z));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetween(f, x, y, z), ReachBetweenSet(f, x, z) } ReachBetween(f, x, y, z) ==> ReachBetweenSet(f, x, z)[y]);

axiom (forall<T> f: [T]T, x: T, z: T :: { ReachBetweenSet(f, x, z) } ReachBetween(f, x, x, x));

axiom (forall<T> f: [T]T, x: T :: ReachBetween(f, x, x, x));

axiom (forall<T> f: [T]T, x: T, y: T, z: T, w: T :: { ReachBetween(f, y, z, w), f[x] } ReachBetween(f, x, f[x], f[x]));

axiom (forall<T> f: [T]T, x: T, y: T :: { f[x], ReachBetween(f, x, y, y) } ReachBetween(f, x, y, y) ==> x == y || ReachBetween(f, x, f[x], y));

axiom (forall<T> f: [T]T, x: T, y: T :: { f[x], ReachBetween(f, x, y, y) } f[x] == x && ReachBetween(f, x, y, y) ==> x == y);

axiom (forall<T> f: [T]T, x: T, y: T :: { ReachBetween(f, x, y, x) } ReachBetween(f, x, y, x) ==> x == y);

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetween(f, x, y, y), ReachBetween(f, x, z, z) } ReachBetween(f, x, y, y) && ReachBetween(f, x, z, z) ==> ReachBetween(f, x, y, z) || ReachBetween(f, x, z, y));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetween(f, x, y, z) } ReachBetween(f, x, y, z) ==> ReachBetween(f, x, y, y) && ReachBetween(f, y, z, z));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachBetween(f, x, y, y), ReachBetween(f, y, z, z) } ReachBetween(f, x, y, y) && ReachBetween(f, y, z, z) ==> ReachBetween(f, x, z, z));

axiom (forall<T> f: [T]T, x: T, y: T, z: T, w: T :: { ReachBetween(f, x, y, z), ReachBetween(f, y, w, z) } ReachBetween(f, x, y, z) && ReachBetween(f, y, w, z) ==> ReachBetween(f, x, y, w) && ReachBetween(f, x, w, z));

axiom (forall<T> f: [T]T, x: T, y: T, z: T, w: T :: { ReachBetween(f, x, y, z), ReachBetween(f, x, w, y) } ReachBetween(f, x, y, z) && ReachBetween(f, x, w, y) ==> ReachBetween(f, x, w, z) && ReachBetween(f, w, y, z));

axiom (forall<T> f: [T]T, u: T, x: T :: { ReachBetween(f, u, x, x) } ReachBetween(f, u, x, x) ==> ReachBetween(f, u, u, x));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { ReachAvoiding(f, x, y, z) } { ReachBetween(f, x, y, z) } ReachAvoiding(f, x, y, z) <==> ReachBetween(f, x, y, z) || (ReachBetween(f, x, y, y) && !ReachBetween(f, x, z, z)));

axiom (forall<T> f: [T]T, u: T, v: T, x: T, p: T, q: T :: { ReachAvoiding(f[p := q], u, v, x) } ReachAvoiding(f[p := q], u, v, x) <==> (ReachAvoiding(f, u, v, p) && ReachAvoiding(f, u, v, x)) || (ReachAvoiding(f, u, p, x) && p != x && ReachAvoiding(f, q, v, p) && ReachAvoiding(f, q, v, x)));

function Equal<T>([T]bool, [T]bool) returns (bool);

function Subset<T>([T]bool, [T]bool) returns (bool);

function Disjoint<T>([T]bool, [T]bool) returns (bool);

function Empty<T>(T) returns ([T]bool);

function Singleton<T>(T) returns ([T]bool);

function Reachable<T>([T,T]bool, T) returns ([T]bool);

function Union<T>([T]bool, [T]bool) returns ([T]bool);

function Intersection<T>([T]bool, [T]bool) returns ([T]bool);

function Difference<T>([T]bool, [T]bool) returns ([T]bool);

function Dereference<T>([T]bool, [T]T) returns ([T]bool);

function Inverse<T>(f: [T]T, x: T) returns ([T]bool);

axiom (forall<T> x: T, y: T :: !Empty(y)[x]);

axiom (forall<T> x: T, y: T :: { Singleton(y)[x] } Singleton(y)[x] <==> x == y);

axiom (forall<T> y: T :: { Singleton(y) } Singleton(y)[y]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Union(S, T)[x] } Union(S, T)[x] <==> S[x] || T[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Union(S, T), S[x] } S[x] ==> Union(S, T)[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Union(S, T), T[x] } T[x] ==> Union(S, T)[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Intersection(S, T)[x] } Intersection(S, T)[x] <==> S[x] && T[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Intersection(S, T), S[x] } S[x] && T[x] ==> Intersection(S, T)[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Intersection(S, T), T[x] } S[x] && T[x] ==> Intersection(S, T)[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Difference(S, T)[x] } Difference(S, T)[x] <==> S[x] && !T[x]);

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { Difference(S, T), S[x] } S[x] ==> Difference(S, T)[x] || T[x]);

axiom (forall<T> x: T, S: [T]bool, M: [T]T :: { Dereference(S, M)[x] } Dereference(S, M)[x] ==> (exists y: T :: x == M[y] && S[y]));

axiom (forall<T> x: T, S: [T]bool, M: [T]T :: { M[x], S[x], Dereference(S, M) } S[x] ==> Dereference(S, M)[M[x]]);

axiom (forall<T> x: T, y: T, S: [T]bool, M: [T]T :: { Dereference(S, M[x := y]) } !S[x] ==> Equal(Dereference(S, M[x := y]), Dereference(S, M)));

axiom (forall<T> x: T, y: T, S: [T]bool, M: [T]T :: { Dereference(S, M[x := y]) } S[x] && Equal(Intersection(Inverse(M, M[x]), S), Singleton(x)) ==> Equal(Dereference(S, M[x := y]), Union(Difference(Dereference(S, M), Singleton(M[x])), Singleton(y))));

axiom (forall<T> x: T, y: T, S: [T]bool, M: [T]T :: { Dereference(S, M[x := y]) } S[x] && !Equal(Intersection(Inverse(M, M[x]), S), Singleton(x)) ==> Equal(Dereference(S, M[x := y]), Union(Dereference(S, M), Singleton(y))));

axiom (forall<T> f: [T]T, x: T :: { Inverse(f, f[x]) } Inverse(f, f[x])[x]);

axiom (forall<T> f: [T]T, x: T, y: T :: { Inverse(f, y), f[x] } Inverse(f, y)[x] ==> f[x] == y);

axiom (forall<T> f: [T]T, x: T, y: T :: { Inverse(f[x := y], y) } Equal(Inverse(f[x := y], y), Union(Inverse(f, y), Singleton(x))));

axiom (forall<T> f: [T]T, x: T, y: T, z: T :: { Inverse(f[x := y], z) } y == z || Equal(Inverse(f[x := y], z), Difference(Inverse(f, z), Singleton(x))));

axiom (forall<T> S: [T]bool, T: [T]bool :: { Equal(S, T) } Equal(S, T) <==> Subset(S, T) && Subset(T, S));

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { S[x], Subset(S, T) } S[x] && Subset(S, T) ==> T[x]);

axiom (forall<T> S: [T]bool, T: [T]bool :: { Subset(S, T) } Subset(S, T) || (exists x: T :: S[x] && !T[x]));

axiom (forall<T> x: T, S: [T]bool, T: [T]bool :: { S[x], Disjoint(S, T), T[x] } !(S[x] && Disjoint(S, T) && T[x]));

axiom (forall<T> S: [T]bool, T: [T]bool :: { Disjoint(S, T) } Disjoint(S, T) || (exists x: T :: S[x] && T[x]));

function Connected<T>(f: [T]T, x: T, y: T) returns (bool);

axiom (forall<T> f: [T]T, x: T, y: T :: { Connected(f, x, y) } Connected(f, x, y) <==> ReachBetween(f, x, y, y) || ReachBetween(f, y, x, x));

function Equals<T,K>([T]K, [T]K) returns (bool);

axiom (forall<T,K> A: [T]K, B: [T]K :: { Equals(A, B) } Equals(A, B) || (exists x: T :: A[x] != B[x]));

axiom (forall<T,K> A: [T]K, B: [T]K, x: T :: { Equals(A, B), A[x] } { Equals(A, B), B[x] } Equals(A, B) <==> A[x] == B[x]);

invariant (forall wb: WriteBuffer :: wb.head <= wb.tail);

invariant (forall tid: TID, i: int, j: int :: { ThreadWriteBuffers[tid].writebuffer[i], ThreadWriteBuffers[tid].writebuffer[j] } i != j ==> ThreadWriteBuffers[tid].writebuffer[i] != ThreadWriteBuffers[tid].writebuffer[j]);

invariant (forall tid1: TID, tid2: TID :: { ThreadWriteBuffers[tid1], ThreadWriteBuffers[tid2] } tid1 != tid2 ==> ThreadWriteBuffers[tid1] != ThreadWriteBuffers[tid2]);


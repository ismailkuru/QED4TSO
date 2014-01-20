/*Structure of TSO MODEL

ThreadWriteBuffers is an array of local thread write buffers
ThreadWriteBuffers	:
						|Thread1's write buf| |Thread2's write buf| |Thread3's write buf| |Thread4's write buf| |Thread5's write buf| .....
							Node:|addr  0X0m|		|addr 0X0k |		|      |				|      |			|        |	
								||						||					||						||					||
								||						||					||						||					||	
								||						||					||						||					||													
								||						||					||						||					||	
								||						||					||						||					||
								||						||					||						||					||	


WriteBuffer:
Each thread gets its own write buffer from ThreadWriteBuffers using owner:TID as key. 
Thread1's write buffer is a WriteBuffer record. This record include and array of Nodes where each node is accessed with address key.
Thread1's write-buffer has head and tail where head is always <= tail. When we add a node , we put it thread1writebuffer[tail] and tail++.
Thread1's write-buffer's head is incremented when we read sth from the buffer.
*/



record Node{
	addr:int;
	value:int;
	idx:int;
}

record WriteBuffer{
	writebuffer:[int]Node ;
	head:int;
	tail:int;
}

var Mem:[int]int;
var ThreadWriteBuffers:[TID]WriteBuffer; 

invariant (forall wb:WriteBuffer :: wb.head <= wb.tail);

invariant (forall tid:TID, i, j: int:: {ThreadWriteBuffers[tid].writebuffer[i] , ThreadWriteBuffers[tid].writebuffer[j]} i != j ==> 
	ThreadWriteBuffers[tid].writebuffer[i] != ThreadWriteBuffers[tid].writebuffer[j]);

invariant (forall tid1,tid2: TID :: {ThreadWriteBuffers[tid1], ThreadWriteBuffers[tid2]} tid1 != tid2 ==> ThreadWriteBuffers[tid1] != ThreadWriteBuffers[tid2]);

function UpdateMemSEG(Memory:[int]int , bf:[int]Node , idx:int, idx2:int, Amap:[Node]int, Vmap:[Node]int) returns([int]int);
axiom(forall addr,i,ix,update:int,  M:[int]int, bf:[int]Node, vmap,amap:[Node]int :: 
	((i <=ix) &&  (i<=update && update<ix )&& (amap[bf[update]] == addr) && 
	(forall ls:int :: (i<=ls && ls<ix && amap[bf[ls]] == addr) ==>ls<=update)) 
		==>(UpdateMemSEG(M, bf,i,ix, amap, vmap)[addr] == vmap[bf[update]] ));
		
axiom(forall addr,i,ix:int,  M:[int]int, bf:[int]Node, vmap,amap:[Node]int :: 
	((i <=ix) &&  (forall update:int :: (i<=update && update<ix ) ==> 
		(amap[bf[update]] != addr))) ==>((UpdateMemSEG(M, bf,i,ix, amap, vmap)[addr] == M[addr] )));
	
procedure  {:isatomic true} write(value: int,addr:int)
{
	var bufferOfthread : WriteBuffer;
	var node: Node;
	
	bufferOfthread := ThreadWriteBuffers[tid];
	node := bufferOfthread.writebuffer[bufferOfthread.tail] ;
	
	assume node.idx == bufferOfthread.tail;
	
	assume node.addr==addr;
	assume node.value == value;
	bufferOfthread.tail := bufferOfthread.tail +1 ;
}
procedure {:isatomic true} read(addr:int) returns (result: int)
{
	var bufferOfthread : WriteBuffer;
	var node:Node;
	var idx : int;
	
	bufferOfthread := ThreadWriteBuffers[tid];
	havoc node;
	
	/*Exists in queue and return the nearest node to tail with the node.addr == addr*/
	if(*){	
		assume (node.idx>=bufferOfthread.head && node.idx < bufferOfthread.tail && bufferOfthread.writebuffer[node.idx].addr == addr )&&  
			   (forall nodeRecent:Node :: nodeRecent.idx>node.idx && nodeRecent.idx <= bufferOfthread.tail ==> 
					nodeRecent.addr != node.addr && nodeRecent.addr != addr );
		
		/*Bir baska deyisle node RECENT*/
		assume (forall nodeLessRecent:Node :: (nodeLessRecent.idx >= bufferOfthread.head &&
				nodeLessRecent.idx < bufferOfthread.tail &&
				nodeLessRecent.addr == node.addr)==>
				(node.idx>= nodeLessRecent.idx)
				);
		
		result := bufferOfthread.writebuffer[node.idx].value;
		
	}
	/*Not found*/
	else{	
	   assume (forall nodeNotFound:Node :: nodeNotFound.idx >= bufferOfthread.head && nodeNotFound.idx < bufferOfthread.tail && nodeNotFound.addr != node.addr);
	   result := Mem[node.addr];
	   
	}
}

procedure {:isatomic true}singleDrain(){
	
	var bufferOfThread:WriteBuffer;
	
	bufferOfThread := ThreadWriteBuffers[tid];
	
	assume bufferOfThread.head < bufferOfThread.tail;
	
	Mem[bufferOfThread.writebuffer[bufferOfThread.head].addr] := bufferOfThread.writebuffer[bufferOfThread.head].value;
	bufferOfThread.head := bufferOfThread.head +1 ;
}

procedure  {:isatomic true} drain(){
	
	var node:Node;
	var bufferOfThread:WriteBuffer;
	var oldHead:int;
	var newHead: int;
	
	bufferOfThread := ThreadWriteBuffers[tid];
	oldHead := bufferOfThread.head;
	
	havoc newHead;
	
	assume oldHead<=newHead && newHead <=bufferOfThread.tail;
	
	bufferOfThread.head := newHead;
	Mem := UpdateMemSEG(Mem,bufferOfThread.writebuffer,oldHead,newHead,Node_addr, Node_value);
}

/*TESTING FUNCTIONS FOR INTERLEAVINGS AND MEMORY UPDATE FUNCTIONALITIY*/
const unique xAddr:int;
const unique yAddr:int;
const unique zAddr:int;
const unique mAddr:int;
const unique kAddr:int;

const unique vAddr:int;

procedure {:isatomic true} testDrain(){
	
	var buf:[int]Node;
	
assume (forall i,j :int :: i!= j ==> buf[i] != buf[j]);
	
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
	
	Mem[zAddr] := 7 ;
	
	Mem:= UpdateMemSEG(Mem,buf,0,6,Node_addr,Node_value);
	
	//assert Mem[mAddr] == 6;
	assert Mem[xAddr] == 5;
	assert Mem[vAddr] == 9;
	assert Mem[kAddr] == 13;
	assert Mem[mAddr] == 21;
	assert false;
	
	assert Mem[zAddr] == 7;
	//assert false;
}
procedure {:isatomic true} readTID(thread:TID ,addr:int)returns (result:int){

	var bufferOfthread : WriteBuffer;
	var node:Node;
	var idx : int;
	
	bufferOfthread := ThreadWriteBuffers[thread];
	havoc node;
	
	/*Exists in queue and return the nearest node to tail with the node.addr == addr*/
	if(*){	
		assume (node.idx>=bufferOfthread.head && node.idx < bufferOfthread.tail && bufferOfthread.writebuffer[node.idx].addr == addr )&&  
			   (forall nodeRecent:Node :: nodeRecent.idx>node.idx && nodeRecent.idx <= bufferOfthread.tail ==> 
					nodeRecent.addr != node.addr && nodeRecent.addr != addr );
		
		/*Bir baska deyisle node RECENT*/
		assume (forall nodeLessRecent:Node :: (nodeLessRecent.idx >= bufferOfthread.head &&
				nodeLessRecent.idx < bufferOfthread.tail &&
				nodeLessRecent.addr == node.addr)==>
				(node.idx>= nodeLessRecent.idx)
				);
		
		result := bufferOfthread.writebuffer[node.idx].value;
	}
	/*Not found*/
	else{	
	   assume (forall nodeNotFound:Node :: nodeNotFound.idx >= bufferOfthread.head && nodeNotFound.idx < bufferOfthread.tail && nodeNotFound.addr != node.addr);
	   result := Mem[node.addr];
	   }
}
procedure {:isatomic true} drainTID(thread:TID){

	var node:Node;
	var bufferOfThread:WriteBuffer;
	var oldHead:int;
	var newHead: int;
	
	bufferOfThread := ThreadWriteBuffers[thread];
	oldHead := bufferOfThread.head;
	
	havoc newHead;
	
	assume oldHead<=newHead && newHead <=bufferOfThread.tail;
	
	bufferOfThread.head := newHead;
	Mem := UpdateMemSEG(Mem,bufferOfThread.writebuffer,oldHead,newHead,Node_addr, Node_value);


}

procedure {:isatomic true} writeTID(thread:TID, value: int,addr:int){

	var bufferOfthread : WriteBuffer;	
	var node: Node;
	
	bufferOfthread := ThreadWriteBuffers[thread];
	node := bufferOfthread.writebuffer[bufferOfthread.tail] ;
	
	assume node.idx == bufferOfthread.tail;
	
	assume node.addr==addr;
	assume node.value == value;
	bufferOfthread.tail := bufferOfthread.tail +1 ;
	assert ThreadWriteBuffers[thread].writebuffer[bufferOfthread.tail-1].value == value;
	assert ThreadWriteBuffers[thread].writebuffer[bufferOfthread.tail-1].addr == addr;
	

}
const unique th1:TID;
const unique th2:TID;
const unique th3:TID;
const unique th4:TID;

/*Testing thread interleavings*/
procedure {:isatomic true}  readLatestSameThread(){

	var toWriteAddr:int;
	var toRead:int;
		
	assume Mem[toWriteAddr] == 100;
	
	call writeTID(th2, 2, toWriteAddr);
	call writeTID(th2, 3, toWriteAddr);
	call writeTID(th2, 4, toWriteAddr);
	call writeTID(th2, 5, toWriteAddr);
	call toRead := readTID(th2, toWriteAddr);
	assert toRead == 5 ;
	
}

procedure {:isatomic true} readLatestDifThread(){

	var toWriteAddr:int;
	var toRead:int;
	
	assume Mem[toWriteAddr] == 100;
	
	call writeTID(th2,2, toWriteAddr);
	call writeTID(th2,3, toWriteAddr);
	
	call writeTID(th3,7, toWriteAddr);
	call writeTID(th3,8,toWriteAddr);
	
	call toRead := readTID(th3,toWriteAddr);
	assert toRead == 8;
	call toRead := readTID(th2,toWriteAddr);
	assert toRead ==3;
}

procedure {:isatomic true} drainTest(){

	var toWriteAddr:int;
	var toRead:int;
	var buf:[int]Node;
	var bufferOfthread:WriteBuffer;
	var bufferOfthread1:WriteBuffer;
	
	bufferOfthread := ThreadWriteBuffers[th3]; 
	bufferOfthread1 := ThreadWriteBuffers[th2];
	
	assume Mem[toWriteAddr] == 100;
	
	call writeTID(th2,2, toWriteAddr);
	call writeTID(th2,3, toWriteAddr);
	
	
	call writeTID(th3,7, toWriteAddr);
	call writeTID(th3,8,toWriteAddr);
	
	Mem := UpdateMemSEG(Mem,bufferOfthread.writebuffer,bufferOfthread.head,bufferOfthread.tail-1,Node_addr,Node_value);
	
	assert Mem[toWriteAddr] == 8;
	
	//UpdateMemSEG yerine Drain cagiridigimda bu assertion gecemez cunku drain buffer in headini set ediyor. !
	/*call toRead := readTID(th3,toWriteAddr);
	assert toRead == 8;*/
	
	call toRead := readTID(th2,toWriteAddr);
	assert toRead ==3;

	Mem := UpdateMemSEG(Mem,bufferOfthread1.writebuffer,bufferOfthread1.head,bufferOfthread1.tail,Node_addr,Node_value);
	
	assert Mem[toWriteAddr] == 3;
	
}

/*CLIENT1 OF TSO MODEL : SEND - RECV*/
var ownerMap:[int]TID;

var toReadX:int;
var toReadF:int;

const unique senderThread:TID;
const unique recvThread:TID;

/*Send-Recv Invariants*/
/*ownermap i sender Thread in ise==>*/

//invariant ((ownerMap[addrFlag] == senderThread)  ==>  (Mem[addrFlag] != 1 && Mem[addrFlag] ==0));
//invariant ((ownerMap[addrFlag] == recvThread) ==> (Mem[addrFlag] != 0 && Mem[addrFlag] ==1));
//invariant ((ownerMap[addrX] == recvThread) ==> Mem[addrX] == sentvalue);
procedure  {:isatomic true} absdrain(addrFlag:int, addrX:int){
	
	var node:Node;
	var bufferOfThread:WriteBuffer;
	var oldHead:int;
	var newHead: int;
	
	bufferOfThread := ThreadWriteBuffers[tid];
	oldHead := bufferOfThread.head;
	
	havoc newHead;
	
	assume oldHead<=newHead && newHead <=bufferOfThread.tail;
	
	bufferOfThread.head := newHead;
	havoc Mem;
	
	assume Mem[addrFlag] == UpdateMemSEG(Mem,bufferOfThread.writebuffer,oldHead,newHead,Node_addr, Node_value)[addrFlag];
	assume Mem[addrX] == UpdateMemSEG(Mem,bufferOfThread.writebuffer,oldHead,newHead,Node_addr, Node_value)[addrX];
}

procedure {:ispublic false} send(addrFlag:int , addrX:int , sentvalue:int){

	var flagLocal:int;
	var bufferOfthread : WriteBuffer;
	var node:Node;
	var idx : int;
	/*
	call flagLocal := read(addrFlag);
	
	while(*){
		assume flagLocal != 0;
		call flagLocal := read(addrFlag);
	}
	*/
	//assume flagLocal != 0;
	//call flagLocal := read(addrFlag);
	havoc flagLocal;
	assume flagLocal == 0;
	
	//while(*){call singleDrain();}
	call absdrain(addrFlag, addrX);
	call write(addrX,sentvalue);
	//while(*){call singleDrain();}
	call absdrain(addrFlag, addrX);
	call write(addrFlag,1);
	//while(*){call singleDrain();}
	call absdrain(addrFlag, addrX);
}

procedure {:ispublic false} recieve(addrFlag:int, addrX:int) returns(result :int){
	
	var flagLocal:int;
	var bufferOfthread : WriteBuffer;
	var node:Node;
	var idx : int;
	
	/*
	call flagLocal := read(addrFlag);
		
	while(*){
		assume flagLocal != 1;
		call flagLocal := read(addrFlag);
	}
	
	assume flagLocal != 1;
	call flagLocal := read(addrFlag);
	
	assume flagLocal == 1;
	*/
	
	havoc flagLocal;
	assume flagLocal == 1;
		
	//while(*){call singleDrain();}//simulated by 
	call absdrain(addrFlag, addrX);
	call result := read(addrX);
	//while(*){call singleDrain();}
	call absdrain(addrFlag, addrX);
	call write(addrFlag , 0);
	//while(*){call singleDrain();}//
	call absdrain(addrFlag, addrX);
}





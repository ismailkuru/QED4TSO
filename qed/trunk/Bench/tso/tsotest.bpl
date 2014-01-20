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
	((i <=ix) &&  (i<=update && update<=ix )&& (amap[bf[update]] == addr) && 
	(forall ls:int :: (i<=ls && ls<=ix && amap[bf[ls]] == addr) ==>ls<=update)) 
		==>(UpdateMemSEG(M, bf,i,ix, amap, vmap)[addr] == vmap[bf[update]] ));
		
axiom(forall addr,i,ix:int,  M:[int]int, bf:[int]Node, vmap,amap:[Node]int :: 
	((i <=ix) &&  (forall update:int :: (i<=update && update<=ix ) ==> 
		(amap[bf[update]] != addr))) ==>((UpdateMemSEG(M, bf,i,ix, amap, vmap)[addr] == M[addr] )));
	
procedure  {:isatomic true} write(value: int,addr:int)
{
	var bufferOfthread : WriteBuffer;
	var node: Node;
	var oldtail :int;
	
	oldtail := bufferOfthread.tail;
	bufferOfthread := ThreadWriteBuffers[tid];
	node := bufferOfthread.writebuffer[bufferOfthread.tail] ;
	
	assume node.idx == bufferOfthread.tail;
	
	assume node.addr==addr;
	assume node.value == value;
	assume bufferOfthread.tail == oldtail +1 ;
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
procedure  {:isatomic true} absdrain(addrrFlag:int, addrrX:int){
	
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
	
	assume Mem[addrrFlag] == UpdateMemSEG(Mem,bufferOfThread.writebuffer,oldHead,newHead,Node_addr, Node_value)[addrrFlag];
	assume Mem[addrrX] == UpdateMemSEG(Mem,bufferOfThread.writebuffer,oldHead,newHead,Node_addr, Node_value)[addrrX];
}

procedure {:isatomic true}singleDrain(){
	
	var bufferOfThread:WriteBuffer;
	var oldhead :int;
	bufferOfThread := ThreadWriteBuffers[tid];
	oldhead := bufferOfThread.head;
	assume bufferOfThread.head < bufferOfThread.tail;
	
	assume Mem[bufferOfThread.writebuffer[bufferOfThread.head].addr] == bufferOfThread.writebuffer[bufferOfThread.head].value;
	assume bufferOfThread.head == oldhead +1 ;
}


/*CLIENT1 OF TSO MODEL : SEND - RECV*/
var ownerMap:[int]TID;

const unique toRd:int;
const unique toRecv:int;
const unique toSend:int;
const unique senderThread:TID;
const unique recvThread:TID;
const unique addrFlag:int;
const unique addrX:int;

/*Send-Recv Invariants*/
invariant (forall node:Node :: node.addr == addrFlag || node.addr == addrX);
invariant (forall node:Node :: node.value == toRd || node.value == toRecv || node.value == toSend );
invariant (ThreadWriteBuffers[senderThread].head == ThreadWriteBuffers[senderThread].tail ==> Mem[addrFlag] == toRecv);
invariant (ThreadWriteBuffers[recvThread].head == ThreadWriteBuffers[recvThread].tail ==> Mem[addrFlag] == toSend);


procedure {:ispublic false} send(){

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
	assume ThreadWriteBuffers[recvThread].head == ThreadWriteBuffers[recvThread].tail;
	
	call flagLocal := read(addrFlag);
	assume flagLocal == toSend;
	
	while(*){call singleDrain();}
	call write(toRd,addrX);
	while(*){call singleDrain();}
	call write(toRecv,addrFlag);
	while(*){call singleDrain();}
}

procedure {:ispublic false} recieve() returns(result :int){
	
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
	
	call flagLocal := read(addrFlag);
	assume flagLocal == toRecv;
		
	while(*){call singleDrain();}//simulated by call absdrain(addrFlag, addrX);
	call result := read(addrX);
	while(*){call singleDrain();}//call absdrain(addrFlag, addrX);
	call write(toSend,addrFlag );
	while(*){call singleDrain();}//call absdrain(addrFlag, addrX);
}





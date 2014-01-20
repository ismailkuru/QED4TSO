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
/*
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
	assume senderThread == tid;
	
	call absdrain(addrFlag, addrX);
	call flagLocal := read(addrFlag);
	assume flagLocal == 0;
	
	call absdrain(addrFlag, addrX);
	call write(addrX,sentvalue);
	call absdrain(addrFlag, addrX);
	call write(addrFlag,1);
	call absdrain(addrFlag, addrX);
}

procedure {:ispublic false} recieve(addrFlag:int, addrX:int) returns(result :int){

	var flagLocal:int;
	
	assume recvThread == tid;
	
	//while(*){
		//havoc flagLocal; // Simulate this
	//}
	//reduce loop
	
	call flagLocal := read(addrFlag);
	assume flagLocal == 1;
	
	call absdrain(addrFlag, addrX);
	call result := read(addrX);
	call absdrain(addrFlag, addrX);
	call write(addrFlag , 0);
	call absdrain(addrFlag, addrX);
}

procedure testSendRecv(){

	var readVal:int;
	
	call send(1,5,10);
	call readVal := recieve(1,5);
	assert readVal == 10;

}

*/

/*CLIENT2 OF TSO : WORK STEALING QUEUE */
/*	class DupQueue{
		Task [];
		int tail; // When head == tail queue is empty
		int head; // elements are taken from head by worker threads to steal elements 
				  // pushing or poping elements to and from queue is done by the owner worker
				  // thread (thread that holds the lock of the queue)
	}
	Properties of the duplicating queue:
		- Take operation either takes an element from the queue or duplicates an element from the queue
		- By allowing duplication , need for putting memory barrier instruction in the Pop  on X86 is reduced ! Our proof has to target this.
		- Duplicate queue never loses an element but our proof has to show that all pushed elements can be returned after a finite number of pop and take
	
	take() operation is called by thiefs . There can be multiple thiefs that may try to steal
	a task at the same time.
    Thief is the only thread that modifies the head field
	Worker is the only thread that modifies the tail field
	
	TSO POINTS : On a TSO architecture the thief may see an outdated tail field or element
				while worker thread may see an outdated head field.
				
				To make these explicit in code headO tailO (outdate versions) are used to state
				potentially outdated ones.
				
	The Global invariants are as the following	:
		1. head >= headO
		2. task[idx] where head<= idx < tailO is valid 
		3. task[idx] where  min(headO, tailMin , tail) // Who cares ?
		4. tail >= head //tailMin li ki

*/

/*Sebastian's scenario is as the following:
	Assume that we get started with pushing one task at the end of the queue
	1. Push task with ID 12 tail and tailO becomes 1
	2. There is a steal of task 12  and head becomes 1 but headO is still 0
	3. There is a pop of task 12 and tail and tailMin become 0
	4. There is a push of task with ID 34 where tail becomes 1 again
	5. By now value of headO and equal to the head
	
	After these, if we want to push another element into the queue  , they claim that new task will be lost

 */


const unique FREE:TID;
const unique NULL_INT:int;


record DupQueue{
	tasks:[int]int ;
	head:int;
	tail:int;
}

var TSKQ:DupQueue;

invariant TSKQ.head<=TSKQ.tail;
  
procedure pop() returns(result:int){

		var tailLocal:int;
		var headLocal:int;
		var resultAddr:int;
		
		//DRAIN 
		call tailLocal := read(TSKQ.tail);
		
		tailLocal := tailLocal -1 ;//call write(tailLocal , tailLocal+1);
		
		//DRAIN
		call write(TSKQ.tail, tailLocal);
		
		//DRAIN
		call headLocal := read(TSKQ.head);
		
		//DRAIN
		call tailLocal := read(TSKQ.tail);
		
		if(headLocal < tailLocal){
									
			//DRAIN
			call result := read( TSKQ.tasks[TSKQ.tail]);
			// DRAIN
			call  write (TSKQ.tasks[TSKQ.tail] , NULL_INT);
			// DRAIN
		}
		
		
		else{
		
				//DRAIN
				
			// Auxiliary ownership transfer 
				call headLocal := read(TSKQ.head);
				//DRAIN 
				call tailLocal := read(TSKQ.tail);
				// DRAIN
				
				// TRY AGAIN
				if (headLocal <= tailLocal) {
					//DRAIN
					call result := read(TSKQ.tasks[TSKQ.tail]);
					//DRAIN
					call write(TSKQ.tasks[TSKQ.tail] , NULL_INT);
					//DRAIN
				} 
				
				else {
					//DRAIN
					call tailLocal := read(TSKQ.tail);
					//DRAIN
					tailLocal := tailLocal +1 ;//call write(tailLocal , tailLocal+1);
					//DRAIN
					call write(TSKQ.tail, tailLocal);
					//DRAIN
					call write(resultAddr, NULL_INT);
					//DRAIN
					call result := read(resultAddr);
					//DRAIN
				}
			
		}	
	}



procedure push(task:int){
	var tailLocal : int ;

	//DRAIN
	call write(TSKQ.tasks[TSKQ.tail], task);
	//DRAIN
	call tailLocal := read(TSKQ.tail);
	tailLocal := tailLocal +1 ;//call write(tailLocal , tailLocal+1);
	//DRAIN
	call write(TSKQ.tail, tailLocal);
	//DRAIN
}


procedure take()returns (result:int){
	
	var headLocal :int ;
	var tailLocal:int;
	var resultAddr:int;
	
	
	//Auxiliary ownership transfer ends
		
		//DRAIN
		call headLocal := read(TSKQ.head);
		//DRAIN
		call tailLocal := read(TSKQ.tail);
		//DRAIN
		
		if (headLocal < tailLocal){
			
		   //DRAIN
		   call  result := read(TSKQ.tasks[TSKQ.head]);
		   //DRAIN
		   call headLocal := read(TSKQ.head);
		   //DRAIN
		   
		   headLocal := headLocal +1 ;
		   //DRAIN
		   call write(TSKQ.head, headLocal);
		   //DRAIN
		
		} else {
		
			call write(resultAddr, NULL_INT);
			//DRAIN
			call result := read(resultAddr);
			//DRAIN
		}

	//Auxiliary ownership transfer ends
}



/*
/*CLIENT3 OF TSO MODEL : Dekker's algorithm*/

/*Dekker with fences*/

const unique ThreadX:TID;
const unique ThreadY:TID;

procedure Fence(){

 Mem :=UpdateMemSEG(Mem,ThreadWriteBuffers[tid].writebuffer,ThreadWriteBuffers[tid].head ,ThreadWriteBuffers[tid].tail, Node_addr,Node_value );

}

procedure  {:isatomic true} absdrainDek(addrX:int){
	
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
	
	assume Mem[addrX] == UpdateMemSEG(Mem,bufferOfThread.writebuffer,oldHead,newHead,Node_addr, Node_value)[addrX];
}

procedure ThreadX(addrX:int, addrY:int){
	
	var tempY :int;
	
	assume tid == ThreadX;
	
	
	call absdrainDek(addrX);
	call write(addrX,1);
	
	call Fence();
	
	call tempY := read(addrY);
	
	//assert tempY == 0 ==> ownerMap[addrY] == ThreadY
	//assert tempY == 1 ==> ownerMap[addrY] == ThreadX
	
	assume tempY==0 ;
	
	//assert ownerMap[addrY] == ThreadY;
	call write(addrX,0);

	
	call absdrainDek(addrX);
}

procedure ThreadY(addrX:int , addrY:int){

	var tempX:int;
	
	assume tid == ThreadY;
    	
	call absdrainDek(addrY);
	
	//assert tid == ThreadY
	call write(addrY, 1);
	
	//assert tid == ThreadY
	call Fence();
	
	//assert tid == ThreadY
	//assert Mem[addrY] == 1;
	call tempX := read(addrX);
	
	// assert tid == ThreadY
	//Mem[addrY] == 1;
	assume tempX== 0 ;
	
	
	// tid == ThreadY
	//tempX == 0 && Mem[addrY] == 1 ;
	// tempX == Mem[addrX] == 0
	
	
	// assert tid == ThreadY;
	// assert Mem[addrY]==1; 
	// assert tempX == 0;  
	// assert Mem[addrX] == tempX;
	call write(addrY, 0);
	
	// assert tid == ThreadY;
	// assert Mem[addrY]==1; 
	// assert tempX == 0;  
	// assert Mem[addrX] == tempX;
	call absdrainDek(addrY);
	
}

*/

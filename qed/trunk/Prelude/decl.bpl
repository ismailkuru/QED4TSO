
type byte;
function OneByteToInt(byte) returns (int);
function TwoBytesToInt(byte, byte) returns (int);
function FourBytesToInt(byte, byte, byte, byte) returns (int);
axiom(forall b0:byte, c0:byte :: {OneByteToInt(b0), OneByteToInt(c0)} OneByteToInt(b0) == OneByteToInt(c0) ==> b0 == c0);
axiom(forall b0:byte, b1: byte, c0:byte, c1:byte :: {TwoBytesToInt(b0, b1), TwoBytesToInt(c0, c1)} TwoBytesToInt(b0, b1) == TwoBytesToInt(c0, c1) ==> b0 == c0 && b1 == c1);
axiom(forall b0:byte, b1: byte, b2:byte, b3:byte, c0:byte, c1:byte, c2:byte, c3:byte :: {FourBytesToInt(b0, b1, b2, b3), FourBytesToInt(c0, c1, c2, c3)} FourBytesToInt(b0, b1, b2, b3) == FourBytesToInt(c0, c1, c2, c3) ==> b0 == c0 && b1 == c1 && b2 == c2 && b3 == c3);

// Mutable
var Mem_BYTE:[int]byte;
var alloc:[int]name;


function Field(int) returns (name);
function Base(int) returns (int);

// Constants
const unique UNALLOCATED:name;
const unique ALLOCATED: name;
const unique FREED:name;

const unique BYTE:name;

function Equal([int]bool, [int]bool) returns (bool);
function Subset([int]bool, [int]bool) returns (bool);
function Disjoint([int]bool, [int]bool) returns (bool);

function Empty() returns ([int]bool);
function Singleton(int) returns ([int]bool);
function Reachable([int,int]bool, int) returns ([int]bool);
function Union([int]bool, [int]bool) returns ([int]bool);
function Intersection([int]bool, [int]bool) returns ([int]bool);
function Difference([int]bool, [int]bool) returns ([int]bool);
function Dereference([int]bool, [int]int) returns ([int]bool);
function Inverse(f:[int]int, x:int) returns ([int]bool);

function AtLeast(int, int) returns ([int]bool);
function Rep(int, int) returns (int);
axiom(forall n:int, x:int, y:int :: {AtLeast(n,x)[y]} AtLeast(n,x)[y] ==> x <= y && Rep(n,x) == Rep(n,y));
axiom(forall n:int, x:int, y:int :: {AtLeast(n,x),Rep(n,x),Rep(n,y)} x <= y && Rep(n,x) == Rep(n,y) ==> AtLeast(n,x)[y]);
axiom(forall n:int, x:int :: {AtLeast(n,x)} AtLeast(n,x)[x]);
axiom(forall n:int, x:int, z:int :: {PLUS(x,n,z)} Rep(n,x) == Rep(n,PLUS(x,n,z)));
axiom(forall n:int, x:int :: {Rep(n,x)} (exists k:int :: Rep(n,x) - x  == n*k));

/*
function AtLeast(int, int) returns ([int]bool);
function ModEqual(int, int, int) returns (bool);
axiom(forall n:int, x:int :: ModEqual(n,x,x));
axiom(forall n:int, x:int, y:int :: {ModEqual(n,x,y)} ModEqual(n,x,y) ==> ModEqual(n,y,x));
axiom(forall n:int, x:int, y:int, z:int :: {ModEqual(n,x,y), ModEqual(n,y,z)} ModEqual(n,x,y) && ModEqual(n,y,z) ==> ModEqual(n,x,z));
axiom(forall n:int, x:int, z:int :: {PLUS(x,n,z)} ModEqual(n,x,PLUS(x,n,z)));
axiom(forall n:int, x:int, y:int :: {ModEqual(n,x,y)} ModEqual(n,x,y) ==> (exists k:int :: x - y == n*k));
axiom(forall x:int, n:int, y:int :: {AtLeast(n,x)[y]}{ModEqual(n,x,y)} AtLeast(n,x)[y] <==> x <= y && ModEqual(n,x,y));
axiom(forall x:int, n:int :: {AtLeast(n,x)} AtLeast(n,x)[x]);
*/

function Array(int, int, int) returns ([int]bool);
axiom(forall x:int, n:int, z:int :: {Array(x,n,z)} z <= 0 ==> Equal(Array(x,n,z), Empty()));
axiom(forall x:int, n:int, z:int :: {Array(x,n,z)} z > 0 ==> Equal(Array(x,n,z), Difference(AtLeast(n,x),AtLeast(n,PLUS(x,n,z)))));


axiom(forall x:int :: !Empty()[x]);

axiom(forall x:int, y:int :: {Singleton(y)[x]} Singleton(y)[x] <==> x == y);
axiom(forall y:int :: {Singleton(y)} Singleton(y)[y]);

/* this formulation of Union IS more complete than the earlier one */
/* (A U B)[e], A[d], A U B = Singleton(c), d != e */
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Union(S,T)[x]} Union(S,T)[x] <==> S[x] || T[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Union(S,T), S[x]} S[x] ==> Union(S,T)[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Union(S,T), T[x]} T[x] ==> Union(S,T)[x]);

axiom(forall x:int, S:[int]bool, T:[int]bool :: {Intersection(S,T)[x]} Intersection(S,T)[x] <==>  S[x] && T[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Intersection(S,T), S[x]} S[x] && T[x] ==> Intersection(S,T)[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Intersection(S,T), T[x]} S[x] && T[x] ==> Intersection(S,T)[x]);

axiom(forall x:int, S:[int]bool, T:[int]bool :: {Difference(S,T)[x]} Difference(S,T)[x] <==> S[x] && !T[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Difference(S,T), S[x]} S[x] ==> Difference(S,T)[x] || T[x]);

axiom(forall x:int, S:[int]bool, M:[int]int :: {Dereference(S,M)[x]} Dereference(S,M)[x] ==> (exists y:int :: x == M[y] && S[y]));
axiom(forall x:int, S:[int]bool, M:[int]int :: {M[x], S[x], Dereference(S,M)} S[x] ==> Dereference(S,M)[M[x]]);
axiom(forall x:int, y:int, S:[int]bool, M:[int]int :: {Dereference(S,M[x := y])} !S[x] ==> Equal(Dereference(S,M[x := y]), Dereference(S,M)));
axiom(forall x:int, y:int, S:[int]bool, M:[int]int :: {Dereference(S,M[x := y])} 
     S[x] &&  Equal(Intersection(Inverse(M,M[x]), S), Singleton(x)) ==> Equal(Dereference(S,M[x := y]), Union(Difference(Dereference(S,M), Singleton(M[x])), Singleton(y))));
axiom(forall x:int, y:int, S:[int]bool, M:[int]int :: {Dereference(S,M[x := y])} 
     S[x] && !Equal(Intersection(Inverse(M,M[x]), S), Singleton(x)) ==> Equal(Dereference(S,M[x := y]), Union(Dereference(S,M), Singleton(y))));

axiom(forall f:[int]int, x:int :: {Inverse(f,f[x])} Inverse(f,f[x])[x]);
axiom(forall f:[int]int, x:int, y:int :: {Inverse(f,y), f[x]} Inverse(f,y)[x] ==> f[x] == y);

axiom(forall f:[int]int, x:int, y:int :: {Inverse(f[x := y],y)} Equal(Inverse(f[x := y],y), Union(Inverse(f,y), Singleton(x))));
axiom(forall f:[int]int, x:int, y:int, z:int :: {Inverse(f[x := y],z)} y == z || Equal(Inverse(f[x := y],z), Difference(Inverse(f,z), Singleton(x))));

axiom(forall S:[int]bool, T:[int]bool :: {Equal(S,T)} Equal(S,T) <==> Subset(S,T) && Subset(T,S));
axiom(forall x:int, S:[int]bool, T:[int]bool :: {S[x], Subset(S,T)} S[x] && Subset(S,T) ==> T[x]);
axiom(forall S:[int]bool, T:[int]bool :: {Subset(S,T)} Subset(S,T) || (exists x:int :: S[x] && !T[x]));
axiom(forall x:int, S:[int]bool, T:[int]bool :: {S[x], Disjoint(S,T), T[x]} !(S[x] && Disjoint(S,T) && T[x]));
axiom(forall S:[int]bool, T:[int]bool :: {Disjoint(S,T)} Disjoint(S,T) || (exists x:int :: S[x] && T[x]));

function Unified([name][int]int) returns ([int]int);
axiom(forall M:[name][int]int, x:int :: {Unified(M)[x]} Unified(M)[x] == M[Field(x)][x]);
axiom(forall M:[name][int]int, x:int, y:int :: {Unified(M[Field(x) := M[Field(x)][x := y]])} Unified(M[Field(x) := M[Field(x)][x := y]]) == Unified(M)[x := y]);
/*************************************************/
/************** Ismail added  TSO abstractions : Primitive Types ***************/

invariant (forall t:thread, i:int :: t.h_value_of_var[i]<=t.t_value_of_var[i]);
invariant (forall t:thread :: t.wb_tail >= t.wb_head);
invariant (forall idx:int , t:thread :: idx >= t.wb_head && idx< t.wb_tail ==> t.h_value_of_var[t.wb[idx].addr]  < t.t_value_of_var[t.wb[idx].addr]);

invariant (forall t:TID , v:variable, i:int  :: 
  (i >= ThreadPool[t].h_value_of_var[v.addr] &&  i < ThreadPool[t].t_value_of_var[v.addr] && v.dirty[tid])  
	==>
  (ThreadPool[t].indx_of_var[v.addr,i] >= ThreadPool[t].wb_head && ThreadPool[t].indx_of_var[v.addr,i] < ThreadPool[t].wb_tail ));
	
invariant (forall v1,v2:variable :: v1!= v2 <==> v1.addr != v2.addr);
invariant (forall t1,t2:TID :: ThreadPool[t1] != ThreadPool[t2] <==> t1 != t2);
invariant(forall index_addr:int :: ref_to_variable[index_addr].value[ADDR]== index_addr);

record variable{

	value:int ; // value of variable : Note: ref type may be used
	addr:int; // addr of variable : Note: ref tpye may be used.
	ver:int ; // global version number of a variable

	dirty:[TID]bool; // is there is any write in any of buffer for this variable then it is false
	allocation:bool;
	
	valInbuffers:[TID]int ; // value of recent write in ThreadPool[tid]
	indxInbuffers:[TID]int; // index of recent value in ThreadPool[tid]
}


record assignment{
	addr:int;
	value:int ;
}

record thread{
	
	t_id : TID;
	wb_head:int;
	wb_tail:int;
	wb:[int]assignment;
	
	value_of_var:[int, int]int;// variabes to its values in thread tid
	h_value_of_var:[int]int; // h_value_of_var<=idx < t_value_of_var
	t_value_of_var:[int]int; //  h_value_of_var<=idx < t_value_of_var
	indx_of_var:[int,int]int; // addr , h_value_of_var<=idx < t_value_of_var ==> wb_head <= indx_int_thread_buf < wb_tail
	
}


var ThreadPool:[TID]thread;
var thread_local_to_variable:[int]variable;


procedure {:isatomic true} drain_last()

{
	
	
var bastakiAdres:int ;

bastakiAdres := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
	
assert (ThreadPool[tid].t_value_of_var[bastakiAdres] == ThreadPool[tid].h_value_of_var[bastakiAdres] +1);

assert ((ThreadPool[tid].wb_head + 1 ) == ThreadPool[tid].wb_tail);


assert thread_local_to_variable[bastakiAdres].dirty[tid];
assert 	ThreadPool[tid].indx_of_var[bastakiAdres,ThreadPool[tid].h_value_of_var[bastakiAdres]] == ThreadPool[tid].wb_head;
assert	ThreadPool[tid].indx_of_var[bastakiAdres,ThreadPool[tid].t_value_of_var[bastakiAdres]] == ThreadPool[tid].wb_tail;	
		
thread_local_to_variable[bastakiAdres].value := 
      ThreadPool[tid].value_of_var[bastakiAdres,ThreadPool[tid].h_value_of_var[bastakiAdres]];  
thread_local_to_variable[bastakiAdres].ver := 
    thread_local_to_variable[bastakiAdres].ver + 1;
thread_local_to_variable[bastakiAdres].dirty[tid] := false;

// Violates		
ThreadPool[tid].h_value_of_var[bastakiAdres] := ThreadPool[tid].h_value_of_var[bastakiAdres] + 1;
ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
		
assert  ThreadPool[tid].h_value_of_var[bastakiAdres] == ThreadPool[tid].t_value_of_var[bastakiAdres]; 
assert  !thread_local_to_variable[bastakiAdres].dirty[tid];
assert 	ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;	
assert false;			
}

procedure {:isatomic true} write_to_ptr(taddr:variable, offset:int, sval:int){
	
	var as:assignment;
	var bastakiAdres :int;

	var oldH :int ;
	var oldT:int;


	
	assume offset >=0 ;
	bastakiAdres := taddr.addr+offset;
	assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head ;
	assert ThreadPool[tid].t_value_of_var[bastakiAdres] == ThreadPool[tid].h_value_of_var[bastakiAdres];

	assert ThreadPool[tid].indx_of_var[bastakiAdres, ThreadPool[tid].h_value_of_var[bastakiAdres]] == ThreadPool[tid].wb_head ;
	assert ThreadPool[tid].indx_of_var[bastakiAdres, ThreadPool[tid].h_value_of_var[bastakiAdres]] == ThreadPool[tid].indx_of_var[bastakiAdres, ThreadPool[tid].t_value_of_var[bastakiAdres]];
	
	oldH := ThreadPool[tid].h_value_of_var[bastakiAdres];
	oldT := ThreadPool[tid].t_value_of_var[bastakiAdres];

	as.value := sval;
	as.addr := bastakiAdres;
	
	thread_local_to_variable[bastakiAdres].valInbuffers[tid] := sval;
	thread_local_to_variable[bastakiAdres].dirty[tid]:= true; // burada 0'inci adresten sonra her bir variable size'inda bu offsete kadar olan tum variable'lar dirty mi ?
	thread_local_to_variable[bastakiAdres].indxInbuffers[tid] := ThreadPool[tid].wb_tail;
	
	ThreadPool[tid].wb[ThreadPool[tid].wb_tail] := as;
	ThreadPool[tid].value_of_var[bastakiAdres,ThreadPool[tid].t_value_of_var[bastakiAdres]] := as.value;
	ThreadPool[tid].indx_of_var[bastakiAdres, ThreadPool[tid].t_value_of_var[bastakiAdres]] := ThreadPool[tid].wb_tail;
	
	
	
	////
	
	assert as.addr ==  bastakiAdres;
	assert as.value == sval;
	assert ThreadPool[tid].t_value_of_var[as.addr] == ThreadPool[tid].h_value_of_var[as.addr];
	
	
	assert ThreadPool[tid].indx_of_var[bastakiAdres,oldH] == ThreadPool[tid].wb_head ;	
	assert ThreadPool[tid].indx_of_var[bastakiAdres,oldT] == ThreadPool[tid].wb_tail ;
	
	ThreadPool[tid].t_value_of_var[bastakiAdres] := ThreadPool[tid].t_value_of_var[bastakiAdres]+1;
	
	ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
	
	assert false;
}


procedure {:isatomic true} write(taddr:variable, sval : int){

	var as:assignment;
	var oldH :int ;
	var oldT:int;
	//assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head ;
	//assert ThreadPool[tid].t_value_of_var[ThreadPool[tid].wb[ThreadPool[tid].wb_tail].addr] == ThreadPool[tid].t_value_of_var[ThreadPool[tid].wb[ThreadPool[tid].wb_tail].addr];
	
	assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head ;
	assert ThreadPool[tid].t_value_of_var[taddr.addr] == ThreadPool[tid].h_value_of_var[taddr.addr];
	assert ThreadPool[tid].indx_of_var[taddr.addr, ThreadPool[tid].h_value_of_var[taddr.addr]] == ThreadPool[tid].wb_head ;
	assert ThreadPool[tid].indx_of_var[taddr.addr, ThreadPool[tid].h_value_of_var[taddr.addr]] == ThreadPool[tid].indx_of_var[taddr.addr, ThreadPool[tid].t_value_of_var[taddr.addr]];

	oldH := ThreadPool[tid].h_value_of_var[taddr.addr];
	oldT := ThreadPool[tid].t_value_of_var[taddr.addr];
	
	as.value := sval;
	as.addr := taddr.addr;
	
	taddr.valInbuffers[tid] :=  sval;
	taddr.dirty[tid] := true;
	taddr.indxInbuffers[tid] := ThreadPool[tid].wb_tail;

	ThreadPool[tid].wb[ ThreadPool[tid].wb_tail] := as;
	
	ThreadPool[tid].value_of_var[taddr.addr,ThreadPool[tid].t_value_of_var[taddr.addr]] := as.value;
	ThreadPool[tid].indx_of_var[taddr.addr,ThreadPool[tid].t_value_of_var[taddr.addr]] := ThreadPool[tid].wb_tail;

	assert as.addr == taddr.addr;
	assert as.value == sval;
	assert ThreadPool[tid].t_value_of_var[as.addr] == ThreadPool[tid].h_value_of_var[as.addr];
	
	
	assert ThreadPool[tid].indx_of_var[taddr.addr,oldH] == ThreadPool[tid].wb_head ;	
	assert ThreadPool[tid].indx_of_var[taddr.addr,oldT] == ThreadPool[tid].wb_tail ;
	
	ThreadPool[tid].t_value_of_var[taddr.addr] := ThreadPool[tid].t_value_of_var[taddr.addr]+1;
	
	ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
	
	assert false;
}


procedure {:isatomic true} read_from_ptr(toRead:variable, offset:int) returns(result:int){

	
	if(*){
		//assume tid == recvThread || tid == senderThread;
		assume offset >= 0;
		assume ThreadPool[tid].t_value_of_var[toRead.addr] == ThreadPool[tid].h_value_of_var[ toRead.addr] ;
		assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
		assume (!toRead.dirty[tid]);
		
		result := toRead.value;
	
	}
	else{
		assume offset >= 0;
		assume ThreadPool[tid].t_value_of_var[toRead.addr] > ThreadPool[tid].h_value_of_var[toRead.addr] ;
		assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
		assume (toRead.dirty[tid]);
	
		result := toRead.valInbuffers[tid];

	}
	


}
procedure {:isatomic true} read(toRead:variable) returns(result : int ){

	if(*){
	//assume tid == recvThread || tid == senderThread;
		assume ThreadPool[tid].t_value_of_var[toRead.addr] == ThreadPool[tid].h_value_of_var[ toRead.addr] ;
		assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
		assume (!toRead.dirty[tid]);
		
		result := toRead.value;
	
	}
	else{
	
		assume ThreadPool[tid].t_value_of_var[toRead.addr] > ThreadPool[tid].h_value_of_var[toRead.addr] ;
		assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
		assume (toRead.dirty[tid]);
	
		result := toRead.valInbuffers[tid];

	}
}
/*********************************************Primitive types for tso**********************************************************/



/************Ismail addded for TSO non-primitive heap types**************/


type field ;

const unique ADDR :field ;
const unique VAL : field ;
const unique VERSION:field ;
const unique NEXT_PTR : field ;
const unique DIRTY: field ;
const  unique ALLOC : field ; // Allocation'i da VALUE ile erisilebilinir hale getir
const unique REC_VAL : field ;
const unique INDX_BUF : field ;



// Probably ADDR, VAL and NEXT_PTR is enough !!!
axiom (forall fld : field ::fld == ADDR ||
	fld == VAL ||
	fld == VERSION ||
	fld == NEXT_PTR ||
	fld == DIRTY ||
	fld == ALLOC ||
	fld == REC_VAL ||
	fld == INDX_BUF);


record ref{
	addr : int ;
}
	
record variable_heap{
	
	value:[field]int;// value of variable : holds any addr of any type.
	ver:int ; // global version number of a variable.
	//heapState:allocation;
	dirty:[TID,field]bool; // is there is any write in any of buffer for this variable then it is false
	valInbuffers:[TID,field]int ; // value of recent write in ThreadPool[tid]
	indxInbuffers:[TID]int; // index of recent value in ThreadPool[tid]
}


record assignment_heap{
	addr:int;
	f_n:field;
	value:int ;
}

// assignment 

record thread_heap{
	
	t_id : TID;
	wb_head:int;
	wb_tail:int;
	wb:[int]assignment;
	
	value_of_var:[int, int]int;// variabes to its values in thread tid
	h_value_of_var:[int]int; // h_value_of_var<=idx < t_value_of_var
	t_value_of_var:[int]int; //  h_value_of_var<=idx < t_value_of_var
	indx_of_var:[int,int]int; // addr , h_value_of_var<=idx < t_value_of_var ==> wb_head <= indx_int_thread_buf < wb_tail
		
}



//var ThreadPool:[TID]thread;
var ref_to_variable:[int]variable;	

var var_to_reference:[int]ref;






procedure {:isatomic true} drain_last_heap()
{
		
		
	var bastakiAdres:int ;
	var bastakiFieldNum:field;
	var bastakiValue : int;
	var dirtySet : bool;
	
	var ref_to_flush : ref;
	
	
	bastakiAdres := ThreadPool[tid].wb[ThreadPool[tid].wb_head].addr;
	bastakiFieldNum := ThreadPool[tid].wb[ThreadPool[tid].wb_head].f_n;
	bastakiValue := ThreadPool[tid].wb[ThreadPool[tid].wb_head].value;
	
	//ref_to_flush := var_to_reference[bastakiAdres];
	
	assert (ThreadPool[tid].t_value_of_var[bastakiAdres] == ThreadPool[tid].h_value_of_var[bastakiAdres] +1);
	assert ((ThreadPool[tid].wb_head + 1 ) == ThreadPool[tid].wb_tail);


	assert ref_to_variable[bastakiAdres].dirty[tid,bastakiFieldNum];
	assert 	ThreadPool[tid].indx_of_var[bastakiAdres,ThreadPool[tid].h_value_of_var[bastakiAdres]] == ThreadPool[tid].wb_head;
	assert	ThreadPool[tid].indx_of_var[bastakiAdres,ThreadPool[tid].t_value_of_var[bastakiAdres]] == ThreadPool[tid].wb_tail;	
	

	ref_to_variable[bastakiAdres].value[bastakiFieldNum] := 
		  ThreadPool[tid].value_of_var[bastakiAdres,ThreadPool[tid].h_value_of_var[bastakiAdres]];  
	
	
	// same addresses same variables ??
	assert ref_to_variable[bastakiAdres] == ref_to_variable[ThreadPool[tid].value_of_var[bastakiAdres,ThreadPool[tid].h_value_of_var[bastakiAdres]]];
	
	ref_to_variable[bastakiAdres].value[VERSION] := 
		ref_to_variable[bastakiAdres].value[VERSION] + 1;
	


	ref_to_variable[bastakiAdres].dirty[tid, bastakiFieldNum] := false;	

	// Violates		
	ThreadPool[tid].h_value_of_var[bastakiAdres] := ThreadPool[tid].h_value_of_var[bastakiAdres] + 1;
	ThreadPool[tid].wb_head := ThreadPool[tid].wb_head + 1;
			
	assert  ThreadPool[tid].h_value_of_var[bastakiAdres] == ThreadPool[tid].t_value_of_var[bastakiAdres]; 
	assert  !ref_to_variable[bastakiAdres].dirty[tid,bastakiFieldNum];
	assert 	ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;	
	assert false;			
}


procedure {:isatomic true} write_heap(taddrR:ref, sval:int, fld:field){

	var as:assignment;
	var oldH :int ;
	var oldT:int;
	var taddr : variable;
	//var sval : variable;
	var dirtySet:bool;
	
	taddr := ref_to_variable[taddrR.addr];
	
	assert taddr.value[ADDR] == taddrR.addr;
	assert ThreadPool[tid].wb_tail == ThreadPool[tid].wb_head ;
	
	assert ThreadPool[tid].t_value_of_var[taddr.value[ADDR]] == ThreadPool[tid].h_value_of_var[taddr.value[ADDR]];
	
	assert ThreadPool[tid].indx_of_var[taddr.value[ADDR], ThreadPool[tid].h_value_of_var[taddr.value[ADDR]]] == ThreadPool[tid].wb_head ;
	
	assert ThreadPool[tid].indx_of_var[taddr.value[ADDR], ThreadPool[tid].h_value_of_var[taddr.value[ADDR]]] == 
			ThreadPool[tid].indx_of_var[taddr.value[ADDR], ThreadPool[tid].t_value_of_var[taddr.value[ADDR]]];

	
 
	oldH := ThreadPool[tid].h_value_of_var[taddr.value[ADDR]];
	oldT := ThreadPool[tid].t_value_of_var[taddr.value[ADDR]];
	
	as.value := sval;
	as.addr := taddr.value[ADDR];
	as.f_n :=  fld;
	
	taddr.valInbuffers[tid,fld] :=  sval;
	taddr.dirty[tid,fld] := true;
	taddr.indxInbuffers[tid] := ThreadPool[tid].wb_tail;
	
	ThreadPool[tid].wb[ ThreadPool[tid].wb_tail] := as;
	
	ThreadPool[tid].value_of_var[taddr.value[ADDR],ThreadPool[tid].t_value_of_var[taddr.value[ADDR]]] := as.value;
	ThreadPool[tid].indx_of_var[taddr.value[ADDR],ThreadPool[tid].t_value_of_var[taddr.value[ADDR]]] := ThreadPool[tid].wb_tail;

	assert as.addr == taddr.value[ADDR];
	assert as.value == sval;
	assert ThreadPool[tid].t_value_of_var[as.addr] == ThreadPool[tid].h_value_of_var[as.addr];
	
	
	assert ThreadPool[tid].indx_of_var[taddr.value[ADDR],oldH] == ThreadPool[tid].wb_head ;	
	assert ThreadPool[tid].indx_of_var[taddr.value[ADDR],oldT] == ThreadPool[tid].wb_tail ;
	
	ThreadPool[tid].t_value_of_var[taddr.value[ADDR]] := ThreadPool[tid].t_value_of_var[taddr.value[ADDR]]+1;
	
	ThreadPool[tid].wb_tail := ThreadPool[tid].wb_tail + 1;
	
	assert false;
}

procedure {:isatomic true} read_heap(toReadR:ref, fld:field) returns(result : int ){

	var toRead : variable;
	toRead := ref_to_variable[toReadR.addr];

		if(*){
			
			assume ThreadPool[tid].t_value_of_var[toRead.value[ADDR]] == ThreadPool[tid].h_value_of_var[ toRead.value[ADDR]] ;
			assume ThreadPool[tid].wb_head == ThreadPool[tid].wb_tail;
			assume (!toRead.dirty[tid,fld]);
		//	assume (!toReadR.fieldsMap[fld]);
			
			result := toRead.value[fld];
		
		}
		else{
		
			assume ThreadPool[tid].t_value_of_var[toRead.value[ADDR]] > ThreadPool[tid].h_value_of_var[toRead.value[ADDR]] ;
			assume ThreadPool[tid].wb_head < ThreadPool[tid].wb_tail;
			assume (toRead.dirty[tid,fld]);
			//assume (toReadR.fields[fld]);
		
			result := toRead.valInbuffers[tid,fld];

		}
}
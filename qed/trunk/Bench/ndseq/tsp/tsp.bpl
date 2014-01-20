
record TourElement
{
	prefix: [int]int; // size: MAX_TOUR_SIZE
	conn: [int]bool;
	last: int;
	prefix_weight: int;
	lower_bound: int;
	mst_weight: int;
}

const MAX_TOUR_SIZE: int;
axiom MAX_TOUR_SIZE == 32;
const MAX_NUM_TOURS: int;
axiom MAX_NUM_TOURS == 5000;
const BIGINT: int;
axiom BIGINT == 2000000;
const END_TOUR: int;
axiom END_TOUR == -1;
const ALL_DONE: int;
axiom ALL_DONE == -1;
const nWorkers: int;
axiom nWorkers == 2;
const TspSize: int;
axiom TspSize == MAX_TOUR_SIZE;
const StartNode: int;
axiom StartNode == 0;
const NodesFromEnd: int;
axiom NodesFromEnd == 12;

const weights: [int,int]int;
var Done: int;
// var PrioQLast: int;
var MinTourLen: int; //  BIGINT
var MinTour: [int]int;
var PrioQ: PrioQueue int; // [int]PrioQElement;
var TourStack: Stack int; //[int]int;
// var TourStackTop: int; // -1
var Tours: [int]TourElement;

/* non-static member variables, used by recusive_solve and visit_nodes */
//var CurDist: int;
//var PathLen: int;
//var Visit: [int]int;
//var Path: [int]int;
//var visitNodes: int;

procedure main()
{
	var curr: int;
	var currTour: TourElement;
	var dummy: int;	

	/* Initialize first tour */
	Tours[0].prefix[0] := StartNode;
	assume(forall k:int :: Tours[0].conn[k] == false);
	Tours[0].conn[0] := true;
	Tours[0].last := 0;
	Tours[0].prefix_weight := 0;
	call dummy := calc_bound(0);

	/* Initialize the priority queue structures */
	    //PrioQLast := 1;
	    call prioqueue_enqueue(PrioQ, 0, Tours[0].lower_bound);
	    
	    /* Put all unused tours in the free tour stack */
	    //for (i = MAX_NUM_TOURS - 1; i > 0; i--)
	    //	TspSolver.TourStack[++TspSolver.TourStackTop] = i;
	    
	    /* create worker threads */
	    foreach {:parallel} (*) // make foreach take a star
	    {
	       atomic { // TourLock
	       	    if (curr != -1) { // put back the tour
		      // TourStack[++TourStackTop] = curr;
		      call stack_push(TourStack, curr);
		    }
	       }
	       call curr := find_solvable_tour();
	       call recursive_solve(curr);
	    } //  end foreach
} // end main

/*
     * find_solvable_tour():
     *
     * Used by both the normal TSP program (called by get_tour()) and
     * the RPC server (called by RPCserver()) to return the next solvable
     * (sufficiently short) tour.
     *
     */
    procedure find_solvable_tour() returns (curr: int)
    {
	var i, left, right, child, index: int;
	var priority, last: int;
	var b: bool;
	
	atomic { // TourLock

	    if (Done != 0) { 
		curr := -1; 
		return;
	    }
	
	    //while(PrioQLast != 0) {
	    call b := prioqueue_isempty(PrioQ);
	    while(!b) {
		call curr, priority := prioqueue_dequeue(PrioQ);
		if (priority >= MinTourLen) {
		    /* We're done -- there's no way a better tour could be found. */
		    Done := 1;
		    curr := -1;
		    return;
		}

		last := Tours[curr].last;
	    
		/* If we're within `NodesFromEnd' nodes of a complete tour, find
		   minimum solutions recursively.  Else, split the tour. */
		if (last < TspSize || last < 1) {
		    if (last >= (TspSize - NodesFromEnd - 1)) {
		      return;
		    } else {
		      call split_tour(curr);	/* The current tour is too long, */
		    }
		}				/* to solve now, break it up.	 */
		// TourStack[++TourStackTop] := curr; /* Free tour. */
		call stack_push(TourStack, curr);
		
		call b := prioqueue_isempty(PrioQ);
	    }
	    /* Ran out of candidates - DONE! */
	    Done := 1;
	    curr := -1;
	    return;
	}
    }

/*
procedure less_than(x: PrioQElement, y: PrioQElement) returns (r : bool){
	atomic {
	  r := ((x.priority  < y.priority) || 
		(x.priority == y.priority) && 
		(Tours[x.index].last > Tours[y.index].last));
        }
    }
*/

procedure calc_bound(curr_index: int) returns (r: int)
{
	var i, j, wt, wt1, wt2: int;
	var curr: TourElement;

	curr := Tours[curr_index];
	
	atomic { //TourLock

	    /*
	     * wt1: the value of the edge with the lowest weight from the node
	     *	    we're testing to another unconnected node.
	     * wt2: the value of the edge with the second lowest weight
	     */

	    /* if we have one unconnected node */
	       if(curr.last == (TspSize - 2)) {
	         i := 0;
		 while(i < TspSize) {
		   if(*) { //((curr.conn & (1<<i))==0)  unconnected node
		     /* we have found the one unconnected node */
		     curr.prefix[TspSize - 1] := i;
		     curr.prefix[TspSize] := StartNode;

		     /* add edges to and from the last node */
		     curr.prefix_weight := curr.prefix_weight + weights[curr.prefix[TspSize],i] +
		     			   		      	weights[i,curr.prefix[StartNode]];
		     if(curr.prefix_weight < MinTourLen) {
		       /* Store our new best path and its weight. */
		       call set_best(curr.prefix_weight, curr.prefix);
		     }

		     /* De-allocate this tour so someone else can use it */
		     curr.lower_bound := BIGINT;

		     // TourStack[++TourStackTop] := curr_index; /* Free tour. */
		     call stack_push(TourStack, curr_index);
		     r := END_TOUR;
		     return;
		   }
		   i := i + 1;
		 }
	       } 

	       curr.mst_weight := 0;
	       
	    /*
	     * Add up the lowest weights for edges connected to vertices
	     * not yet used or at the ends of the current tour, and divide by two.
	     * This could be tweaked quite a bit.  For example:
	     *   (1) Check to make sure that using an edge would not make it
	     *       impossible for a vertex to have degree two.
	     *   (2) Check to make sure that the edge doesn't give some
	     *       vertex degree 3.
	     */

	       if (curr.last != TspSize - 1) {
		 i := 0;
		 while(i < TspSize) {
		    if (curr.conn[i] == true) {
		      i := i + 1;
		      continue;
		    }
		    j := 0;
		    wt1 := BIGINT;
		    wt2 := BIGINT;
		    while(j < TspSize) {
			/* Ignore j's that are not connected to i (global->weights[i][j]==0), */
			/* or that are already in the tour and aren't either the      */
			/* first or last node in the current tour.		      */
			wt := weights[i,j];
			if ((wt==0) || ((curr.conn[i] == true) && (j != curr.prefix[0]) &&
					(j != curr.prefix[curr.last]))) {
			    j := j + 1;
			    continue;
			}
			
			/* Might want to check that edges go to unused vertices */
			if (wt < wt1) {
			    wt2 := wt1;
			    wt1 := wt;
			} else {
			  if (wt < wt2) {
			     wt2 := wt;
			  }
			}
			j := j + 1;  
		    } // end while

		    /* At least three unconnected nodes? */
		    if (wt2 != BIGINT) {
		      curr.mst_weight := curr.mst_weight + ((wt1 + wt2) / 2);
		    }
		    /* Exactly two unconnected nodes? */
		    else {
		      if (wt1 != BIGINT) {
		        curr.mst_weight := curr.mst_weight + wt1;
		      }
		    }
		    i := i + 1;
		} // end while
		curr.mst_weight := curr.mst_weight + 1;
	    }
	    curr.lower_bound := curr.mst_weight + curr.prefix_weight;
	    r := curr_index;
	    return;
	} // end atomic
} // end calc_bound

    /*
     * set_best():
     *
     *  Set the global `best' value.
     *
     */
    procedure set_best(best: int, path: [int]int) {
        var i: int;    	

	if (best >= MinTourLen) {
	    return;
	}
	atomic {  // MinLock
	    if (best < MinTourLen) {
		MinTourLen := best;
		i := 0;
		while(i < TspSize) {
		    MinTour[i] := path[i];
		    i := i + 1;
		}
	    }
	}
    }

    /*
     * split_tour():
     *
     *  Break current tour into subproblems, and stick them all in the priority
     *  queue for later evaluation.
     *
     */
procedure split_tour(curr_ind: int) {
	var n_ind, last_node, wt: int;
	var i, pq, parent, index, priority: int;
	var curr: TourElement;
	var t1, t2, t3: bool;
	var new_: TourElement;

	atomic { // TourLock

	    curr := Tours[curr_ind];
	
	    /* Create a tour and add it to the priority Q for each possible
	       path that can be derived from the current path by adding a single
	       node while staying under the current minimum tour length. */
	
	    if (curr.last != (TspSize - 1)) {
	    
		last_node := curr.prefix[curr.last];
		i := 0;
		while(i < TspSize) {
		    /*
		     * Check: 1. Not already in tour
		     *	      2. Edge from last entry to node in graph
		     *	and   3. Weight of new partial tour is less than cur min.
		     */
		    wt := weights[last_node,i];
		    t1 := (curr.conn[i] == false);
		    t2 := (wt != 0);
		    t3 := (curr.lower_bound + wt) <= MinTourLen;
		    if (t1 && t2 && t3) {
		        call n_ind := new_tour(curr_ind, i);
			if (n_ind == END_TOUR) {
			    i := i + 1;
			    continue;
			}
			/*
			 * If it's shorter than the current best tour, or equal
			 * to the current best tour and we're reporting all min
			 * length tours, put it on the priority q.
			 */
			new_ := Tours[n_ind];
		    
			// assume (PrioQLast < MAX_NUM_TOURS-1);

			call prioqueue_enqueue(PrioQ, n_ind, new_.lower_bound);

		   } // end if t1 t2 t3
		} // end while
	    }
	} // end atomic
    }

    /*
     * new_tour():
     *
     *    Create a new tour structure given an existing tour structure and
     *  the next edge to add to the tour.  Returns the index of the new structure.
     *
     */
procedure new_tour(prev_index: int, move: int) returns (index: int){
	    var i: int;
	    var curr, prev: TourElement;
	    var b: bool;

	    atomic { // TourLock
	        index := 0;

		// assume (TourStackTop >= 0);
		call b := stack_isempty(TourStack);
		assume !b;
		//index = TourStack[TourStackTop--];
		call index := stack_pop(TourStack);

		curr := Tours[index];
		prev := Tours[prev_index];
       
		i := 0;
		while(i < TspSize) {
		    curr.prefix[i] := prev.prefix[i];
		    curr.conn := prev.conn;
		    i := i + 1;
		}
		curr.last := prev.last;
		curr.prefix_weight := prev.prefix_weight + 
		    weights[curr.prefix[curr.last],move];
		curr.last := curr.last + 1;
		curr.prefix[curr.last] := move;
		assume curr.conn[move] == false;
		curr.conn[move] := true;
	
		call index := calc_bound(index);
		// return;
	    }
	}


    /*
     *   recursive_solve(curr_ind)
     *
     *	We're now supposed to recursively try all possible solutions
     *	starting with the current tour.  We do this by copying the
     *	state to local variables (to avoid unneeded conflicts) and
     *	calling visit_nodes to do the actual recursive solution.
     *
     */
procedure recursive_solve(index: int) {
	var i, j: int;
	var curr: TourElement;
	
	var CurDist: int;
	var PathLen: int;
	var Visit: [int]int;
	var Path: [int]int;
	var visitNodes: int;

	curr := Tours[index];

	CurDist := curr.prefix_weight;
	PathLen := curr.last + 1;
	
	i := 0;
	while (i < TspSize)
	{
	  Visit[i] := 0;
	  i := i + 1;
	}
	
	i := 0;
	while(i < PathLen) {
	    Path[i] := curr.prefix[i];
	    Visit[Path[i]] := 1;
	    i := i + 1;
	}

	assume (PathLen <= TspSize);
	
	call visit_nodes(Path[PathLen-1]);
    }

    /*
     *   visit_nodes()
     *
     *       Exhaustively visits each node to find Hamilton cycle.
     *       Assumes that search started at node from.
     *
     */
procedure visit_nodes(from: int) {
	var i: int;
	var dist, last: int;

	var CurDist: int;
	var PathLen: int;
	var Visit: [int]int;
	var Path: [int]int;
	var visitNodes: int;

	visitNodes := visitNodes + 1;	
	
	i := 1;
	while(i < TspSize) {
	    if (Visit[i]!=0) { i := i + 1; continue; }	/* Already visited. */

	    dist := weights[from,i];
	    if (dist == 0) 
		{ i := i + 1; continue; } /* Not connected. */

	    if (CurDist + dist > MinTourLen) 
		{ i := i + 1; continue; } /* Path too long. */
	    
	    /* Try next node. */
	    Visit[i] := 1;
	    Path[PathLen] := i;
	    PathLen := PathLen + 1;
	    CurDist := CurDist + dist;
	    
	    if (PathLen == TspSize) {
		/* Visiting last node - determine if path is min length. */
		last := weights[i,StartNode];
		if (last != 0) {
		  CurDist := CurDist + last;
		  if(CurDist < MinTourLen) {
		    call set_best(CurDist, Path);
		  }
		}
		CurDist := CurDist - last;
	    } /* if visiting last node */
	    else {
	      if (CurDist < MinTourLen) {
		call visit_nodes(i);	/* Visit on. */
	      }
	    }
	    
	    /* Remove current try and loop again at this level. */
	    CurDist := CurDist - dist;
	    PathLen := PathLen - 1;
	    Visit[i] := 0;

	    i := i + 1;
	}
    }


record Node {
       distance: int;
       outEdges: Set Edge;
}

record Edge {
       weight: int;
       dst: Node;
}

const G: Set Node;
const StartNode: Node;
const INFINITY: int;

procedure main () {
	  var node: Node;
	  var outEdges: Set Edge;
	  var edge: Edge;
	  var worklist: PrioQueue Node;
	  var dist, new_dist: int;
	  var dst: Node;
	  var b: bool;

	  // set every distance to infinity
	  foreach(node in G) {
	    node.distance := INFINITY;
	  }
	  StartNode.distance := 0;

	  call prioqueue_enqueue(worklist, StartNode, 0);
	  foreach(node in worklist) {
	      outEdges := node.outEdges;
	      foreach(edge in outEdges) {
	          new_dist := node.distance + edge.weight;
		  dst := edge.dst;
		  b := (new_dist < dst.distance); 
		  if(b) {
		      dst.distance := new_dist;
		      call prioqueue_enqueue(worklist, dst, dst.distance);
		  }
	      }

	  }
}


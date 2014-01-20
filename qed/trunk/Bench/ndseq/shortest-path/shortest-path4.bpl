
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
	  var worklist: Set Node;
	  var node_dist, dst_dist, new_dist: int;
	  var dst: Node;
	  var b: bool;

	  // set every distance to infinity
	  foreach(node in G) {
	    node.distance := INFINITY;
	  }
	  StartNode.distance := 0;

	  call set_add(worklist, StartNode);
	  foreach {:parallel} (node in worklist) {
	    //atomic {
	      outEdges := node.outEdges;
	      foreach {:parallel} (edge in outEdges) {
	        atomic {
		  node_dist := node.distance; // node_dist := *;
		}
		atomic {
		  new_dist := node_dist + edge.weight; // computation
		}
		atomic {
		  dst := edge.dst; // read from immutable object
		}
		atomic {
		  dst_dist := dst.distance; //dst_dist := *; 
		}
		atomic {
		  b := (new_dist < dst_dist); // computation
		}
		atomic {
		  if(node.distance != node_dist || dst.distance != dst_dist) {
		      call set_add(worklist, node);
		      continue;
		  } 
		  if(b) {
		      assume new_dist < dst.distance;
		      dst.distance := new_dist;
		      call set_add(worklist, dst);
		  }
		}
	      }
	    //}
	  }
}


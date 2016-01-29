--2 Binary trees [20 points; 5 points/part]
--Consider the following model for binary trees:
module binarytree
one sig BinaryTree {
  root: lone Node
}
abstract sig Node {
  left, right: lone Node
}
pred Acyclic(t: BinaryTree) {
  all n: t.root.*(left + right) {
    n !in n.^(left + right)
    no n.(left) & n.(right)
    lone n.~(left + right)
  }
}
-- (a) Connectivity
-- TODO
--Implement the following fact as described in the comments:
fact DisconnectedNodesHaveSelfLoops {
  // the left and right fields of a node that is not in the
  // tree point to the node itself
  all n:Node | n !in (BinaryTree.root.*(left+right)) => n in (n.left + n.right)
}

-- (b) Isomorphism
-- TODO
/*
With the fact DisconnectedNodesHaveSelfLoops included in your model,
if you execute the command 'run Acyclic' and enumerate the instances,
do any two of these instances represent isomorphic binary trees[1] as solutions to the constraint Acyclic? 
If such instances appear as solutions, write two distinct instances
using Alloy Analyzer's textual format (i.e., Txt in the GUI) as comments in your model:
[1]Consider only the part of the instance reachable from the binary tree atom.
*/
// narrow down field of possibilities
fact {
  // force BinaryTree to have a root node
  one n: Node | n in BinaryTree.root
  // ensure that all nodes are in a BinaryTree
  --all n:Node | n in (BinaryTree.root.*(left+right))
  no n:Node | n !in (BinaryTree.root.*(left+right))
}
-- ensure fixed number of nodes; ?perhaps?: tree with 3 nodes cannot be isomorphic to tree with 2 nodes
run Acyclic for 1 BinaryTree, exactly 3 Node

/*
   Isomorphic instances for Question 2 (b):
   Instance #1:
   TODO

   Instance #2:
   TODO

*/



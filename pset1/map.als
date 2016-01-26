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
--Implement the following fact as described in the comments:
fact DisconnectedNodesHaveSelfLoops {
  // the left and right fields of a node that is not in the
  // tree point to the node itself
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
/*
   Isomorphic instances for Question 2 (b):
   Instance #1:
   ...
   Instance #2:
   ...
*/

/*
-- (c) Linear order
/*
Add the following declaration to your model to introduce four nodes, namely
N0, N1, N2, and N3, in the model:
  one sig N0, N1, N2, N3 extends Node {}
Implement the following fact LinearOrder to define a linear ordering on the 4 nodes as described in the comments:
*/
/*
one sig N0, N1, N2, N3 extends Node {}
one sig Ordering { // model a linear order on nodes
  first: Node, // the first node in the linear order
  order: Node -> Node // for each node n, n.(Ordering.order) represents the
           // node (if any) immediately after n in order
}
fact LinearOrder {
  // the first node in the linear order is N0; and
  // the four nodes are ordered as [N0, N1, N2, N3]
}
*/

-- (d) Non-isomorphic enumeration
/*
Use the linear order defined by the signature Ordering and the fact LinearOrder
for the four nodes to implement the following predicate NonIsomorphicTrees as
described in the comments:
*/
/*
pred SymmetryBreaking(t: BinaryTree) {
  // if t has a root node, it is the first node according to the linear order; and
  // a "pre-order" traversal of the nodes in t visits them according to the linear order

}
pred NonIsomorphicTrees(t: BinaryTree) {
  Acyclic[t]
    SymmetryBreaking[t]
}
run NonIsomorphicTrees // enumerates non-isomorphic binary trees with up to 4 nodes
*/
/*
Verify that your implementation is correct by executing the command run
NonIsomorphicTrees and checking that it enumerates exactly 23 binary trees -
which are all the (non-isomorphic) binary trees with up to 4 nodes.
*/

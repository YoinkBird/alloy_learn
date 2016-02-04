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
  // <requirements> 
  // the left and right fields of a node that is not in the
  // tree point to the node itself
  // </requirements> 
  all n:Node | n !in (BinaryTree.root.*(left+right)) => n in (n.left) and n in (n.right)
}
run Acyclic

-- (b) Isomorphism
/* <requirements> 
With the fact DisconnectedNodesHaveSelfLoops included in your model,
if you execute the command 'run Acyclic' and enumerate the instances,
do any two of these instances represent isomorphic binary trees[1] as solutions to the constraint Acyclic? 
If such instances appear as solutions, write two distinct instances
using Alloy Analyzer's textual format (i.e., Txt in the GUI) as comments in your model:
[1]Consider only the part of the instance reachable from the binary tree atom.
 </requirements> 
*/
// narrow down field of possibilities
fact {
  // force BinaryTree to have a root node
--  one n: Node | n in BinaryTree.root
  // ensure that all nodes are in a BinaryTree
  --all n:Node | n in (BinaryTree.root.*(left+right))
--  no n:Node | n !in (BinaryTree.root.*(left+right))
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


/*
-- (c) Linear order
/*
Add the following declaration to your model to introduce four nodes, namely
N0, N1, N2, and N3, in the model:
  one sig N0, N1, N2, N3 extends Node {}
Implement the following fact 'LinearOrder' to define a linear ordering
  on the 4 nodes as described in the comments:
*/
one sig N0, N1, N2, N3 extends Node {}
one sig Ordering { // model a linear order on nodes
  first: Node, // the first node in the linear order
  order: Node -> Node // for each node n, n.(Ordering.order) represents the
           // node (if any) immediately after n in order
}
/*notes
-- TREE structure
..n0
.|..\
n1  n3
|.\
n2
-- TREE linearorder:
n0->n1->n2->n3
*/
fact LinearOrder {
  // the first node in the linear order is N0; and
  // the four nodes are ordered as [N0, N1, N2, N3]

  // ta_note: that is all you need for your linear order.
  all o:Ordering{
    o.first = N0
    o.order = N0 -> N1 + N1 -> N2 + N2 -> N3
  }

}
run Acyclic

-- (d) Non-isomorphic enumeration
/*
Use the linear order defined by the signature Ordering and the fact LinearOrder
for the four nodes to implement the following predicate NonIsomorphicTrees as
described in the comments:
*/
/*custom*/
fact SymmetryBreakingFail {
  // test 
  // N0: force it to be right:
  // N1: force it to be false:
--  N0 in BinaryTree.root
}
/*</custom>*/

pred PreOrderRule_1(t: BinaryTree){
  // for all nodes in tree, the preorder is defined such that:
  // ensure that any node with only node.right and no node.left has a mapping node->node.right in Ordering.order
  // ensure that any node with node.left has a mapping node->node.left in Ordering.order
  all n:t.root.*(left+right) {
    #{n.left} = 0 and #{n.right} = 1 => n->n.right in n->n.(Ordering.order)
    #{n.left} = 1                    => n->n.left   in n->n.(Ordering.order)
  }
}
pred SymmetryBreaking(t: BinaryTree) {
  // stub - not sure if good
  PreOrderRule_1[t]

  // if t has a root node, it is the first node according to the linear order; and
  all n : t.root | n in Ordering.first
  // a "pre-order" traversal of the nodes in t visits them according to the linear order

  /*
  all n: t.root.*(left + right) {
    -- proof of concept
    #(n) = #(Ordering.order)
  }
  */
}
run SymmetryBreaking
pred NonIsomorphicTrees(t: BinaryTree) {
  Acyclic[t]
    SymmetryBreaking[t]
}
run NonIsomorphicTrees for 4 Node// enumerates non-isomorphic binary trees with up to 4 nodes
/*
Verify that your implementation is correct by executing the command run
NonIsomorphicTrees and checking that it enumerates exactly 23 binary trees -
which are all the (non-isomorphic) binary trees with up to 4 nodes.
*/

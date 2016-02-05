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
pred IsomorphismPrereq {
  // force BinaryTree to have a root node
  one n: Node | n in BinaryTree.root
  // ensure that all nodes are in a BinaryTree
  all n:Node | n in (BinaryTree.root.*(left+right))
--  no n:Node | n !in (BinaryTree.root.*(left+right))
  Acyclic[BinaryTree]
}
--run IsomorphismPrereq for 1 BinaryTree

/*
   Isomorphic instances for Question 2 (b):
   Instance #1:
---INSTANCE---
integers={}
univ={BinaryTree$0, N0$0, N1$0, N2$0, N3$0, Ordering$0}
Int={}
seq/Int={}
String={}
none={}
this/BinaryTree={BinaryTree$0}
this/BinaryTree<:root={BinaryTree$0->N3$0}
this/Node={N0$0, N1$0, N2$0, N3$0}
this/Node<:left={N3$0->N1$0}
this/Node<:right={N2$0->N0$0, N3$0->N2$0}
this/N0={N0$0}
this/N1={N1$0}
this/N2={N2$0}
this/N3={N3$0}
this/Ordering={Ordering$0}
this/Ordering<:first={Ordering$0->N0$0}
this/Ordering<:order={Ordering$0->N0$0->N1$0, Ordering$0->N1$0->N2$0, Ordering$0->N2$0->N3$0}

   Instance #2:
---INSTANCE---
integers={}
univ={BinaryTree$0, N0$0, N1$0, N2$0, N3$0, Ordering$0}
Int={}
seq/Int={}
String={}
none={}
this/BinaryTree={BinaryTree$0}
this/BinaryTree<:root={BinaryTree$0->N3$0}
this/Node={N0$0, N1$0, N2$0, N3$0}
this/Node<:left={N3$0->N2$0}
this/Node<:right={N1$0->N0$0, N3$0->N1$0}
this/N0={N0$0}
this/N1={N1$0}
this/N2={N2$0}
this/N3={N3$0}
this/Ordering={Ordering$0}
this/Ordering<:first={Ordering$0->N0$0}
this/Ordering<:order={Ordering$0->N0$0->N1$0, Ordering$0->N1$0->N2$0, Ordering$0->N2$0->N3$0}

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
assert SymmetryBreakingPass {
  // test 
  // N0: force it to be correct:
  N0 in BinaryTree.root
  NonIsomorphicTrees[BinaryTree]
}
assert SymmetryBreakingFail {
  // N1: force it to be false:
  N1 in BinaryTree.root
  NonIsomorphicTrees[BinaryTree]
}
check SymmetryBreakingPass
check SymmetryBreakingFail
/*</custom>*/

pred PreOrderRule_1(t: BinaryTree){
  // for all nodes in tree, the preorder is defined such that:
  // ensure that any node with only node.right and no node.left has a mapping node->node.right in Ordering.order
  // ensure that any node with node.left has a mapping node->node.left in Ordering.order
  all n:t.root.*(left+right) {
    #{n.left} = 0 and #{n.right} = 1 => n.right = n.(Ordering.order)
    #{n.left} = 1                    => n.left  = n.(Ordering.order)
    #{n.left} = 1 and #{n.right} = 1 => n.right in n.left.*(left+right).(Ordering.order)
  }
}
pred SymmetryBreaking(t: BinaryTree) {
  // if t has a root node, it is the first node according to the linear order; and
  all n : t.root | n in Ordering.first

  // a "pre-order" traversal of the nodes in t visits them according to the linear order
  PreOrderRule_1[t]

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

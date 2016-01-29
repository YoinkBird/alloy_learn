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
  all n:Node | n !in (BinaryTree.root.*(left+right)) => n in (n.left) and n in (n.right)
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
/*
ensure that there is a node in the binary tree for testing the pred Symmetry Breaking
*/
fact {
-- Note: if instance 'one sig' you can do this: 
--  DO NOT USE: -- N0 in BinaryTree.root
-- Note: if thingy not declared as 'one' you have to create one really quick
--  one n: Node | n in BinaryTree.root
}

fact SymmetryBreakingFail {
  // test 
  // N0: force it to be right:
  // N1: force it to be false:
--  N0 in BinaryTree.root
}
/*</custom>*/

pred HardCodedPreorderDoNotUse(t: BinaryTree){
  all n0:N0, n1:N1 | n1 in n0.(left+right)
  all n0:N0, n3:N3 | n3 in n0.(left+right)
  all n1:N1, n2:N2 | n2 in n1.(left+right)
}
pred GeneratePreorderMapping_1(t: BinaryTree){
  /* broken v
  forces a linear tree
  */
  -- too much! generates all possibilities of nodes
  --all n : Node | (n->n.(left) + n->n.(right)) = Ordering.order

  all n: t.root.*(left + right) | (n->n.(left) + n->n.(right)) = Ordering.order
--  all n : Node | n->n.(right) in Ordering.order
}
pred NodeHasLeft(t: BinaryTree){
  some n:Node | n->n.(left) = n->n.(Ordering.order)
}
pred NodeHasRight(t: BinaryTree){
  all n:Node | n->n.(right) = n->n.(Ordering.order)
}
pred PreOrderRule_1(t: BinaryTree){
  // whenever there are two child-nodes
  /*
  some nL:Node.(left), nR:Node.(right){
    // n1 always left (preorder)
    some n1:N1, nR:N0.(right) | n1 in N0.(left) and n1 !in nR
    --  some n1:N1, nR:N0.(right) | n1 !in nR
    --  some n2:N2 | n2 in N1.(left)
  }
  */
  --all n:Node | n.(left) | n->n.(left) in Ordering.order
--  some n:Node,nNext:Node | nNext in n.(left) | n->nNext in Ordering.order
--  NodeHasLeft implies NodeHasLeft else NodeHasRight
--  NodeHasLeft[t] implies NodeHasLeft[t] else NodeHasRight[t]

-- syntax ok
--  all n:t.root.*(left+right) | #{n.left} = 0 => n->n.right in n->n.(Ordering.order)
  // for all nodes in tree, the preorder is defined such that:
  // ensure that any node with only node.right and no node.left has a mapping node->node.right in Ordering.order
  // ensure that any node with node.left has a mapping node->node.left in Ordering.order
  all n:t.root.*(left+right) {
    #{n.left} = 0 and #{n.right} = 1 => n->n.right in n->n.(Ordering.order)
    #{n.left} = 1                    => n->n.left   in n->n.(Ordering.order)
  }
}
pred NodesAlwaysParents(t: BinaryTree) {
  // NOTE: seemingly good rule!
  // But hard-coding is almost never a good idea
  // define nodes which are always parents
  all n1:N1 {
    n1 !in N2.(left+right)
    n1 !in N3.(left+right)
  }
  all n2:N2 {
    n2 !in N3.(left+right)
  }
}
pred SymmetryBreaking(t: BinaryTree) {
  // BAD: initial idea
  --HardCodedPreorderDoNotUse[t]
  // BAD: only generates linear tree
--  GeneratePreorderMapping_1[t]
  // seems to work
  // commenting out to try other things
  --NodesAlwaysParents[t]
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

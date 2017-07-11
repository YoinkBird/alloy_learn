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
--   all n: BinaryTree.root.*left | n in n.left and n in n.right

--    all n:(BinaryTree.root.*(left + right)) | n in n.left
--   all n:Node - (BinaryTree.root.*(left + right))

   -- TODO: syntax error!
   all n:Node | n !in (BinaryTree.root.*(left+right)) => n in (n.left + n.right)

}

-- TODO
run Acyclic for 1 BinaryTree, exactly 4 Node

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
fact {
  one n: Node | n in BinaryTree.root

}
/*
   Isomorphic instances for Question 2 (b):
   Instance #1:

---INSTANCE---
integers={}
univ={BinaryTree$0, Node$0, Node$1, Node$2, Node$3}
Int={}
seq/Int={}
String={}
none={}
this/BinaryTree={BinaryTree$0}
this/BinaryTree<:root={BinaryTree$0->Node$3}
this/Node={Node$0, Node$1, Node$2, Node$3}
this/Node<:left={Node$3->Node$2}
this/Node<:right={Node$1->Node$0, Node$2->Node$1}
skolem $Acyclic_t={BinaryTree$0}


   Instance #2:
---INSTANCE---
integers={}
univ={BinaryTree$0, Node$0, Node$1, Node$2, Node$3}
Int={}
seq/Int={}
String={}
none={}
this/BinaryTree={BinaryTree$0}
this/BinaryTree<:root={BinaryTree$0->Node$3}
this/Node={Node$0, Node$1, Node$2, Node$3}
this/Node<:left={Node$0->Node$2, Node$1->Node$1, Node$2->Node$3}
this/Node<:right={Node$0->Node$0, Node$1->Node$0, Node$2->Node$2}
skolem $Acyclic_t={BinaryTree$0}

*/


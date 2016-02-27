module redBlackTree
--import integer
sig Color {}
sig Red, Black extends Color {}
sig Entry {
--  key: option Integer,
  key: Int,
  color: Color,
  left: Entry,
  right: Entry,
  parent: Entry
}
sig Root extends Entry {}
sig NIL extends Entry {} // models leaf nodes

fact ParentDefn {
  all e1, e2: Entry |
    e1 in e2.parent <=> e2 in e1.left + e1.right
}
fun HasNILChild[e: Entry]: Entry { NIL in e.left + e.right }

fact RedBlackFacts {
  // every node is red or black -- holds by construction
  // leafs are black
  NIL.color = Black
  // red has black children
  all e: Entry | e.color = Red =>
    (e.left + e.right).color = Black
  // paths from root to NIL have same # of black nodes
  all e1, e2: Entry |
    HasNILChild(e1) && HasNILChild(e2) =>
      #(e1.*parent & Black. ~color) =
        #(e2.*parent & Black. ~color)
}

fact BinaryTreeFacts {
  // root has no parent
  no Root.parent
  // acyclic
  all e: Entry | e !in e.^( ~parent)
  // unique children
  all e: Entry - NIL |
    e.left != e.right ||
    e.left + e.right = NIL
  // internal nodes
  all e: Entry - NIL |
    some e.left && some e.right && some e.key
  // leaf nodes
  no NIL.left && no NIL.right && no NIL.key
}

fact SearchTreeFacts {
  // left subtree has smaller keys
  all e: Entry - NIL |
    all el: e.left.*( ~parent) - NIL | el.key <= e.key
  // right subtree has larger keys
  all e: Entry - NIL |
    all er: e.right.*( ~parent) - NIL | e.key <= er.key
}

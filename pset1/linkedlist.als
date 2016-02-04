-- reference: http://www.ics.uci.edu/~alspaugh/cls/shr/alloy.html#predicate
/*
Call a singly-linked list a loop-list if it is empty or if it is non-empty and its last
node has a pointer back to itself. Consider modeling the following Java program
that implements loop-lists with sorted elements:
*/
module list
sig List {
  header: set Node
}
sig Node {
  link: set Node,
  elem: set Int
}
fact {
-- TODO: constrain all nodes to exist within a list
--  Node in List.*header
  -- src http://stackoverflow.com/a/28281643
  all n: Node | one l: List | n = l.header or n in l.header.^link 
}

pred show(){
}


--run show for 1 List, 3 Node, 2 Int

-- a: cardinality constraints
/* notes:
'lone' : zero or one
*/
fact CardinalityConstraints {
  // each list has at most one header node
  // TODO:
  all l:List | lone l.header
--    all l:List | one l.header
--    some l.header.*link | no n.link
  // each node has at most one link
  all n:Node | lone n.link
  // each node has exactly one elem
  all n:Node | one n.elem
}

-- b: Class invariant
/*Implement the following predicates Loop and Sorted
  and the run command as described in the comments:
*/


/*
loop-list: singly-linked list which is empty
or non-empty and its last node has a pointer back to itself
*/
pred Loop(This: List) {
  // <This> is a valid loop-list
  -- empty or one link points to itself
  no This.header or
    one n:This.header.*link | n in n.link
}
pred Sorted(This: List) {
  // <This> has elements in sorted order (‘<=’)
  all n:Node | n.elem <= n.link.elem
}

pred RepOk(This: List) { // class invariant for List
  Loop[This]
  Sorted[This]
}
// scope: #List <= 1, #Node <= 3, ints = { -2, -1, 0, 1 }
run RepOk for 1 List, 3 Node, 2 Int

-- c: Specifying the count method
-- Implement the following predicate Count and the run command as described below:
pred Count(This: List, x: Int, result: Int) {
  // count correctly returns the number of occurences of <x> in <This>
  // <result> reprsents the return value of count
--  let ints = #{Node.elem}-- | x in This.header.*elem and 
  #{n:This.header.*link | x in n.elem} = result
  RepOk[This] // assume This is a valid list
}

// scope: #List <= 1, #Node <= 3, ints = { -2, -1, 0, 1 }
run Count for 1 List, 3 Node, 2 Int


-- d: Specifying the contains method
-- Implement the following predicate Contains and the run command as described below:
abstract sig Boolean {}
one sig True, False extends Boolean {}
pred Contains(This: List, x: Int, result: Boolean) {
  // contains returns true if and only if <x> is in <This>
  // <result> represents the return value of contains
  x in This.header.*link.elem => result = True else result = False
  /*** v template ***/
  RepOk[This] // assume This is a valid list
}
// scope: #List <= 1, #Node <= 3, ints = { -2, -1, 0, 1 }
run Contains for 1 List, 3 Node, 2 Int

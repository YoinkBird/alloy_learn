-- https://www.doc.ic.ac.uk/project/examples/2007/271j/suprema_on_alloy/Web/tutorial1_1.php
module examples/tutorial/queue
sig Queue{
  root: lone Node
}

sig Node{
  next: lone Node
}

fact nextNotReflexive{
  no n:Node | n = n.next
}

--fact allNodesBelongToSomeQueue{
fact allNodesBelongToOneQueue{
  // for_all Node n there_exists n in q.root.*next
--  all n:Node | some q:Queue | n in q.root.*next
  all n:Node | one q:Queue | n in q.root.*next
}

fact nextNotCyclic{
  no n:Node | n in n.^next
}

pred show(){
}


run show for 3

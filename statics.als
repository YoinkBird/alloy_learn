-- https://www.doc.ic.ac.uk/project/examples/2007/271j/suprema_on_alloy/Web/tutorial1_1.php
module examples/tutorial/queue
sig queue{
  root: lone Node
}

sig Node{
  next: lone Node
}

fact nextNotReflexive{
  no n:Node | n = n.next
}

pred show(){
}


run show for 2

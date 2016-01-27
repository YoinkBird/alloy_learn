-- https://www.doc.ic.ac.uk/project/examples/2007/271j/suprema_on_alloy/Web/tutorial2_1.php

module examples/tutorial/Map

abstract sig Object{}
sig Key, Value extends Object{}
sig Map {values: Key -> lone Value}

assert mappingIsUnique{
  all m:Map, k:Key, v, v':Value |
    k -> v in m.values and k -> v' in m.values implies v = v'
}
-- check
check mappingIsUnique for 2

-- part 2 
--  convention is to use ' to decorate the state after the operation
pred put(m, m':Map, k:Key, v:Value){
  /* m' : the set of values after is equal to
     m  : the union of the set of values before with the extra mapping from k to v
  */
  m'.values = m.values + k -> v
}
run put for 3 but exactly 2 Map, exactly 1 Key, exactly 1 Value

assert putLocal {
  all m, m': Map, k, k': Key, v: Value |
    put[m,m',k,v] and k != k' implies
    lookup[m,k'] = lookup[m',k']
}
fun lookup(m: Map, k: Key): set Value { k.(m.values) }
check putLocal

fact {
  all k:Key   | some v:Value, m:Map | k -> v in m.values
  all v:Value | some k:Key, m:Map   | k -> v in m.values
}

-- run
pred show(){ #Map > 0}
run show for 3 but exactly 1 Map


-- https://www.doc.ic.ac.uk/project/examples/2007/271j/suprema_on_alloy/Web/tutorial2_1.php

module examples/tutorial/Map

abstract sig Object{}
sig Key, Value extends Object{}
sig Map {values: Key -> lone Value}

assert mappingIsUnique{
  all m:Map, k:Key, v, v':Value |
    k -> v in m.values and k -> v' in m.values implies v = v'
}

fact {
  all k:Key   | some v:Value, m:Map | k -> v in m.values
  all v:Value | some k:Key, m:Map   | k -> v in m.values
}

-- run
pred show(){ #Map > 0}
run show for 3 but exactly 1 Map
-- check
check mappingIsUnique for 2

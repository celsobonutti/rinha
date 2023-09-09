import Lake
open Lake DSL

package rinha {
  -- add package configuration options here
}

lean_lib Rinha {
  -- add library configuration options here
}

lean_lib Map {

}


lean_lib JSON {

}

lean_exe rinha {
  root := `Main
}

require soda from git "https://github.com/algebraic-sofia/soda.git"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

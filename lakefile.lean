import Lake
open Lake DSL

package «bellman-Ford» {
  -- add package configuration options here
}

lean_lib «BellmanFord» {
  -- add library configuration options here
}

lean_lib «Graph_lib» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

require Graph from git
  "https://github.com/OmkarBaraskar/graph-library-for-lean4.git"

@[default_target]
lean_exe «bellman-Ford» {
  root := `Main
}

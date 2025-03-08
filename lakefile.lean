import Lake
open Lake DSL

package "topology_in_lean" where
  version := v!"0.1.0"

lean_lib «TopologyInLean» where
  -- add library configuration options here

@[default_target]
lean_exe "topology_in_lean" where
  root := `Main

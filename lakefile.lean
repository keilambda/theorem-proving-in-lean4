import Lake
open Lake DSL

package «theorem-proving-in-lean4» where
  -- add package configuration options here

lean_lib «TheoremProvingInLean4» where
  -- add library configuration options here

@[default_target]
lean_exe «theorem-proving-in-lean4» where
  root := `Main

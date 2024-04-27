import Lake
open Lake DSL

package «exe» where
  -- add package configuration options here

require std from git
  "https://github.com/leanprover/std4" @ "v4.3.0"

@[default_target]
lean_exe «exe» where
  root := `Main

import Lake
open Lake Lake.DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "e72804323d45b6a44a59371c74c05cd6826902a7"

-- lake -Kdoc=on build Coc:docs
meta if get_config? doc = some "on" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "e888e9cc383f838ef8f519e6941e32fe5c48df1b"

package «coc» {
  -- add package configuration options here
}

lean_lib «Coc» {
  -- add library configuration options here
}

@[default_target]
lean_exe «coc» {
  root := `Main
}

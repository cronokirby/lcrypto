import Lake
open Lake DSL

package "lcrypto" where
  -- add package configuration options here

lean_lib «Lcrypto» where
  -- add library configuration options here

@[default_target]
lean_exe "lcrypto" where
  root := `Main

import Lake

open Lake DSL

package «cordis-lean» where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Cordis

@[default_target]
lean_exe cordis_demo where
  root := `Main

@[default_target]
lean_exe cordis_tests where
  root := `Tests

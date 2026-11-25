import Lake
open Lake DSL

package «TorusACC0» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «TorusACC0» where
  roots := #[`TorusACC0]
  moreLeanArgs := #["-j", "1"]

import Lake
open Lake DSL
package ClosedCoverCutting where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "520045ab14e26149ee970e2e617ca04b09bde5d6"
require HatcherLib from git
  "https://github.com/frenzymath/Poincare-Conjecture.git" @ "bb91a091f0b968f8bbe8d861e025a88d82b161be" / "formalized-sources/Hatcher"
@[default_target]
lean_lib ClosedCover where
  roots := #[`ClosedCover]
lean_lib CapFilling
lean_lib PuncturedCap
lean_lib AttachmentOpen
lean_lib ConnectedCap
lean_lib HomotopicFactorization
lean_lib CappingTheorem

@[default_target]
lean_lib CutSides

@[default_target]
lean_lib ClosedCoverTests

@[default_target]
lean_lib ClosedCoverAudit

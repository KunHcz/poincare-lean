import Lake
open Lake DSL
package CapFilling where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "520045ab14e26149ee970e2e617ca04b09bde5d6"
require HatcherLib from git
  "https://github.com/frenzymath/Poincare-Conjecture.git" @ "bb91a091f0b968f8bbe8d861e025a88d82b161be" / "formalized-sources/Hatcher"
@[default_target]
lean_lib CapFilling
@[default_target]
lean_lib PuncturedCap
@[default_target]
lean_lib AttachmentOpen
@[default_target]
lean_lib HomotopicFactorization
@[default_target]
lean_lib ConnectedCap
@[default_target]
lean_lib CappingTheorem
@[default_target]
lean_lib CapFillingTests
@[default_target]
lean_lib CapFillingAudit

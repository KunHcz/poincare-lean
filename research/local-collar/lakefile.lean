import Lake
open Lake DSL
package CompactLocalCollar where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "520045ab14e26149ee970e2e617ca04b09bde5d6"
require HatcherLib from git
  "https://github.com/frenzymath/Poincare-Conjecture.git" @ "bb91a091f0b968f8bbe8d861e025a88d82b161be" / "formalized-sources/Hatcher"
lean_lib PuncturedCap
lean_lib CappingTheorem
lean_lib SeparatedCapping
lean_lib ConnectedCap
lean_lib CutSides
lean_lib ClosedCover
lean_lib CapFilling
lean_lib HomotopicFactorization
lean_lib AttachmentOpen
lean_lib CollarPhase
lean_lib CollarSeparator
lean_lib SeparationComponents
@[default_target]
lean_lib CompactCollar
@[default_target]
lean_lib UniformCollar
@[default_target]
lean_lib DifferentialCollar

lean_lib SeparationTests
@[default_target]
lean_lib LocalCollarTests
@[default_target]
lean_lib LocalCollarAudit

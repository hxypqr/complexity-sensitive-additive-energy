import ComplexitySensitiveEnergy.External.AlgebraicGeometry
import ComplexitySensitiveEnergy.External.Analysis
import ComplexitySensitiveEnergy.External.Literature

/-!
# External literature and standard-theorem registry

This proposition-valued bundle records the cited algebraic, analytic, and
additive-combinatorial theorems without declaring global axioms.  It does not
by itself manufacture the finite recurrence/dyadic certificates used by the
paper-facing verifiers; those bridge constructions remain separately visible
in their theorem hypotheses.
-/

namespace ComplexitySensitiveEnergy.External

structure Inputs : Prop where
  algebraicGeometry : AlgebraicGeometryInputs
  standardAnalysis : AnalysisInputs
  literature : LiteratureInputs

end ComplexitySensitiveEnergy.External

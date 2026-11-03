/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionShiftCount
public import OnLeConjecture.Analytic.ResolutionSectionFloerReduction
public import OnLeConjecture.KnotTheory.PositiveWordNormalForms

/-!
# The combinatorial choices of the native route on one assembly and one level

This module defines the combinatorial data of the native route (stage 1 of job J17). For an
assembled analytic section `A` and one nearby level `L`, a `NativeRouteChoice A L` consists of

* a positive word on `S = A.squareSum` strands for the image curve `W`, whose permutation has
  as many cycles as `W` has branches and whose length satisfies
  `|w| + S(S - 1) + b = 2δ(W) + S`;
* for each singular point of the level, a number of strands `a_j` with `2 ≤ a_j ≤ t_J` and a
  positive word on `a_j` strands with one permutation cycle, using every generator, of length
  `|w_j| + 1 = 2δ_j + a_j`, where `δ_j` is the delta invariant of the local section equation.

The braid shift of the image word and the exterior shift `μ(v)/2` add up to the candidate
genus (`NativeRouteChoice.braid_exterior_count`, from job J16).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open OnLeConjecture.PlaneCurve OnLeConjecture.KnotTheory

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- The combinatorial choices of the native route on one assembly `A` and one level `L`. -/
structure NativeRouteChoice (A : ResolutionSectionAssembly g hd hi)
    (L : ResolutionSectionLevel A) where
  /-- The positive word `w` of the image curve, after the full-twist prefix. -/
  imageWord : PositiveAdjacentWord A.squareSum
  imageWord_cycleCount : imageWord.toSigned.cycleCount = irreducibleBranchCount A.imageEquation
  imageWord_length : imageWord.length + A.squareSum * (A.squareSum - 1) +
      irreducibleBranchCount A.imageEquation = 2 * deltaInvariant A.imageEquation + A.squareSum
  /-- The number of strands `a_j` of the braid of the singular point `j`. -/
  strands : Fin L.points.card → ℕ
  /-- The positive word of the singular point `j`. -/
  factorWord : ∀ j, PositiveAdjacentWord (strands j)
  two_le_strands : ∀ j, 2 ≤ strands j
  strands_le : ∀ j, strands j ≤ (g.criticalJacobianFactorization hi).maxMultiplicity
  factorWord_cycleCount : ∀ j, (factorWord j).toSigned.cycleCount = 1
  factorWord_generators : ∀ j, (factorWord j).toSigned.generatorIndices = Finset.univ
  factorWord_length : ∀ j, (factorWord j).length + 1 =
    2 * deltaInvariant (localSectionEquation A.H (L.point j)) + strands j

namespace NativeRouteChoice

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}

/-- The braid shift of the image word and the exterior shift `μ(v)/2` add up to the
candidate genus. -/
theorem braid_exterior_count (C : NativeRouteChoice A L) :
    ((C.imageWord.length : ℝ) - ((A.squareSum : ℝ) - C.imageWord.toSigned.cycleCount) +
        ((C.imageWord.toSigned.cycleCount : ℝ) - 1)) / 2 + (A.sourceMilnorNumber : ℝ) / 2 =
      (A.candidateGenus : ℝ) :=
  A.braid_exterior_count C.imageWord C.imageWord_cycleCount C.imageWord_length

/-- The selected grid of every factor word has size at least two. -/
theorem two_le_factorWordGrid_size (C : NativeRouteChoice A L) (j : Fin L.points.card) :
    2 ≤ (C.factorWord j).length * 3 := by
  have h1 := C.factorWord_length j
  have h2 := C.two_le_strands j
  omega

end NativeRouteChoice

end OnLeConjecture.Analytic

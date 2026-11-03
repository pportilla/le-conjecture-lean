/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AnalyticCobordismInput
public import OnLeConjecture.Analytic.SectionDeltaSpecialization
public import OnLeConjecture.KnotTheory.PositivePermutationWords

/-!
# Shift bookkeeping for the braid and exterior pieces

This module proves the count form of the shift identity used by the final
assembly (job J16 of the dependency audit). Let `A` be an assembled analytic
section, let `S = A.squareSum`, let `v = A.sourceEquation` and `W = A.imageEquation`,
and let `b` be the number of branches of `W`.

* The reduced image equation and the reduced source equation have the same number
  of branches, because both counts equal the number of branches of the section
  image factorization.
* For a positive word `w` on `S` strands whose permutation has `b` cycles and whose
  length satisfies `|w| + S(S - 1) + b = 2δ(W) + S`, the braid shift
  `(|w| - (S - b) + (b - 1)) / 2` and the exterior shift `μ(v) / 2` add up to the
  candidate genus `δ(v) + δ(W) - S(S - 1)/2`.

The second identity uses Milnor's formula for `v` in the form supplied by
`exists_sourceGenus`, and the inequality `torusGenus_le`, which excludes truncation
in the natural-number subtraction defining `candidateGenus`.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open OnLeConjecture.PlaneCurve OnLeConjecture.KnotTheory

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

namespace ResolutionSectionAssembly

/-- The reduced image equation and the reduced source equation have the same number
of irreducible branches. -/
theorem irreducibleBranchCount_imageEquation (A : ResolutionSectionAssembly g hd hi) :
    irreducibleBranchCount A.imageEquation = irreducibleBranchCount A.sourceEquation := by
  rw [A.imageEquation_eq,
    SectionImageFactorization.irreducibleBranchCount_imageEquation A.factorization A.H_injective,
    ← SectionImageFactorization.irreducibleBranchCount_component_zero A.factorization,
    A.sourceEquation_component]

/-- Twice the torus genus `S.choose 2` is `S * (S - 1)`. -/
theorem two_mul_torusGenus (A : ResolutionSectionAssembly g hd hi) :
    2 * A.torusGenus = A.squareSum * (A.squareSum - 1) := by
  unfold torusGenus
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd]

/-- **Shift count.** For a positive word `w` on `S = A.squareSum` strands whose
permutation has as many cycles as `W` has branches, and whose length satisfies
`|w| + S(S - 1) + b = 2δ(W) + S` with `b` the branch count of `W`, the braid shift and
the exterior shift `μ(v)/2` add up to the candidate genus. -/
theorem braid_exterior_count (A : ResolutionSectionAssembly g hd hi)
    (w : PositiveAdjacentWord A.squareSum)
    (hc : w.toSigned.cycleCount = irreducibleBranchCount A.imageEquation)
    (hl : w.length + A.squareSum * (A.squareSum - 1) + irreducibleBranchCount A.imageEquation =
      2 * deltaInvariant A.imageEquation + A.squareSum) :
    ((w.length : ℝ) - ((A.squareSum : ℝ) - w.toSigned.cycleCount) +
        ((w.toSigned.cycleCount : ℝ) - 1)) / 2 + (A.sourceMilnorNumber : ℝ) / 2 =
      (A.candidateGenus : ℝ) := by
  obtain ⟨γ, hγ₁, hγ₂⟩ := A.exists_sourceGenus
  rw [← A.irreducibleBranchCount_imageEquation] at hγ₁ hγ₂
  have htorus := A.two_mul_torusGenus
  have hle := A.torusGenus_le
  -- The natural-number identity `2 * (braid shift + exterior shift) = 2 * candidateGenus`.
  have hnat : w.length + 2 * w.toSigned.cycleCount + A.sourceMilnorNumber =
      2 * A.candidateGenus + A.squareSum + 1 := by
    unfold candidateGenus
    omega
  have hreal : ((w.length : ℕ) : ℝ) + 2 * (w.toSigned.cycleCount : ℝ) +
      (A.sourceMilnorNumber : ℝ) = 2 * (A.candidateGenus : ℝ) + (A.squareSum : ℝ) + 1 := by
    exact_mod_cast hnat
  linarith

end ResolutionSectionAssembly

end OnLeConjecture.Analytic

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicWeightedLimitArc
public import OnLeConjecture.DTwo.CyclicPreparedHypersurfaceFactorization

/-!
# Weighted limiting arcs constructed from the cyclic coefficient

The exact first noninvariant coefficient gives analytic representatives
of the unit defect and the remaining correction. Their lifted quadratic
branches solve the original first-plane equation after weighted scaling.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem exists_cyclicCoefficientGerm_representation (u : Germ 1) :
    ∃ ε : ℂ → ℂ, ∃ hε : AnalyticAt ℂ ε 0, cyclicCoefficientGerm ε hε = u := by
  obtain ⟨U, hU, rfl⟩ := exists_ofFunction u
  let e : Source 1 ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)
  let ε := U ∘ e.symm
  have hε : AnalyticAt ℂ ε 0 := by
    have hU' : AnalyticAt ℂ U (e.symm 0) := by simpa only [map_zero] using hU
    exact hU'.comp (e.symm.analyticAt 0)
  refine ⟨ε, hε, ?_⟩
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro q
  change U (e.symm (e q)) = U q
  rw [e.symm_apply_apply]

/-- The analytic unit and correction in the weighted plane equation are
constructed from the actual implicit branch and coefficient jet. -/
theorem cyclicPlane_weighted_defect_decomposition
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (ζ : ℂ) (hζ : ζ ^ k = 1) (hζ0 : ζ ≠ 0)
    (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0) (hz0 : z 0 = ζ)
    (hsol : ∀ᶠ q in 𝓝 (0 : ℂ × ℂ),
      q.1 + β (q.2 ^ p) - z q ^ k * β (q.2 ^ p * z q) = 0)
    (hne : cyclicCoefficientGerm β hβ -
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ0)).forward.pullbackRingHom
        (cyclicCoefficientGerm β hβ) ≠ 0) :
    ∃ j : ℕ, 0 < j ∧ ζ ^ j ≠ 1 ∧
      ∃ ε : ℂ → ℂ, ∃ hε : AnalyticAt ℂ ε 0, ε 0 ≠ 0 ∧
        ∃ K : Source 3 → ℂ, ∃ hK : AnalyticAt ℂ K 0,
          cyclicFirstPlaneGerm k p z hz =
            coordinate (0 : Fin 3) ^ 2 - coordinate (1 : Fin 3) ^ 2 +
              coordinate 2 ^ (k * (p - 2)) * (coordinate 2 ^ (p * j) *
                cyclicLastExtension (cyclicCoefficientGerm ε hε) +
                  (coordinate 0 ^ p - coordinate 1 ^ p) * ofFunction K hK) ∧
          ∃ P : MvPolynomial (Fin 1) ℂ,
            cyclicCoefficientGerm β hβ - coordinatePolynomialAlgHom 1 P ∈
              maximalIdeal 1 ^ (j + 1) ∧
            MvPolynomial.coeff (Finsupp.single 0 j) P ≠ 0 ∧
            ε 0 = -(MvPolynomial.coeff (Finsupp.single 0 j) P / β 0) * (1 - ζ ^ j) ∧
            ∀ i < j, P.coeff (Finsupp.single 0 i) = 0 ∨ ζ ^ i = 1 := by
  have hp0 : 0 < p := by omega
  obtain ⟨j, hj, hchar, u, hδ, P, hP, hPc, hvalue, hprevious⟩ :=
    cyclicPlane_parameter_defect_order k p hk hp0 β hβ hc ζ hζ hζ0 z hz hz0 hsol hne
  obtain ⟨ε, hε, hεu⟩ := exists_cyclicCoefficientGerm_representation (↑u : Germ 1)
  have hεvalue : ε 0 = valueRingHom 1 (↑u : Germ 1) := by
    rw [← hεu]
    rfl
  have hε0 : ε 0 ≠ 0 := hεvalue ▸ valueRingHom_ne_zero_of_isUnit u.isUnit
  obtain ⟨K, _, _, _, hD, _, _, _, _, _⟩ :=
    exists_cyclicPlane_hypersurface_coordinates p (k * (p - 2)) hp (cyclicBranchDefectGerm k z hz)
  obtain ⟨Krep, hKrep, hK⟩ := exists_ofFunction K
  refine ⟨j, hj, hchar, ε, hε, hε0, Krep, hKrep, ?_, P, hP, hPc,
    hεvalue.trans hvalue, hprevious⟩
  rw [cyclicFirstPlaneGerm, ← cyclicBranchDefectGerm_powerDifference_pullback k p z hz,
    hD, hδ, hεu, ← hK]

/-- Every nonsingular point of the limiting quadratic component has an
actual analytic arc on the first-plane hypersurface. -/
theorem exists_cyclicPlane_weighted_arc_of_defect_decomposition
    (k p j : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hj : 0 < j)
    (ε : ℂ → ℂ) (hε : AnalyticAt ℂ ε 0) (hε0 : ε 0 ≠ 0)
    (K : Source 3 → ℂ) (hK : AnalyticAt ℂ K 0) (H : Germ 3)
    (hH : H = coordinate (0 : Fin 3) ^ 2 - coordinate (1 : Fin 3) ^ 2 +
      coordinate 2 ^ (k * (p - 2)) * (coordinate 2 ^ (p * j) *
        cyclicLastExtension (cyclicCoefficientGerm ε hε) +
          (coordinate 0 ^ p - coordinate 1 ^ p) * ofFunction K hK))
    (s S : ℂ) (hS : S ≠ 0) (hpoint : S ^ 2 = s ^ 2 + ε 0) :
    ∃ hr : 0 < k * (p - 2) + p * j,
      ∃ B : ℂ → ℂ, ∃ hB : AnalyticAt ℂ B 0,
        B 0 = S ∧ s ≠ B 0 ∧
          (cyclicWeightedArc (k * (p - 2) + p * j) hr s B hB).pullbackRingHom H = 0 := by
  have hν : 0 < k * (p - 2) := Nat.mul_pos hk (by omega)
  have hr : 0 < k * (p - 2) + p * j := by positivity
  obtain ⟨B, hB, hB0, hsol⟩ := exists_cyclicWeightedLimit_analytic_branch
    p (k * (p - 2)) (k * (p - 2) + p * j) hν hr ε hε K hK s S hS hpoint
  have hne : s ≠ B 0 := by
    rw [hB0]
    intro h
    rw [← h] at hpoint
    exact hε0 (by linear_combination -hpoint)
  refine ⟨hr, B, hB, hB0, hne, ?_⟩
  exact cyclicWeightedArc_pullback_equation p (k * (p - 2)) j
    (k * (p - 2) + p * j) (by omega) hr rfl ε hε K hK s B hB hsol H hH

end OnLeConjecture.DTwo

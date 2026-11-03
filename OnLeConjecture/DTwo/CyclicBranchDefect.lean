/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicCenteredEquation

/-!
# The defect of the analytic cyclic branch

For an actual analytic solution `b(lambda)` through `zeta`, the germ
`1-b^k` is a unit multiple of `beta(lambda^p)-beta(zeta*lambda^p)`.
The unit has value `-1/beta(0)`. This replaces an induction on coefficients
by an analytic factorization and also covers an identically zero defect.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

@[expose] noncomputable def cyclicCenteredBranchMap
    (b : Source 1 → ℂ) (hb : AnalyticAt ℂ b 0) (ζ : ℂ) (hb0 : b 0 = ζ) :
    PointedMapGerm 1 2 :=
  PointedMapGerm.ofFunction (fun q : Source 1 => ![b q - ζ, q 0])
    (by
      apply AnalyticAt.pi
      intro i
      fin_cases i
      · exact hb.sub analyticAt_const
      · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0)
    (by ext i; fin_cases i <;> simp [hb0])

theorem cyclicCenteredBranchMap_pullback_first
    (b : Source 1 → ℂ) (hb : AnalyticAt ℂ b 0) (ζ : ℂ) (hb0 : b 0 = ζ) :
    (cyclicCenteredBranchMap b hb ζ hb0).pullbackRingHom (coordinate (0 : Fin 2)) =
      ofFunction b hb - constRingHom 1 ζ := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  simp only [cyclicCenteredBranchMap, PointedMapGerm.ofFunction,
    MapGerm.component_ofFunction]
  rfl

theorem cyclicCenteredBranchMap_solves
    (k p : ℕ) (hp : 0 < p) (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0)
    (b : Source 1 → ℂ) (hb : AnalyticAt ℂ b 0) (ζ : ℂ) (hb0 : b 0 = ζ)
    (hsolution : ∀ᶠ q in 𝓝 (0 : Source 1),
      β (q 0 ^ p) - b q ^ k * β (q 0 ^ p * b q) = 0) :
    (cyclicCenteredBranchMap b hb ζ hb0).pullbackRingHom
      (cyclicCenteredEquationGerm k p hp β hβ ζ) = 0 := by
  apply Subtype.ext
  change ((fun q : Source 1 =>
    cyclicCenteredEquation k p β ζ (![b q - ζ, q 0])) : FunctionGerm 1) = 0
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hsolution] with q hq
  simpa [cyclicCenteredEquation] using hq

@[expose] noncomputable def cyclicRotationDefectFunction
    (p : ℕ) (β : ℂ → ℂ) (ζ : ℂ) (q : Source 1) : ℂ :=
  β (q 0 ^ p) - β (q 0 ^ p * ζ)

theorem cyclicRotationDefectFunction_analyticAt
    (p : ℕ) (hp : 0 < p) (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (ζ : ℂ) :
    AnalyticAt ℂ (cyclicRotationDefectFunction p β ζ) 0 := by
  have hq : AnalyticAt ℂ (fun q : Source 1 => q 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0
  have h1 : AnalyticAt ℂ (fun q : Source 1 => β (q 0 ^ p)) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 1)) _ (hq.pow p)
    simpa only [Pi.pow_apply, Pi.zero_apply, zero_pow hp.ne'] using hβ
  have h2 : AnalyticAt ℂ (fun q : Source 1 => β (q 0 ^ p * ζ)) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 1)) _ ((hq.pow p).mul analyticAt_const)
    simpa only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply, zero_pow hp.ne', zero_mul] using hβ
  exact h1.sub h2

/-- The explicit axis defect after pullback by the pointed branch. -/
theorem cyclicCenteredBranchMap_pullback_axis_defect
    (k p : ℕ) (hp : 0 < p) (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0)
    (b : Source 1 → ℂ) (hb : AnalyticAt ℂ b 0) (ζ : ℂ) (hb0 : b 0 = ζ)
    (hζ : ζ ^ k = 1) :
    (cyclicCenteredBranchMap b hb ζ hb0).pullbackRingHom
      (hyperplaneExtension 1 (hyperplaneRestriction 1
        (cyclicCenteredEquationGerm k p hp β hβ ζ))) =
      ofFunction (cyclicRotationDefectFunction p β ζ)
        (cyclicRotationDefectFunction_analyticAt p hp β hβ ζ) := by
  apply Subtype.ext
  change ((fun q : Source 1 => cyclicCenteredEquation k p β ζ
    (hyperplaneInclusion 1 (hyperplaneTail 1 (![b q - ζ, q 0])))) : FunctionGerm 1) = _
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro q
  have heq : hyperplaneInclusion 1 (hyperplaneTail 1 (![b q - ζ, q 0])) =
      ![0, q 0] := by
    ext i
    fin_cases i
    · exact hyperplaneInclusion_apply_zero 1 _
    · change (hyperplaneInclusion 1 _ ) (0 : Fin 1).succ = q 0
      rw [hyperplaneInclusion_apply_succ, hyperplaneTail_apply]
      rfl
  change cyclicCenteredEquation k p β ζ
    (hyperplaneInclusion 1 (hyperplaneTail 1 (![b q - ζ, q 0]))) = _
  rw [heq]
  simp [cyclicCenteredEquation, cyclicRotationDefectFunction, hζ]

/-- Exact analytic unit comparison of the two scalar defects. -/
theorem exists_cyclicBranch_defect_unit
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (b : Source 1 → ℂ) (hb : AnalyticAt ℂ b 0) (ζ : ℂ) (hb0 : b 0 = ζ)
    (hζ : ζ ^ k = 1)
    (hsolution : ∀ᶠ q in 𝓝 (0 : Source 1),
      β (q 0 ^ p) - b q ^ k * β (q 0 ^ p * b q) = 0) :
    ∃ ε : Germ 1, IsUnit ε ∧
      1 - ofFunction b hb ^ k =
        ofFunction (cyclicRotationDefectFunction p β ζ)
          (cyclicRotationDefectFunction_analyticAt p hp β hβ ζ) * ε ∧
      valueRingHom 1 ε = -1 / β 0 := by
  obtain ⟨ε, hε, hfactor, hvalue⟩ := cyclicCenteredEquation_power_defect_unit
    k p hk hp β hβ hc ζ hζ (cyclicCenteredBranchMap b hb ζ hb0)
    (cyclicCenteredBranchMap_solves k p hp β hβ b hb ζ hb0 hsolution)
  rw [cyclicCenteredBranchMap_pullback_first,
    cyclicCenteredBranchMap_pullback_axis_defect k p hp β hβ b hb ζ hb0 hζ] at hfactor
  refine ⟨ε, hε, ?_, hvalue⟩
  convert hfactor using 1
  congr 2
  ring

/-- Construct the branch and the unit comparison together from the
prepared analytic coefficient and the chosen root of unity. -/
theorem exists_cyclicBranch_with_defect_unit
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (ζ : ℂ) (hζ : ζ ^ k = 1) :
    ∃ b : Source 1 → ℂ, ∃ hb : AnalyticAt ℂ b 0,
      b 0 = ζ ∧
      (∀ᶠ q in 𝓝 (0 : Source 1),
        β (q 0 ^ p) - b q ^ k * β (q 0 ^ p * b q) = 0) ∧
      ∃ ε : Germ 1, IsUnit ε ∧
        1 - ofFunction b hb ^ k =
          ofFunction (cyclicRotationDefectFunction p β ζ)
            (cyclicRotationDefectFunction_analyticAt p hp β hβ ζ) * ε ∧
        valueRingHom 1 ε = -1 / β 0 := by
  obtain ⟨z, hz, hz0, hsolution⟩ := exists_cyclicPlane_analytic_branch k p hk hp β hβ hc ζ hζ
  let b : Source 1 → ℂ := fun q => z (0, q 0)
  have hparam : AnalyticAt ℂ (fun q : Source 1 => ((0 : ℂ), q 0)) 0 :=
    analyticAt_const.prod
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0)
  have hb : AnalyticAt ℂ b 0 := by
    apply AnalyticAt.comp (x := (0 : Source 1)) _ hparam
    simpa only [Pi.zero_apply, Prod.zero_eq_mk] using hz
  have hb0 : b 0 = ζ := by simpa only [b, Pi.zero_apply, Prod.zero_eq_mk] using hz0
  have hsol : ∀ᶠ q in 𝓝 (0 : Source 1),
      β (q 0 ^ p) - b q ^ k * β (q 0 ^ p * b q) = 0 := by
    have ht : Tendsto (fun q : Source 1 => ((0 : ℂ), q 0))
        (𝓝 0) (𝓝 (0 : ℂ × ℂ)) := by
      simpa only [ContinuousAt, Pi.zero_apply, Prod.zero_eq_mk] using hparam.continuousAt
    filter_upwards [ht.eventually hsolution] with q hq
    simpa only [zero_add] using hq
  exact ⟨b, hb, hb0, hsol,
    exists_cyclicBranch_defect_unit k p hk hp β hβ hc b hb ζ hb0 hζ hsol⟩

end OnLeConjecture.DTwo

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicBranchDefect
public import OnLeConjecture.Analytic.OneVariableRotationOrder
public import OnLeConjecture.Analytic.OneVariablePowerSubstitution

/-!
# The first noninvariant order of the cyclic branch defect

The first nonzero character and its coefficient are selected from the
actual analytic coefficient. Ramification and the proved implicit unit
comparison then give the exact branch-defect exponent.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem cyclicCoefficient_analyticAt (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) :
    AnalyticAt ℂ (fun q : Source 1 => β (q 0)) 0 := by
  apply AnalyticAt.comp (x := (0 : Source 1)) _
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0)
  exact hβ

@[expose] noncomputable def cyclicCoefficientGerm
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) : Germ 1 :=
  ofFunction (fun q : Source 1 => β (q 0)) (cyclicCoefficient_analyticAt β hβ)

theorem cyclicRotationDefect_eq_power_pullback
    (p : ℕ) (hp : 0 < p) (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0)
    (ζ : ℂ) (hζ : ζ ≠ 0) :
    ofFunction (cyclicRotationDefectFunction p β ζ)
      (cyclicRotationDefectFunction_analyticAt p hp β hβ ζ) =
      (oneVariablePowerMapGerm p hp).pullbackRingHom
        (cyclicCoefficientGerm β hβ -
          (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ)).forward.pullbackRingHom
            (cyclicCoefficientGerm β hβ)) := by
  apply Subtype.ext
  change ((cyclicRotationDefectFunction p β ζ) : FunctionGerm 1) =
    ((fun q : Source 1 => β (q 0 ^ p) -
      β (diagonalContinuousLinearEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ)
        (oneVariablePowerMap p q) 0)) : FunctionGerm 1)
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro q
  simp [cyclicRotationDefectFunction, diagonalContinuousLinearEquiv_apply,
    oneVariablePowerMap, mul_comm]

/-- The first noninvariant coefficient determines the exact order and
leading coefficient of the branch defect. -/
theorem cyclicBranch_defect_order_of_noninvariant
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (b : Source 1 → ℂ) (hb : AnalyticAt ℂ b 0) (ζ : ℂ) (hb0 : b 0 = ζ)
    (hζ : ζ ^ k = 1) (hζ0 : ζ ≠ 0)
    (hsolution : ∀ᶠ q in nhds (0 : Source 1),
      β (q 0 ^ p) - b q ^ k * β (q 0 ^ p * b q) = 0)
    (hne : cyclicCoefficientGerm β hβ -
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ0)).forward.pullbackRingHom
        (cyclicCoefficientGerm β hβ) ≠ 0) :
    ∃ j : ℕ, 0 < j ∧ ζ ^ j ≠ 1 ∧
      ∃ u : Germ 1, IsUnit u ∧
        1 - ofFunction b hb ^ k = coordinate (0 : Fin 1) ^ (p * j) * u ∧
        ∃ P : MvPolynomial (Fin 1) ℂ,
          cyclicCoefficientGerm β hβ - coordinatePolynomialAlgHom 1 P ∈
            maximalIdeal 1 ^ (j + 1) ∧
          MvPolynomial.coeff (Finsupp.single 0 j) P ≠ 0 ∧
          valueRingHom 1 u =
            -(MvPolynomial.coeff (Finsupp.single 0 j) P / β 0) * (1 - ζ ^ j) ∧
          ∀ i < j, P.coeff (Finsupp.single 0 i) = 0 ∨ ζ ^ i = 1 := by
  obtain ⟨j, hj, hchar, u, hu, hfactor, P, hP, hPcoeff, hvalue, hprevious⟩ :=
    exists_rotation_difference_order_and_coefficient ζ hζ0 (cyclicCoefficientGerm β hβ) hne
  obtain ⟨ε, hε, hbranch, hεvalue⟩ :=
    exists_cyclicBranch_defect_unit k p hk hp β hβ hc b hb ζ hb0 hζ hsolution
  let v := (oneVariablePowerMapGerm p hp).pullbackRingHom u * ε
  have hv : IsUnit v := (hu.map (oneVariablePowerMapGerm p hp).pullbackRingHom).mul hε
  refine ⟨j, hj, hchar, v, hv, ?_, P, hP, hPcoeff, ?_, hprevious⟩
  · rw [hbranch, cyclicRotationDefect_eq_power_pullback p hp β hβ ζ hζ0,
      hfactor, map_mul, map_pow, oneVariablePowerMapGerm_pullback_coordinate,
      ← pow_mul, mul_assoc]
  · simp only [v, map_mul, PointedMapGerm.valueRingHom_pullback, hvalue, hεvalue]
    ring

/-- An invariant coefficient has identically zero branch defect. -/
theorem cyclicBranch_defect_eq_zero_of_invariant
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (b : Source 1 → ℂ) (hb : AnalyticAt ℂ b 0) (ζ : ℂ) (hb0 : b 0 = ζ)
    (hζ : ζ ^ k = 1) (hζ0 : ζ ≠ 0)
    (hsolution : ∀ᶠ q in nhds (0 : Source 1),
      β (q 0 ^ p) - b q ^ k * β (q 0 ^ p * b q) = 0)
    (hinvariant : cyclicCoefficientGerm β hβ =
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ0)).forward.pullbackRingHom
        (cyclicCoefficientGerm β hβ)) :
    1 - ofFunction b hb ^ k = 0 := by
  obtain ⟨ε, _, hfactor, _⟩ :=
    exists_cyclicBranch_defect_unit k p hk hp β hβ hc b hb ζ hb0 hζ hsolution
  rw [hfactor, cyclicRotationDefect_eq_power_pullback p hp β hβ ζ hζ0,
    sub_eq_zero.mpr hinvariant, map_zero, zero_mul]

end OnLeConjecture.DTwo

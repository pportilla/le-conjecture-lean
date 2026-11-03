/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicPlaneHypersurface
public import OnLeConjecture.DTwo.CyclicBranchDefectOrder

/-!
# The cyclic hypersurface from the actual implicit branch

The second plane equation supplies an analytic branch in the power
difference and the scaling parameter. The first noninvariant coefficient
of the original analytic unit determines the exponent of the first plane
hypersurface. Neither its parameter defect nor its normalizing unit is
assumed.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- Extension of a one-variable germ along the last coordinate. -/
@[expose] noncomputable def cyclicLastExtension : Germ 1 →+* Germ 3 :=
  (hyperplaneExtension 2).comp (hyperplaneExtension 1)

@[simp] theorem cyclicLastExtension_coordinate :
    cyclicLastExtension (coordinate (0 : Fin 1)) = coordinate (2 : Fin 3) := by
  apply Subtype.ext
  rfl

theorem powerDifferenceParameters_pullback_extension (p : ℕ) (f : Germ 1) :
    (powerDifferenceParameters p).pullbackRingHom (hyperplaneExtension 1 f) =
      cyclicLastExtension f := by
  obtain ⟨F, hF, rfl⟩ := exists_ofFunction f
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro q
  change F (hyperplaneTail 1 (![q 0 ^ p - q 1 ^ p, q 2])) =
    F (hyperplaneTail 1 (hyperplaneTail 2 q))
  congr 1
  ext i
  fin_cases i
  rfl

theorem cyclicParameterDefect_eq_lastExtension (p : ℕ) (D : Germ 2) :
    cyclicParameterDefect p D = cyclicLastExtension (hyperplaneRestriction 1 D) :=
  powerDifferenceParameters_pullback_extension p _

theorem cyclicBranchParameters_analyticAt (n : ℕ) (i j : Fin n) :
    AnalyticAt ℂ (fun q : Source n => (q i, q j)) 0 :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt 0).prod
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).analyticAt 0)

theorem cyclicBranchDefect_analyticAt
    (k : ℕ) (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0) :
    AnalyticAt ℂ (fun q : Source 2 => 1 - z (q 0, q 1) ^ k) 0 := by
  have hcomp : AnalyticAt ℂ (fun q : Source 2 => z (q 0, q 1)) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 2)) _ (cyclicBranchParameters_analyticAt 2 0 1)
    simpa only [Pi.zero_apply, Prod.zero_eq_mk] using hz
  exact analyticAt_const.sub (hcomp.pow k)

@[expose] noncomputable def cyclicBranchDefectGerm
    (k : ℕ) (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0) : Germ 2 :=
  ofFunction (fun q : Source 2 => 1 - z (q 0, q 1) ^ k)
    (cyclicBranchDefect_analyticAt k z hz)

theorem cyclicBranchSlice_analyticAt
    (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0) :
    AnalyticAt ℂ (fun q : Source 1 => z (0, q 0)) 0 := by
  apply AnalyticAt.comp (x := (0 : Source 1)) _
    (analyticAt_const.prod
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0))
  simpa only [Pi.zero_apply, map_zero, Prod.zero_eq_mk] using hz

theorem cyclicBranchDefectGerm_restriction
    (k : ℕ) (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0) :
    hyperplaneRestriction 1 (cyclicBranchDefectGerm k z hz) =
      1 - ofFunction (fun q : Source 1 => z (0, q 0))
        (cyclicBranchSlice_analyticAt z hz) ^ k := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro q
  change 1 - z ((hyperplaneInclusion 1 q) 0, (hyperplaneInclusion 1 q) 1) ^ k = _
  rw [hyperplaneInclusion_apply_zero]
  rfl

/-- The second source coordinate after substituting the power difference. -/
@[expose] noncomputable def cyclicPowerDifferenceBranch
    (p : ℕ) (z : ℂ × ℂ → ℂ) (q : Source 3) : ℂ :=
  z (q 0 ^ p - q 1 ^ p, q 2)

theorem cyclicPowerDifferenceBranch_analyticAt
    (p : ℕ) (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0) :
    AnalyticAt ℂ (cyclicPowerDifferenceBranch p z) 0 := by
  have hq (i : Fin 3) : AnalyticAt ℂ (fun q : Source 3 => q i) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) i).analyticAt 0
  apply AnalyticAt.comp (x := (0 : Source 3)) _
    ((((hq 0).pow p).sub ((hq 1).pow p)).prod (hq 2))
  simpa only [Pi.sub_apply, Pi.pow_apply, Pi.zero_apply, sub_self, Prod.zero_eq_mk] using hz

@[simp] theorem cyclicPowerDifferenceBranch_zero
    (p : ℕ) (z : ℂ × ℂ → ℂ) : cyclicPowerDifferenceBranch p z 0 = z 0 := by
  simp only [cyclicPowerDifferenceBranch, Pi.zero_apply, sub_self]
  rfl

theorem cyclicBranchDefectGerm_powerDifference_pullback
    (k p : ℕ) (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0) :
    (powerDifferenceParameters p).pullbackRingHom (cyclicBranchDefectGerm k z hz) =
      1 - ofFunction (cyclicPowerDifferenceBranch p z)
        (cyclicPowerDifferenceBranch_analyticAt p z hz) ^ k := by
  apply Subtype.ext
  rfl

theorem cyclicPowerDifferenceBranch_solves
    (k p : ℕ) (β : ℂ → ℂ) (z : ℂ × ℂ → ℂ)
    (hsol : ∀ᶠ q in 𝓝 (0 : ℂ × ℂ),
      q.1 + β (q.2 ^ p) - z q ^ k * β (q.2 ^ p * z q) = 0) :
    ∀ᶠ q in 𝓝 (0 : Source 3),
      q 0 ^ p - q 1 ^ p + β (q 2 ^ p) -
        cyclicPowerDifferenceBranch p z q ^ k *
          β (q 2 ^ p * cyclicPowerDifferenceBranch p z q) = 0 := by
  have hq (i : Fin 3) : AnalyticAt ℂ (fun q : Source 3 => q i) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) i).analyticAt 0
  have ht : Tendsto (fun q : Source 3 => (q 0 ^ p - q 1 ^ p, q 2))
      (𝓝 0) (𝓝 (0 : ℂ × ℂ)) := by
    simpa only [ContinuousAt, Pi.sub_apply, Pi.pow_apply, Pi.zero_apply, sub_self,
      Prod.zero_eq_mk] using
      ((((hq 0).pow p).sub ((hq 1).pow p)).prod (hq 2)).continuousAt
  exact ht.eventually hsol

/-- The actual parameter defect, including its first noninvariant
coefficient, extracted from the two-parameter branch. -/
theorem cyclicPlane_parameter_defect_order
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (ζ : ℂ) (hζ : ζ ^ k = 1) (hζ0 : ζ ≠ 0)
    (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0) (hz0 : z 0 = ζ)
    (hsol : ∀ᶠ q in 𝓝 (0 : ℂ × ℂ),
      q.1 + β (q.2 ^ p) - z q ^ k * β (q.2 ^ p * z q) = 0)
    (hne : cyclicCoefficientGerm β hβ -
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ0)).forward.pullbackRingHom
        (cyclicCoefficientGerm β hβ) ≠ 0) :
    ∃ j : ℕ, 0 < j ∧ ζ ^ j ≠ 1 ∧ ∃ u : (Germ 1)ˣ,
      cyclicParameterDefect p (cyclicBranchDefectGerm k z hz) =
        coordinate (2 : Fin 3) ^ (p * j) * cyclicLastExtension (↑u : Germ 1) ∧
      ∃ P : MvPolynomial (Fin 1) ℂ,
        cyclicCoefficientGerm β hβ - coordinatePolynomialAlgHom 1 P ∈
          maximalIdeal 1 ^ (j + 1) ∧
        MvPolynomial.coeff (Finsupp.single 0 j) P ≠ 0 ∧
        valueRingHom 1 (↑u : Germ 1) =
          -(MvPolynomial.coeff (Finsupp.single 0 j) P / β 0) * (1 - ζ ^ j) ∧
        ∀ i < j, P.coeff (Finsupp.single 0 i) = 0 ∨ ζ ^ i = 1 := by
  let b : Source 1 → ℂ := fun q => z (0, q 0)
  have hb := cyclicBranchSlice_analyticAt z hz
  have hb0 : b 0 = ζ := by simpa only [b, Pi.zero_apply, Prod.zero_eq_mk] using hz0
  have hparam : AnalyticAt ℂ (fun q : Source 1 => ((0 : ℂ), q 0)) 0 :=
    analyticAt_const.prod
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0)
  have ht : Tendsto (fun q : Source 1 => ((0 : ℂ), q 0))
      (𝓝 0) (𝓝 (0 : ℂ × ℂ)) := by
    simpa only [ContinuousAt, Pi.zero_apply, Prod.zero_eq_mk] using hparam.continuousAt
  have hbsol : ∀ᶠ q in 𝓝 (0 : Source 1),
      β (q 0 ^ p) - b q ^ k * β (q 0 ^ p * b q) = 0 := by
    filter_upwards [ht.eventually hsol] with q hq
    simpa only [zero_add] using hq
  obtain ⟨j, hj, hchar, u, hu, hfactor, P, hP, hPc, hvalue, hprevious⟩ :=
    cyclicBranch_defect_order_of_noninvariant k p hk hp β hβ hc b hb ζ hb0
      hζ hζ0 hbsol hne
  obtain ⟨u, rfl⟩ := hu
  refine ⟨j, hj, hchar, u, ?_, P, hP, hPc, hvalue, hprevious⟩
  rw [cyclicParameterDefect_eq_lastExtension, cyclicBranchDefectGerm_restriction,
    hfactor, map_mul, map_pow, cyclicLastExtension_coordinate]

/-- Construct the first-plane cyclic hypersurface and its exact exponent
from the prepared analytic coefficient. -/
theorem exists_cyclicPlane_actual_hypersurface
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (ζ : ℂ) (hζ : ζ ^ k = 1) (hζ0 : ζ ≠ 0)
    (hne : cyclicCoefficientGerm β hβ -
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ0)).forward.pullbackRingHom
        (cyclicCoefficientGerm β hβ) ≠ 0) :
    ∃ z : ℂ × ℂ → ℂ, ∃ hz : AnalyticAt ℂ z 0,
      z 0 = ζ ∧
      (∀ᶠ q in 𝓝 (0 : ℂ × ℂ),
        q.1 + β (q.2 ^ p) - z q ^ k * β (q.2 ^ p * z q) = 0) ∧
      ∃ j : ℕ, 0 < j ∧ ζ ^ j ≠ 1 ∧
        0 < k * (p - 2) + p * j ∧
        ∃ ε : (Germ 3)ˣ, ∃ e : PointedEquivGerm 3,
          e.forward.pullbackRingHom (coordinate (0 : Fin 3)) = coordinate 0 - coordinate 1 ∧
          e.forward.pullbackRingHom (coordinate (2 : Fin 3)) = coordinate 2 ∧
          e.forward.pullbackRingHom (Analytic.CyclicCover.relationGerm (k * (p - 2) + p * j)) =
            -(↑(ε⁻¹) : Germ 3) *
              (coordinate (0 : Fin 3) ^ 2 - coordinate (1 : Fin 3) ^ 2 +
                coordinate 2 ^ (k * (p - 2)) *
                  (1 - ofFunction (cyclicPowerDifferenceBranch p z)
                    (cyclicPowerDifferenceBranch_analyticAt p z hz) ^ k)) := by
  have hp0 : 0 < p := by omega
  obtain ⟨z, hz, hz0, hsol⟩ := exists_cyclicPlane_analytic_branch k p hk hp0 β hβ hc ζ hζ
  obtain ⟨j, hj, hchar, u, hdefect, _⟩ :=
    cyclicPlane_parameter_defect_order k p hk hp0 β hβ hc ζ hζ hζ0 z hz hz0 hsol hne
  let ε : (Germ 3)ˣ := Units.map cyclicLastExtension u
  have hfactor : coordinate (2 : Fin 3) ^ (k * (p - 2)) *
      cyclicParameterDefect p (cyclicBranchDefectGerm k z hz) =
        coordinate 2 ^ (k * (p - 2) + p * j) * (↑ε : Germ 3) := by
    rw [hdefect, ← mul_assoc, ← pow_add]
    rfl
  obtain ⟨e, he0, he2, heR⟩ := exists_cyclicPlane_normalized_hypersurface
    p (k * (p - 2)) (k * (p - 2) + p * j) hp (cyclicBranchDefectGerm k z hz) ε hfactor
  refine ⟨z, hz, hz0, hsol, j, hj, hchar, by positivity, ε, e, he0, he2, ?_⟩
  rw [cyclicBranchDefectGerm_powerDifference_pullback] at heR
  exact heR

end OnLeConjecture.DTwo

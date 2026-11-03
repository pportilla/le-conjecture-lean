/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AnalyticImplicitFunction
public import OnLeConjecture.Analytic.Hyperplane
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# The analytic branch of the cyclic plane equation

The second plane equation determines the second source coordinate as an
analytic function of the power difference and the deformation parameter.
The nonzero derivative required by the implicit function theorem is proved
from the prepared unit coefficient.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic

/-- The second equation, with parameters `(v, lambda)` and unknown `z`. -/
@[expose] noncomputable def cyclicPlaneEquation (k p : ℕ) (β : ℂ → ℂ)
    (q : (ℂ × ℂ) × ℂ) : ℂ :=
  q.1.1 + β (q.1.2 ^ p) - q.2 ^ k * β (q.1.2 ^ p * q.2)

theorem cyclicPlaneEquation_analyticAt (k p : ℕ) (hp : 0 < p)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (ζ : ℂ) :
    AnalyticAt ℂ (cyclicPlaneEquation k p β) ((0, 0), ζ) := by
  have hv : AnalyticAt ℂ (fun q : (ℂ × ℂ) × ℂ => q.1.1) ((0, 0), ζ) :=
    analyticAt_fst.comp analyticAt_fst
  have hl : AnalyticAt ℂ (fun q : (ℂ × ℂ) × ℂ => q.1.2) ((0, 0), ζ) :=
    analyticAt_snd.comp analyticAt_fst
  have hz : AnalyticAt ℂ (fun q : (ℂ × ℂ) × ℂ => q.2) ((0, 0), ζ) :=
    analyticAt_snd
  have hb1 : AnalyticAt ℂ (fun q : (ℂ × ℂ) × ℂ => β (q.1.2 ^ p))
      ((0, 0), ζ) := by
    apply AnalyticAt.comp (x := ((0, 0), ζ)) _ (hl.pow p)
    simpa only [Pi.pow_apply, zero_pow hp.ne'] using hβ
  have hb2 : AnalyticAt ℂ (fun q : (ℂ × ℂ) × ℂ => β (q.1.2 ^ p * q.2))
      ((0, 0), ζ) := by
    apply AnalyticAt.comp (x := ((0, 0), ζ)) _ ((hl.pow p).mul hz)
    simpa only [Pi.mul_apply, Pi.pow_apply, zero_pow hp.ne', zero_mul] using hβ
  exact (hv.add hb1).sub ((hz.pow k).mul hb2)

theorem cyclicPlaneEquation_pointDerivative_invertible
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (ζ : ℂ) (hζ : ζ ≠ 0) :
    (fderiv ℂ (cyclicPlaneEquation k p β) ((0, 0), ζ) ∘L
      ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ).IsInvertible := by
  let a : ℂ := -((k : ℂ) * ζ ^ (k - 1) * β 0)
  have ha : a ≠ 0 := neg_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hk.ne')
      (pow_ne_zero _ hζ)) hc)
  let e : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha)
  have hderiv : HasFDerivAt
      (fun z : ℂ => cyclicPlaneEquation k p β ((0, 0), z))
      (e : ℂ →L[ℂ] ℂ) ζ := by
    have h : HasDerivAt (fun z : ℂ => β 0 - z ^ k * β 0) a ζ := by
      simpa only [a] using ((hasDerivAt_pow k ζ).mul_const (β 0)).const_sub (β 0)
    have heq : (fun z : ℂ => cyclicPlaneEquation k p β ((0, 0), z)) =
        (fun z : ℂ => β 0 - z ^ k * β 0) := by
      funext z
      simp [cyclicPlaneEquation, zero_pow hp.ne']
    have he : (e : ℂ →L[ℂ] ℂ) = ContinuousLinearMap.toSpanSingleton ℂ a := by
      ext
      simp [e, ContinuousLinearEquiv.smulLeft, mul_comm]
    rw [heq, he]
    exact h.hasFDerivAt
  have hcomp := (cyclicPlaneEquation_analyticAt k p hp β hβ ζ).hasStrictFDerivAt.comp ζ
    (ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ).hasStrictFDerivAt
  exact ⟨e, (hcomp.hasFDerivAt.unique hderiv).symm⟩

/-- The actual two-parameter analytic solution of the second plane equation. -/
theorem exists_cyclicPlane_analytic_branch
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (ζ : ℂ) (hζ : ζ ^ k = 1) :
    ∃ z : ℂ × ℂ → ℂ,
      AnalyticAt ℂ z 0 ∧ z 0 = ζ ∧
      ∀ᶠ q in 𝓝 (0 : ℂ × ℂ),
        q.1 + β (q.2 ^ p) - z q ^ k * β (q.2 ^ p * z q) = 0 := by
  have hζ0 : ζ ≠ 0 := by
    intro hzero
    simp [hzero, zero_pow hk.ne'] at hζ
  let Φ := cyclicPlaneEquation k p β
  have hΦ := cyclicPlaneEquation_analyticAt k p hp β hβ ζ
  have hpoint := cyclicPlaneEquation_pointDerivative_invertible k p hk hp β hβ hc ζ hζ0
  refine ⟨analyticImplicitBranch Φ ((0, 0), ζ) hΦ hpoint,
    analyticAt_analyticImplicitBranch Φ ((0, 0), ζ) hΦ hpoint,
    analyticImplicitBranch_apply_base Φ ((0, 0), ζ) hΦ hpoint, ?_⟩
  have hzero : Φ ((0, 0), ζ) = 0 := by
    simp [Φ, cyclicPlaneEquation, zero_pow hp.ne', hζ]
  simpa only [hzero, Φ, cyclicPlaneEquation, Prod.zero_eq_mk] using
    eventually_analyticImplicitBranch_eq Φ ((0, 0), ζ) hΦ hpoint

/-- Analytic division in the power-difference parameter separates the
one-parameter defect from the term divisible by that difference. -/
theorem cyclicPlane_branch_defect_decomposition
    (k : ℕ) (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0) :
    ∃ K : Source 2 → ℂ, AnalyticAt ℂ K 0 ∧
      ∀ᶠ q in 𝓝 (0 : Source 2),
        1 - z (q 0, q 1) ^ k =
          1 - z (0, q 1) ^ k + q 0 * K q := by
  have hp : AnalyticAt ℂ (fun q : Source 2 => (q 0, q 1)) 0 :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt 0).prod
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt 0)
  have hcomp : AnalyticAt ℂ (fun q : Source 2 => z (q 0, q 1)) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 2)) _ hp
    simpa only [Pi.zero_apply, Prod.zero_eq_mk] using hz
  have hF : AnalyticAt ℂ (fun q : Source 2 => 1 - z (q 0, q 1) ^ k) 0 :=
    analyticAt_const.sub (hcomp.pow k)
  obtain ⟨K, hK, heq⟩ :=
    Analytic.Germ.AnalyticAt.exists_eventuallyEq_hyperplane_add_coordinate_mul hF
  refine ⟨K, hK, ?_⟩
  filter_upwards [heq] with q hq
  simpa only [Analytic.Germ.hyperplaneProjection_apply_zero,
    show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    Analytic.Germ.hyperplaneProjection_apply_succ] using hq

end OnLeConjecture.DTwo

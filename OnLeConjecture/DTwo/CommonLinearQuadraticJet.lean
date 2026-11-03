/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.FullQuadraticJacobianIdeal
public import OnLeConjecture.Analytic.PointBlowupChart
public import OnLeConjecture.Analytic.UnitIntersection
public import OnLeConjecture.PlaneCurve.SmoothStraightening
import Mathlib.Tactic

/-!
# The common-linear-factor quadratic jet

The Jacobian and critical tangent are derived from the two analytic jets
`x²` and `xy`. The critical equation is not supplied with a tangent cone
or an assumed order. The numerical endpoint retains the point-basis and
polar identities as explicit reduction inputs.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ _root_.Polynomial

theorem common_linear_quadratic_jacobian_tail
    (f g : Germ 2)
    (hf : f - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : g - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3) :
    jacobian f g - constRingHom 2 2 * coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3 := by
  have h := normalized_quadratic_jacobian_initial_generators
    f g (coordinate (1 : Fin 2) ^ 2) hf hg (by simp) (2 : Fin 3)
  change constRingHom 2 ((2 : ℂ)⁻¹) * jacobian f g -
    weightedOrderGenerator 1 2 (2 : Fin 3) ∈ maximalIdeal 2 ^ 3 at h
  simp only [weightedOrderGenerator, Fin.val_two, one_mul, Nat.reduceSub,
    pow_zero, mul_one] at h
  have hmul := (maximalIdeal 2 ^ 3).mul_mem_left (constRingHom 2 2) h
  have hscalar : constRingHom 2 2 * constRingHom 2 ((2 : ℂ)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), map_one]
  simpa only [mul_sub, ← mul_assoc, hscalar, one_mul] using hmul

theorem common_linear_quadratic_jacobian_not_mem_cube
    (f g : Germ 2)
    (hf : f - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : g - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3) :
    jacobian f g ∉ maximalIdeal 2 ^ 3 := by
  intro hJ
  have ht := common_linear_quadratic_jacobian_tail f g hf hg
  have hx : constRingHom 2 2 * coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3 := by
    simpa only [sub_sub_cancel] using (maximalIdeal 2 ^ 3).sub_mem hJ ht
  have hres := PointedMapGerm.pullback_mem_maximalIdeal_pow pointBlowupExceptionalLine hx
  have hpoly : (2 * _root_.Polynomial.X ^ 2 : ℂ[X]) ≠ 0 := by simp
  apply oneVariablePolynomialEvaluation_not_mem_pow 2 (2 * _root_.Polynomial.X ^ 2)
    hpoly (by compute_degree)
  simpa only [map_mul, map_pow, PointedMapGerm.pullback_constRingHom,
    pointBlowupExceptionalLine_pullback_zero, oneVariablePolynomialEvaluation,
    map_ofNat, _root_.Polynomial.aeval_X] using hres

/-- The first linear Taylor polynomial, with an analytic remainder in
the square of the maximal ideal. -/
theorem exists_linear_tail_of_mem_maximalIdeal (h : Germ 2) (hh : h ∈ maximalIdeal 2) :
    ∃ a b : ℂ, h - (constRingHom 2 a * coordinate (0 : Fin 2) +
      constRingHom 2 b * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 2 := by
  have hw : h ∈ weightedOrderIdeal 1 1 := by
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow, pow_one] using hh
  obtain ⟨c, hc⟩ := (mem_weightedOrderIdeal_iff 1 1 h).mp hw
  change ∑ i : Fin 2, c i * weightedOrderGenerator 1 1 i = h at hc
  have hcs : c 0 * coordinate 1 + c 1 * coordinate 0 = h := by
    simpa [Fin.sum_univ_two, weightedOrderGenerator] using hc
  refine ⟨valueRingHom 2 (c 1), valueRingHom 2 (c 0), ?_⟩
  have hco (i : Fin 2) : c i - constRingHom 2 (valueRingHom 2 (c i)) ∈ maximalIdeal 2 := by
    simp [mem_maximalIdeal_iff]
  have h0 := Ideal.mul_mem_mul (hco 0) (coordinate_mem_maximalIdeal (1 : Fin 2))
  have h1 := Ideal.mul_mem_mul (hco 1) (coordinate_mem_maximalIdeal (0 : Fin 2))
  rw [← pow_two] at h0 h1
  have heq : h - (constRingHom 2 (valueRingHom 2 (c 1)) * coordinate 0 +
      constRingHom 2 (valueRingHom 2 (c 0)) * coordinate 1) =
      (c 0 - constRingHom 2 (valueRingHom 2 (c 0))) * coordinate 1 +
      (c 1 - constRingHom 2 (valueRingHom 2 (c 1))) * coordinate 0 := by
    rw [← hcs]
    ring
  rw [heq]
  exact Ideal.add_mem _ h0 h1

/-- The common critical power has exponent exactly two, and its quotient
in the Jacobian is a unit. -/
theorem common_linear_quadratic_critical_power
    (f g h : Germ 2)
    (hf : f - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : g - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3)
    (hh : h ∈ maximalIdeal 2) (t : ℕ) (ht : 3 ≤ t)
    (hdiv : h ^ (t - 1) ∣ jacobian f g) :
    t = 3 ∧ ∃ q : Germ 2, IsUnit q ∧ jacobian f g = h ^ 2 * q := by
  have hnot := common_linear_quadratic_jacobian_not_mem_cube f g hf hg
  have htle : t ≤ 3 := by
    by_contra hn
    obtain ⟨q, hq⟩ := hdiv
    apply hnot
    rw [hq]
    exact Ideal.mul_mem_right _ _ ((Ideal.pow_le_pow_right (by omega : 3 ≤ t - 1))
      (Ideal.pow_mem_pow hh (t - 1)))
  have htEq : t = 3 := by omega
  refine ⟨htEq, ?_⟩
  rw [htEq] at hdiv
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨q, ?_, hq⟩
  apply isUnit_of_valueRingHom_ne_zero
  intro hqzero
  apply hnot
  rw [hq]
  have hprod := Ideal.mul_mem_mul (Ideal.pow_mem_pow hh 2) (mem_maximalIdeal_iff.mpr hqzero)
  simpa only [pow_succ] using hprod

/-- The critical equation is smooth and tangent to `x=0`. Both assertions
follow from the analytic divisor relation, not an assumed tangent cone. -/
theorem common_linear_quadratic_critical_tangent
    (f g h : Germ 2)
    (hf : f - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : g - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3)
    (hh : h ∈ maximalIdeal 2) (t : ℕ) (ht : 3 ≤ t)
    (hdiv : h ^ (t - 1) ∣ jacobian f g) :
    t = 3 ∧ differential h ≠ 0 ∧
      ∃ a : ℂ, a ≠ 0 ∧ h - constRingHom 2 a * coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 2 := by
  obtain ⟨htEq, q, hqUnit, hq⟩ := common_linear_quadratic_critical_power f g h hf hg hh t ht hdiv
  have hnot : h ∉ maximalIdeal 2 ^ 2 := by
    intro htwo
    apply common_linear_quadratic_jacobian_not_mem_cube f g hf hg
    rw [hq, pow_two]
    exact Ideal.mul_mem_right q _ (by
      simpa only [pow_succ] using Ideal.mul_mem_mul htwo hh)
  have hdiff : differential h ≠ 0 := by
    intro hz
    apply hnot
    rw [← firstOrderIdeal_eq_maximalIdeal_sq]
    exact ⟨mem_maximalIdeal_iff.mp hh, hz⟩
  obtain ⟨a, b, hlinear⟩ := exists_linear_tail_of_mem_maximalIdeal h hh
  let L : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1
  have hL : L.IsWeightedHomogeneous ![1, 1] 1 := by
    exact ((MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 0).C_mul a).add
      ((MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 1).C_mul b)
  have hlinear' : h - coordinatePolynomialAlgHom 2 L ∈ maximalIdeal 2 ^ 2 := by
    simpa only [L, map_add, map_mul, coordinatePolynomialAlgHom_C,
      coordinatePolynomialAlgHom_X] using hlinear
  have hLmax : coordinatePolynomialAlgHom 2 L ∈ maximalIdeal 2 := by
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow, pow_one] using
      coordinatePolynomial_mem_weightedOrderIdeal 1 1 (by decide) hL
  have hsq : h ^ 2 - coordinatePolynomialAlgHom 2 (L ^ 2) ∈ weightedOrderIdeal 1 3 := by
    rw [weightedOrderIdeal_one_eq_maximalIdeal_pow]
    have hprod := Ideal.mul_mem_mul hlinear' (Ideal.add_mem _ hh hLmax)
    have heq : h ^ 2 - coordinatePolynomialAlgHom 2 (L ^ 2) =
        (h - coordinatePolynomialAlgHom 2 L) * (h + coordinatePolynomialAlgHom 2 L) := by
      rw [map_pow]
      ring
    rw [heq]
    simpa only [pow_succ] using hprod
  have hscaled := mul_weighted_initial_tail 1 2 (by decide) q (h ^ 2) (L ^ 2)
    (by simpa using hL.pow 2) hsq
  rw [weightedOrderIdeal_one_eq_maximalIdeal_pow, mul_comm q, ← hq] at hscaled
  have hJ := common_linear_quadratic_jacobian_tail f g hf hg
  let T : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.C (valueRingHom 2 q) * L ^ 2 - MvPolynomial.C 2 * MvPolynomial.X 0 ^ 2
  have hT : T = 0 := by
    apply eq_zero_of_isWeightedHomogeneous_coordinatePolynomial_mem_succ 1 2 (by decide)
    · exact ((hL.pow 2).C_mul (valueRingHom 2 q)).sub
        (((MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 0).pow 2).C_mul 2)
    · rw [weightedOrderIdeal_one_eq_maximalIdeal_pow]
      have hd := Ideal.sub_mem (maximalIdeal 2 ^ 3) hJ hscaled
      simpa only [T, map_sub, map_mul, map_pow, coordinatePolynomialAlgHom_C,
        coordinatePolynomialAlgHom_X, sub_sub_sub_cancel_left] using hd
  have hb : b = 0 := by
    have heval := congrArg (MvPolynomial.eval (![0, 1] : Fin 2 → ℂ)) hT
    have hvq := valueRingHom_ne_zero_of_isUnit hqUnit
    simpa [T, L, hvq] using heval
  refine ⟨htEq, hdiff, a, ?_, ?_⟩
  · intro ha
    apply hnot
    simpa only [ha, hb, map_zero, zero_mul, add_zero, sub_zero] using hlinear
  · simpa only [hb, map_zero, zero_mul, add_zero] using hlinear

/-- Restriction of a quadratic divisible by the tangent line to the
smooth critical curve has order at least three. Higher analytic terms
are retained. No intersection estimate is assumed. -/
theorem smooth_tangent_common_linear_intersection_ge_three
    (h v : Germ 2) (hh : h ∈ maximalIdeal 2) (hdh : differential h ≠ 0)
    (a α β : ℂ) (ha : a ≠ 0)
    (htangent : h - constRingHom 2 a * coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 2)
    (hv : v - coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3)
    (hfinite : PlaneCurve.HasFiniteIntersection h v) :
    3 ≤ PlaneCurve.intersectionMultiplicity h v hfinite := by
  obtain ⟨e, he, hne, hinter⟩ :=
    PlaneCurve.exists_smoothBranch_intersection_formula h v hh hdh hfinite
  let φ : Germ 2 →ₐ[ℂ] Germ 1 :=
    (hyperplaneRestrictionAlgHom 1).comp e.pullbackAlgEquiv.toAlgHom
  have hφh : φ h = 0 := by
    change hyperplaneRestriction 1 (e.pullbackAlgEquiv h) = 0
    rw [he, hyperplaneRestriction_coordinate_zero]
  have hφconst (z : ℂ) : φ (constRingHom 2 z) = constRingHom 1 z := φ.commutes z
  have hφmem {k : ℕ} {w : Germ 2} (hw : w ∈ maximalIdeal 2 ^ k) :
      φ w ∈ maximalIdeal 1 ^ k :=
    PointedMapGerm.pullback_mem_maximalIdeal_pow (hyperplaneInclusionGerm 1)
      (PointedMapGerm.pullback_mem_maximalIdeal_pow e.forward hw)
  have hx : φ (coordinate (0 : Fin 2)) ∈ maximalIdeal 1 ^ 2 := by
    have hm := hφmem htangent
    rw [map_sub, map_mul, hφh, hφconst, zero_sub] at hm
    have hmpos := (maximalIdeal 1 ^ 2).neg_mem hm
    rw [neg_neg] at hmpos
    have hi := (maximalIdeal 1 ^ 2).mul_mem_left (constRingHom 1 a⁻¹) hmpos
    have hunit : constRingHom 1 a⁻¹ * constRingHom 1 a = 1 := by
      rw [← map_mul, inv_mul_cancel₀ ha, map_one]
    simpa only [← mul_assoc, hunit, one_mul] using hi
  have hlin : φ (constRingHom 2 α * coordinate (0 : Fin 2) +
      constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 1 := by
    have hsource : constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2) ∈ maximalIdeal 2 := Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (coordinate_mem_maximalIdeal 0))
      (Ideal.mul_mem_left _ _ (coordinate_mem_maximalIdeal 1))
    simpa only [pow_one] using hφmem (k := 1) (by simpa only [pow_one] using hsource)
  have hprod : φ (coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2))) ∈ maximalIdeal 1 ^ 3 := by
    rw [map_mul]
    simpa only [pow_succ] using Ideal.mul_mem_mul hx hlin
  have hvord : φ v ∈ maximalIdeal 1 ^ 3 := by
    have htail := hφmem hv
    rw [map_sub] at htail
    simpa only [sub_add_cancel] using Ideal.add_mem _ htail hprod
  rw [hinter]
  have horder := mem_maximalIdeal_one_pow_iff.mp hvord
  have hfiniteOrder : vanishingOrder (φ v) ≠ ⊤ := vanishingOrder_eq_top_iff.not.mpr hne
  exact ENat.toNat_le_toNat horder hfiniteOrder

/-- The analytic common-factor jets supply the critical exponent, the
smooth tangent, and the intersection lower bound simultaneously. -/
theorem common_linear_quadratic_critical_intersection
    (f g h v : Germ 2)
    (hf : f - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : g - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3)
    (hh : h ∈ maximalIdeal 2) (t : ℕ) (ht : 3 ≤ t)
    (hdiv : h ^ (t - 1) ∣ jacobian f g) (α β : ℂ)
    (hv : v - coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3)
    (hfinite : PlaneCurve.HasFiniteIntersection h v) :
    t = 3 ∧ differential h ≠ 0 ∧ 3 ≤ PlaneCurve.intersectionMultiplicity h v hfinite := by
  obtain ⟨htEq, hdiff, a, ha, htail⟩ :=
    common_linear_quadratic_critical_tangent f g h hf hg hh t ht hdiv
  exact ⟨htEq, hdiff, smooth_tangent_common_linear_intersection_ge_three
    h v hh hdiff a α β ha htail hv hfinite⟩

/-- The rank-two common-factor endpoint, with the point-basis count and
polar estimates retained as explicit reduction inputs. -/
theorem common_linear_quadratic_excluded_of_point_counts
    (f g h v : Germ 2)
    (hf : f - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : g - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3)
    (hh : h ∈ maximalIdeal 2) (t A₁ : ℕ) (hA₁ : 1 ≤ A₁) (hMt : 2 + A₁ ≤ t)
    (hdiv : h ^ (t - 1) ∣ jacobian f g) (α β : ℂ)
    (hv : v - coordinate (0 : Fin 2) *
      (constRingHom 2 α * coordinate (0 : Fin 2) +
        constRingHom 2 β * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3)
    (hfinite : PlaneCurve.HasFiniteIntersection h v)
    (hpolar : PlaneCurve.intersectionMultiplicity h v hfinite * (t - 1) ≤ 4 + A₁) : False := by
  obtain ⟨ht, _hsmooth, hi⟩ := common_linear_quadratic_critical_intersection f g h v hf hg hh t
    (by omega) hdiv α β hv hfinite
  simp only [ht, Nat.reduceSub] at hpolar
  omega

end OnLeConjecture.DTwo

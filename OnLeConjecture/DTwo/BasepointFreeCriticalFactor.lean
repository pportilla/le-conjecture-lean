/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrdinaryNodeFactorization
public import OnLeConjecture.Analytic.WeightedPolynomialInitialForm
public import OnLeConjecture.Analytic.OrdinaryIntersectionExact

/-!
# Critical factors for a normalized basepoint-free quadratic pencil

For quadratic initial forms `x²+y²` and `y²`, the normalized Jacobian has
initial form `xy`. Analytic node factorization and unique factorization
then produce a smooth common critical factor from any nonunit common
Jacobian divisor. The smoothness and tangent line are conclusions.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem normalized_basepointFree_jacobian_tail
    (v u : Germ 2)
    (hv : v - (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ 2) ∈ maximalIdeal 2 ^ 3)
    (hu : u - coordinate (1 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3) :
    constRingHom 2 ((4 : ℂ)⁻¹) * jacobian v u - coordinate 0 * coordinate 1 ∈
      maximalIdeal 2 ^ 3 := by
  let X : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0
  let Y : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 1
  have hX : X.IsWeightedHomogeneous ![1, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 0
  have hY : Y.IsWeightedHomogeneous ![1, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 1
  have hP : (X ^ 2 + Y ^ 2).IsWeightedHomogeneous ![1, 1] 2 :=
    (hX.pow 2).add (hY.pow 2)
  have hQ : (Y ^ 2).IsWeightedHomogeneous ![1, 1] 2 := hY.pow 2
  have ht := jacobian_sub_coordinatePolynomial_mem_weightedOrderIdeal
    1 2 2 (by omega) (by omega) (by omega) (X ^ 2 + Y ^ 2) (Y ^ 2) hP hQ v u
    (by simpa [X, Y, weightedOrderIdeal_one_eq_maximalIdeal_pow] using hv)
    (by simpa [Y, weightedOrderIdeal_one_eq_maximalIdeal_pow] using hu)
  have hpoly : OnLeConjecture.Polynomial.jacobian (X ^ 2 + Y ^ 2) (Y ^ 2) =
      MvPolynomial.C 4 * (X * Y) := by
    rw [show (MvPolynomial.C (4 : ℂ) : MvPolynomial (Fin 2) ℂ) = 4 from map_ofNat _ 4]
    norm_num [OnLeConjecture.Polynomial.jacobian, X, Y]
    ring
  rw [hpoly] at ht
  have ht' : jacobian v u - constRingHom 2 4 * (coordinate 0 * coordinate 1) ∈
      maximalIdeal 2 ^ 3 := by
    simpa only [X, Y, map_mul, coordinatePolynomialAlgHom_C,
      coordinatePolynomialAlgHom_X, weightedOrderIdeal_one_eq_maximalIdeal_pow] using ht
  have hm := (maximalIdeal 2 ^ 3).mul_mem_left (constRingHom 2 ((4 : ℂ)⁻¹)) ht'
  have hone : constRingHom 2 ((4 : ℂ)⁻¹) * constRingHom 2 4 = 1 := by
    rw [← map_mul]
    norm_num
  simpa only [mul_sub, ← mul_assoc, hone, one_mul] using hm

/-- A nonunit divisor common to the minors has a constructed smooth
irreducible factor tangent to one coordinate axis. -/
theorem exists_smooth_common_factor_of_normalized_basepointFree_jets
    (v u w c : Germ 2)
    (hv : v - (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ 2) ∈ maximalIdeal 2 ^ 3)
    (hu : u - coordinate (1 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hc : c ∈ maximalIdeal 2)
    (hvu : c ∣ jacobian v u) (hvw : c ∣ jacobian v w) (huw : c ∣ jacobian u w) :
    ∃ h : Germ 2, h ∈ maximalIdeal 2 ∧ differential h ≠ 0 ∧ Irreducible h ∧ h ∣ c ∧
      h ∣ jacobian v u ∧ h ∣ jacobian v w ∧ h ∣ jacobian u w ∧
      (h - coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 2 ∨
        h - coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 2) := by
  let J := constRingHom 2 ((4 : ℂ)⁻¹) * jacobian v u
  have ht : J - coordinate (0 : Fin 2) *
      (constRingHom 2 0 * coordinate 0 + constRingHom 2 1 * coordinate 1) ∈
      maximalIdeal 2 ^ 3 := by
    simpa only [J, map_zero, map_one, zero_mul, one_mul, zero_add] using
      normalized_basepointFree_jacobian_tail v u hv hu
  obtain ⟨F, G, hJ, hFs, hGs, hFi, hGi, _hnot, hFt, hGt⟩ :=
    exists_ordinary_node_smooth_irreducible_factorization J 0 1 (by norm_num) ht
  have hGt' : G - coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 2 := by
    simpa only [map_zero, map_one, zero_mul, one_mul, zero_add] using hGt
  have hJne : J ≠ 0 := by rw [hJ]; exact mul_ne_zero hFi.ne_zero hGi.ne_zero
  have hcJ : c ∣ J := dvd_mul_of_dvd_right hvu _
  have hcne : c ≠ 0 := by
    intro hz
    apply hJne
    simpa [hz] using hcJ
  have hcunit : ¬ IsUnit c := fun hh =>
    (isUnit_iff_valueRingHom_ne_zero.mp hh) (mem_maximalIdeal_iff.mp hc)
  obtain ⟨p, hp, hpc⟩ := WfDvdMonoid.exists_irreducible_factor hcunit hcne
  have hpJ : p ∣ F * G := by rw [← hJ]; exact hpc.trans hcJ
  have hmem (h : Germ 2) (i : Fin 2) (ht : h - coordinate i ∈ maximalIdeal 2 ^ 2) :
      h ∈ maximalIdeal 2 := by
    have ht' := Ideal.pow_le_self (by decide : 2 ≠ 0) ht
    simpa only [sub_add_cancel] using (maximalIdeal 2).add_mem ht' (coordinate_mem_maximalIdeal i)
  rcases hp.prime.dvd_mul.mp hpJ with hpF | hpG
  · have hFc : F ∣ c := ((hp.associated_of_dvd hFi hpF).symm.dvd).trans hpc
    exact ⟨F, hmem F 0 hFt, hFs, hFi, hFc, hFc.trans hvu, hFc.trans hvw,
      hFc.trans huw, Or.inl hFt⟩
  · have hGc : G ∣ c := ((hp.associated_of_dvd hGi hpG).symm.dvd).trans hpc
    exact ⟨G, hmem G 1 hGt', hGs, hGi, hGc, hGc.trans hvu, hGc.trans hvw,
      hGc.trans huw, Or.inr hGt'⟩

/-- The first member is regular of order two in the first coordinate. -/
theorem regular_two_of_sum_squares_quadratic_tail
    (v : Germ 2)
    (hv : v - (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ 2) ∈ maximalIdeal 2 ^ 3) :
    IsRegularInFirstCoordinateOfOrder v 2 := by
  let l := Germ.lineGerm (firstCoordinateVector 1)
  have hcoord (i : Fin 2) : l.pullbackRingHom (coordinate i) =
      constRingHom 1 ((firstCoordinateVector 1) i) * coordinate 0 :=
    lineRestriction_coordinate_eq (firstCoordinateVector 1) i
  have ht := l.pullback_mem_maximalIdeal_pow hv
  have ht' : l.pullbackRingHom v - coordinate (0 : Fin 1) ^ 2 ∈ maximalIdeal 1 ^ 3 := by
    simpa only [map_sub, map_add, map_pow, hcoord, firstCoordinateVector,
      Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      map_one, map_zero, one_mul, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using ht
  rw [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton] at ht'
  obtain ⟨W, hW⟩ := ht'
  have hunit : IsUnit (1 + coordinate (0 : Fin 1) * W) := by
    apply isUnit_of_valueRingHom_ne_zero
    simp
  apply vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hunit
  change l.pullbackRingHom v = coordinate (0 : Fin 1) ^ 2 * (1 + coordinate 0 * W)
  linear_combination hW

/-- Each constructed critical tangent has exact intersection two with
the first member. Both finiteness and the intersection number are derived. -/
theorem intersection_two_of_sum_squares_and_axis_tail
    (v h : Germ 2)
    (hv : v - (coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ 2) ∈ maximalIdeal 2 ^ 3)
    (hh : h - coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 2 ∨
      h - coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 2) :
    ∃ hfinite : PlaneCurve.HasFiniteIntersection v h,
      PlaneCurve.intersectionMultiplicity v h hfinite = 2 := by
  let P : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2
  have hX := MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) (0 : Fin 2)
  have hY := MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) (1 : Fin 2)
  have hP : P.IsWeightedHomogeneous ![1, 1] 2 := (hX.pow 2).add (hY.pow 2)
  have hPne : P ≠ 0 := by
    intro hz
    have h := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → ℂ)) hz
    norm_num [P] at h
  have hv2 : v ∈ maximalIdeal 2 ^ 2 := by
    have hpoly : coordinate (0 : Fin 2) ^ 2 + coordinate 1 ^ 2 ∈ maximalIdeal 2 ^ 2 :=
      (maximalIdeal 2 ^ 2).add_mem
        (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) 2)
        (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) 2)
    simpa only [sub_add_cancel] using (maximalIdeal 2 ^ 2).add_mem
      (Ideal.pow_le_pow_right (by decide : 2 ≤ 3) hv) hpoly
  have hvt : v - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ (2 + 1) := by
    simpa only [P, map_add, map_pow, coordinatePolynomialAlgHom_X] using hv
  have hregular := regular_two_of_sum_squares_quadratic_tail v hv
  rcases hh with hx | hy
  · apply ordinary_intersection_eq_of_regular_no_common_initial_root 2 1 (by omega)
      v h hregular hv2 P (MvPolynomial.X 0) hP hPne hX hvt
      (by simpa only [coordinatePolynomialAlgHom_X] using hx)
    intro z hz
    have hz0 : z = 0 := by simpa using hz.2
    have hh := hz.1
    norm_num [P, hz0] at hh
  · apply ordinary_intersection_eq_of_regular_no_common_initial_root 2 1 (by omega)
      v h hregular hv2 P (MvPolynomial.X 1) hP hPne hY hvt
      (by simpa only [coordinatePolynomialAlgHom_X] using hy)
    intro z hz
    simpa using hz.2

end OnLeConjecture.DTwo

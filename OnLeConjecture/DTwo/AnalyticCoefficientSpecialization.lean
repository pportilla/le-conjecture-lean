/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.AnalyticCoefficientRecurrence

/-!
# Analytic specialization of the quadratic coefficient recurrence

This file specializes the analytic coefficient recurrence at `g = 0`.
It proves divisibility and order bounds for the one variable germs obtained
on the odd and even branches of `x² + yᵏ = 0`.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open Filter

namespace Germ

local instance germOneCharZero : CharZero (Germ 1) :=
  (Germ.valueRingHom 1).charZero

/-- The one variable map `t ↦ t^q`. -/
@[expose]
noncomputable def oneVariablePowerMap (q : ℕ) (z : Source 1) : Source 1 :=
  fun _ ↦ z 0 ^ q

theorem oneVariablePowerMap_analyticAt (q : ℕ) :
    AnalyticAt ℂ (Germ.oneVariablePowerMap q) 0 := by
  apply AnalyticAt.pi
  intro i
  exact ((ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)).analyticAt 0).pow q

theorem oneVariablePowerMap_zero {q : ℕ} (hq : 1 ≤ q) :
    Germ.oneVariablePowerMap q (0 : Source 1) = 0 := by
  ext i
  simp [Germ.oneVariablePowerMap, zero_pow (by omega : q ≠ 0)]

/-- The pointed germ represented by `t ↦ t^q`. -/
@[expose]
noncomputable def oneVariablePowerMapGerm (q : ℕ) (hq : 1 ≤ q) :
    PointedMapGerm 1 1 :=
  PointedMapGerm.ofFunction (Germ.oneVariablePowerMap q)
    (Germ.oneVariablePowerMap_analyticAt q)
    (Germ.oneVariablePowerMap_zero hq)

/-- Substitution of `t^q` in a one variable analytic germ. -/
@[expose]
noncomputable def oneVariablePowerSubstitutionRingHom
    (q : ℕ) (hq : 1 ≤ q) : Germ 1 →+* Germ 1 :=
  (Germ.oneVariablePowerMapGerm q hq).pullbackRingHom

@[simp]
theorem oneVariablePowerSubstitutionRingHom_coordinate
    (q : ℕ) (hq : 1 ≤ q) :
    Germ.oneVariablePowerSubstitutionRingHom q hq
        (Germ.coordinate (0 : Fin 1)) =
      Germ.coordinate (0 : Fin 1) ^ q := by
  rw [Germ.oneVariablePowerSubstitutionRingHom,
    PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rfl

@[simp]
theorem oneVariablePowerSubstitutionRingHom_const
    (q : ℕ) (hq : 1 ≤ q) (c : ℂ) :
    Germ.oneVariablePowerSubstitutionRingHom q hq
        (Germ.constRingHom 1 c) =
      Germ.constRingHom 1 c := by
  exact (Germ.oneVariablePowerMapGerm q hq).pullback_constRingHom c

/-- Divisibility by `t^n` becomes divisibility by `t^(qn)` after
substitution of `t^q`. -/
theorem oneVariablePowerSubstitution_dvd
    {q n : ℕ} (hq : 1 ≤ q) {f : Germ 1}
    (hdiv : Germ.coordinate (0 : Fin 1) ^ n ∣ f) :
    Germ.coordinate (0 : Fin 1) ^ (q * n) ∣
      Germ.oneVariablePowerSubstitutionRingHom q hq f := by
  obtain ⟨R, hR⟩ := hdiv
  refine ⟨Germ.oneVariablePowerSubstitutionRingHom q hq R, ?_⟩
  calc
    Germ.oneVariablePowerSubstitutionRingHom q hq f =
        Germ.oneVariablePowerSubstitutionRingHom q hq
          (Germ.coordinate (0 : Fin 1) ^ n * R) := by rw [hR]
    _ = Germ.oneVariablePowerSubstitutionRingHom q hq
            (Germ.coordinate (0 : Fin 1)) ^ n *
          Germ.oneVariablePowerSubstitutionRingHom q hq R := by
      rw [map_mul, map_pow]
    _ = (Germ.coordinate (0 : Fin 1) ^ q) ^ n *
          Germ.oneVariablePowerSubstitutionRingHom q hq R := by
      rw [Germ.oneVariablePowerSubstitutionRingHom_coordinate]
    _ = Germ.coordinate (0 : Fin 1) ^ (q * n) *
          Germ.oneVariablePowerSubstitutionRingHom q hq R := by
      rw [pow_mul]

/-- Formal divisibility in the first coordinate is equivalent to analytic
divisibility by the corresponding coordinate power. -/
theorem firstCoordinateFormalRingHom_X_pow_dvd_iff
    {n d : ℕ} {f : Germ (n + 1)} :
    PowerSeries.X ^ d ∣ Germ.firstCoordinateFormalRingHom n f ↔
      Germ.coordinate (0 : Fin (n + 1)) ^ d ∣ f := by
  constructor
  · intro hformal
    have hcoeff : ∀ k < d,
        Germ.firstCoordinateTaylorCoefficient k f = 0 := by
      intro k hk
      have hkzero := (PowerSeries.X_pow_dvd_iff.mp hformal) k hk
      simpa using hkzero
    refine ⟨Germ.firstCoordinateTailIterate d f, ?_⟩
    have hsum :
        (∑ k ∈ Finset.range d,
          Germ.coordinate (0 : Fin (n + 1)) ^ k *
            Germ.hyperplaneExtension n
              (Germ.firstCoordinateTaylorCoefficient k f)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [hcoeff k (Finset.mem_range.mp hk), map_zero, mul_zero]
    calc
      f = (∑ k ∈ Finset.range d,
            Germ.coordinate (0 : Fin (n + 1)) ^ k *
              Germ.hyperplaneExtension n
                (Germ.firstCoordinateTaylorCoefficient k f)) +
          Germ.coordinate (0 : Fin (n + 1)) ^ d *
            Germ.firstCoordinateTailIterate d f :=
        Germ.firstCoordinate_finite_expansion f
      _ = Germ.coordinate (0 : Fin (n + 1)) ^ d *
          Germ.firstCoordinateTailIterate d f := by rw [hsum, zero_add]
  · intro hdiv
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨Germ.firstCoordinateFormalRingHom n q, ?_⟩
    calc
      Germ.firstCoordinateFormalRingHom n f =
          Germ.firstCoordinateFormalRingHom n
            (Germ.coordinate (0 : Fin (n + 1)) ^ d * q) := by rw [hq]
      _ = Germ.firstCoordinateFormalRingHom n
              (Germ.coordinate (0 : Fin (n + 1))) ^ d *
            Germ.firstCoordinateFormalRingHom n q := by rw [map_mul, map_pow]
      _ = PowerSeries.X ^ d * Germ.firstCoordinateFormalRingHom n q := by
        rw [Germ.firstCoordinateFormalRingHom_coordinate]

/-- Swapping the plane coordinates and restricting to the first coordinate
axis is restriction to the hyperplane `g = 0`. -/
theorem swap_forward_comp_firstCoordinateLine :
    planeCoordinateSwapEquiv.forward.comp
        (Germ.lineGerm (Germ.firstCoordinateVector 1)) =
      Germ.hyperplaneInclusionGerm 1 := by
  simp only [planeCoordinateSwapEquiv, Germ.lineGerm,
    Germ.hyperplaneInclusionGerm]
  rw [PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    ext i
    fin_cases i
    · simp [Germ.lineMap_apply, Germ.firstCoordinateVector,
        planeCoordinateSwapMap]
    · simp only [Fin.mk_one, Fin.isValue, Function.comp_apply,
        Germ.lineMap_apply, Nat.reduceAdd]
      change (z 0 • Germ.firstCoordinateVector 1) 0 = z 0
      rw [Pi.smul_apply, Germ.firstCoordinateVector_apply_zero]
      change z 0 * 1 = z 0
      exact mul_one (z 0)

/-- Restriction after swapping identifies the first coordinate axis with
the second coordinate axis. -/
theorem lineRestriction_swap_eq_hyperplaneRestriction (f : Germ 2) :
    Germ.lineRestriction (Germ.firstCoordinateVector 1)
        (planeCoordinateSwapEquiv.pullbackAlgEquiv f) =
      Germ.hyperplaneRestriction 1 f := by
  change (Germ.lineGerm (Germ.firstCoordinateVector 1)).pullbackRingHom
      (planeCoordinateSwapEquiv.forward.pullbackRingHom f) =
    (Germ.hyperplaneInclusionGerm 1).pullbackRingHom f
  change ((Germ.lineGerm (Germ.firstCoordinateVector 1)).pullbackRingHom.comp
      planeCoordinateSwapEquiv.forward.pullbackRingHom) f = _
  rw [← PointedMapGerm.pullbackRingHom_comp,
    swap_forward_comp_firstCoordinateLine]

/-- Setting the coefficient variable `g` equal to zero in the second
coordinate formal expansion gives the Taylor series of `f(0,y)`. -/
theorem mapped_secondFormal_eq_taylor_restriction (f : Germ 2) :
    PowerSeries.map (Germ.valueRingHom 1)
        (Germ.secondCoordinateFormalRingHom f) =
      Germ.oneVariableTaylorRingHom (Germ.hyperplaneRestriction 1 f) := by
  apply PowerSeries.ext
  intro j
  rw [PowerSeries.coeff_map, Germ.secondCoordinateFormalRingHom_coeff]
  rw [Germ.oneVariableTaylorRingHom_apply,
    ← Germ.lineRestriction_swap_eq_hyperplaneRestriction f]
  exact (Germ.firstCoordinateAxisTaylorSeries_coeff
    (planeCoordinateSwapEquiv.pullbackAlgEquiv f)).symm

/-- Formal divisibility in the second coordinate is equivalent to analytic
divisibility by the corresponding coordinate power. -/
theorem secondCoordinateFormalRingHom_X_pow_dvd_iff
    {d : ℕ} {f : Germ 2} :
    PowerSeries.X ^ d ∣ Germ.secondCoordinateFormalRingHom f ↔
      Germ.coordinate (1 : Fin 2) ^ d ∣ f := by
  rw [Germ.secondCoordinateFormalRingHom]
  change PowerSeries.X ^ d ∣ Germ.firstCoordinateFormalRingHom 1
      (planeCoordinateSwapEquiv.pullbackAlgEquiv f) ↔ _
  rw [Germ.firstCoordinateFormalRingHom_X_pow_dvd_iff]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨planeCoordinateSwapEquiv.pullbackAlgEquiv q, ?_⟩
    have hmapped := congrArg planeCoordinateSwapEquiv.pullbackAlgEquiv hq
    simpa only [map_mul, map_pow,
      Germ.planeCoordinateSwapEquiv_pullback_zero,
      Germ.planeCoordinateSwapEquiv_pullback_involution] using hmapped
  · rintro ⟨q, hq⟩
    refine ⟨planeCoordinateSwapEquiv.pullbackAlgEquiv q, ?_⟩
    have hmapped := congrArg planeCoordinateSwapEquiv.pullbackAlgEquiv hq
    simpa only [map_mul, map_pow,
      Germ.planeCoordinateSwapEquiv_pullback_one,
      Germ.planeCoordinateSwapEquiv_pullback_involution] using hmapped

/-- Extension of a coefficient germ as a plane germ independent of the
second coordinate. -/
@[expose]
noncomputable def secondCoordinateConstantExtension (q : Germ 1) : Germ 2 :=
  planeCoordinateSwapEquiv.pullbackAlgEquiv
    (Germ.hyperplaneExtension 1 q)

/-- The second coordinate expansion of a germ independent of that
coordinate is constant. -/
theorem secondCoordinateFormalRingHom_constantExtension (q : Germ 1) :
    Germ.secondCoordinateFormalRingHom
        (Germ.secondCoordinateConstantExtension q) =
      PowerSeries.C q := by
  rw [Germ.secondCoordinateFormalRingHom]
  change Germ.firstCoordinateFormalRingHom 1
      (planeCoordinateSwapEquiv.pullbackAlgEquiv
        (planeCoordinateSwapEquiv.pullbackAlgEquiv
          (Germ.hyperplaneExtension 1 q))) = _
  rw [Germ.planeCoordinateSwapEquiv_pullback_involution,
    Germ.firstCoordinateFormalRingHom_hyperplaneExtension]

/-- If `y^(m-1)` divides the derivative of `A` with respect to `y`, then
`y^m` divides `A` after subtraction of its constant coefficient in `y`. -/
theorem secondCoordinate_sub_constantExtension_dvd_of_partialDerivative_dvd
    {m : ℕ} (hm : 1 ≤ m) {A : Germ 2}
    (hderivative : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.partialDerivative (1 : Fin 2) A) :
    Germ.coordinate (1 : Fin 2) ^ m ∣
      A - Germ.secondCoordinateConstantExtension
        (Germ.secondCoordinateTaylorCoefficient 0 A) := by
  apply Germ.secondCoordinateFormalRingHom_X_pow_dvd_iff.mp
  rw [map_sub,
    Germ.secondCoordinateFormalRingHom_constantExtension,
    PowerSeries.X_pow_dvd_iff]
  have hformal : PowerSeries.X ^ (m - 1) ∣
      PowerSeries.derivative (Germ 1)
        (Germ.secondCoordinateFormalRingHom A) := by
    have hmapped := Germ.secondCoordinateFormalRingHom_X_pow_dvd hderivative
    rwa [Germ.secondCoordinateFormalRingHom_partialDerivative_one] at hmapped
  intro n hn
  by_cases hnzero : n = 0
  · subst n
    rw [map_sub, Germ.secondCoordinateFormalRingHom_coeff,
      PowerSeries.coeff_C, if_pos rfl, sub_self]
  · have hpred : n - 1 < m - 1 := by omega
    have hzero := (PowerSeries.X_pow_dvd_iff.mp hformal) (n - 1) hpred
    rw [PowerSeries.coeff_derivative] at hzero
    have hindex : n - 1 + 1 = n := by omega
    have hcast : ((n - 1 : ℕ) : Germ 1) + 1 = (n : Germ 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun a : ℕ ↦ (a : Germ 1)) hindex
    rw [hindex, hcast] at hzero
    have hscalar : (n : Germ 1) ≠ 0 := by
      intro hscalar
      have hmapped := congrArg (Germ.valueRingHom 1) hscalar
      simp only [map_natCast, map_zero] at hmapped
      exact hnzero (Nat.cast_eq_zero.mp hmapped)
    have hcoefficient : PowerSeries.coeff n
        (Germ.secondCoordinateFormalRingHom A) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hscalar
    rw [map_sub, hcoefficient,
      PowerSeries.coeff_C_of_ne_zero hnzero, sub_zero]

/-- Restricting a germ independent of `y` to `g = 0` gives its value at the
origin as a constant one variable germ. -/
theorem hyperplaneRestriction_secondCoordinateConstantExtension
    (q : Germ 1) :
    Germ.hyperplaneRestriction 1
        (Germ.secondCoordinateConstantExtension q) =
      Germ.constRingHom 1 (Germ.valueRingHom 1 q) := by
  apply Germ.oneVariableTaylorRingHom_injective
  rw [← Germ.mapped_secondFormal_eq_taylor_restriction,
    Germ.secondCoordinateFormalRingHom_constantExtension,
    PowerSeries.map_C]
  symm
  change Germ.oneVariableTaylorAlgHom
      (Germ.constRingHom 1 (Germ.valueRingHom 1 q)) =
    PowerSeries.C (Germ.valueRingHom 1 q)
  exact Germ.oneVariableTaylorAlgHom.commutes _

/-- The restriction to `g = 0` of the integrated coefficient is divisible
by `y^m` after subtraction of its value at the origin. -/
theorem hyperplaneRestriction_sub_constant_dvd_of_partialDerivative_dvd
    {m : ℕ} (hm : 1 ≤ m) {A : Germ 2}
    (hderivative : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.partialDerivative (1 : Fin 2) A) :
    Germ.coordinate (0 : Fin 1) ^ m ∣
      Germ.hyperplaneRestriction 1 A -
        Germ.constRingHom 1
          (Germ.valueRingHom 1
            (Germ.secondCoordinateTaylorCoefficient 0 A)) := by
  obtain ⟨Q, hQ⟩ :=
    Germ.secondCoordinate_sub_constantExtension_dvd_of_partialDerivative_dvd
      hm hderivative
  refine ⟨Germ.hyperplaneRestriction 1 Q, ?_⟩
  have hmapped := congrArg (Germ.hyperplaneRestriction 1) hQ
  have hy : Germ.hyperplaneRestriction 1
      (Germ.coordinate (1 : Fin 2)) =
        Germ.coordinate (0 : Fin 1) := by
    simpa only [show (1 : Fin 2) = (0 : Fin 1).succ by decide] using
      Germ.hyperplaneRestriction_coordinate_succ 1 (0 : Fin 1)
  simpa only [map_sub, map_mul, map_pow, hy,
    Germ.hyperplaneRestriction_secondCoordinateConstantExtension] using hmapped

/-- The value at the origin of the constant coefficient in the second
coordinate expansion equals the value of the plane germ. -/
theorem value_secondCoordinateTaylorCoefficient_zero (B : Germ 2) :
    Germ.valueRingHom 1 (Germ.secondCoordinateTaylorCoefficient 0 B) =
      Germ.valueRingHom 2 B := by
  rw [Germ.secondCoordinateTaylorCoefficient,
    Germ.firstCoordinateTaylorCoefficient_zero]
  change Germ.valueRingHom 1
      (Germ.hyperplaneRestriction 1
        (planeCoordinateSwapEquiv.pullbackAlgEquiv B)) = _
  change Germ.valueRingHom 1
      ((Germ.hyperplaneInclusionGerm 1).pullbackRingHom
        (planeCoordinateSwapEquiv.forward.pullbackRingHom B)) = _
  rw [PointedMapGerm.valueRingHom_pullback,
    PointedMapGerm.valueRingHom_pullback]

/-- The first source derivative at the origin of a quadratic base
decomposition is the value of its odd coefficient at the origin. -/
theorem value_partialDerivative_zero_quadraticBase_decomposition
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2) :
    Germ.valueRingHom 2
        (Germ.partialDerivative (0 : Fin 2)
          (Germ.quadraticBaseSubstitutionAlgHom k hk A +
            Germ.coordinate (0 : Fin 2) *
              Germ.quadraticBaseSubstitutionAlgHom k hk B)) =
      Germ.valueRingHom 1
        (Germ.secondCoordinateTaylorCoefficient 0 B) := by
  rw [Germ.partialDerivative_add, Germ.partialDerivative_mul,
    Germ.partialDerivative_coordinate_same,
    Germ.quadraticBaseSubstitutionAlgHom_apply,
    Germ.quadraticBaseSubstitutionAlgHom_apply,
    Germ.partialDerivative_compPointed,
    Germ.partialDerivative_compPointed,
    Germ.quadraticBaseMapGerm_component_zero,
    Germ.quadraticBaseMapGerm_component_one]
  simp only [Germ.partialDerivative_add, Germ.partialDerivative_pow,
    Germ.partialDerivative_coordinate_same,
    Germ.partialDerivative_coordinate_ne (by decide :
      (0 : Fin 2) ≠ (1 : Fin 2)), mul_zero, add_zero,
    one_mul]
  simp only [map_add, map_mul, map_nsmul,
    Germ.valueRingHom_coordinate, mul_zero, add_zero, zero_add,
    Nat.reduceSub, pow_one, smul_eq_mul, mul_one, smul_zero]
  change Germ.valueRingHom 2
      ((Germ.quadraticBaseMapGerm k hk).pullbackRingHom B) =
    Germ.valueRingHom 1 (Germ.secondCoordinateTaylorCoefficient 0 B)
  rw [PointedMapGerm.valueRingHom_pullback,
    Germ.value_secondCoordinateTaylorCoefficient_zero]

/-- Vanishing at the origin of the first source derivative forces the
specialized constant coefficient of the odd part to vanish. -/
theorem specialized_constant_eq_zero_of_value_partialDerivative_zero
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2)
    (hzero : Germ.valueRingHom 2
      (Germ.partialDerivative (0 : Fin 2)
        (Germ.quadraticBaseSubstitutionAlgHom k hk A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom k hk B)) = 0) :
    Germ.valueRingHom 1
        (Germ.secondCoordinateTaylorCoefficient 0 B) = 0 := by
  rw [← Germ.value_partialDerivative_zero_quadraticBase_decomposition
    k hk A B]
  exact hzero

/-- A zero differential forces the specialized constant coefficient of the
odd part to vanish. -/
theorem specialized_constant_eq_zero_of_differential_zero
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2)
    (hzero : Germ.differential
      (Germ.quadraticBaseSubstitutionAlgHom k hk A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom k hk B) = 0) :
    Germ.valueRingHom 1
        (Germ.secondCoordinateTaylorCoefficient 0 B) = 0 := by
  apply Germ.specialized_constant_eq_zero_of_value_partialDerivative_zero
    k hk A B
  rw [Germ.valueRingHom_partialDerivative, hzero]
  rfl

/-- Every controlled coefficient in the zero residue class before index
`j k` vanishes after setting `g = 0`. -/
theorem specialized_secondCoordinateTaylorCoefficient_eq_zero
    {k m j : ℕ} {B : Germ 2}
    (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hrec : SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun n ↦ Germ.secondCoordinateTaylorCoefficient n B) k m)
    (hjm : j * k < m) :
    Germ.valueRingHom 1
        (Germ.secondCoordinateTaylorCoefficient ((j - 1) * k) B) = 0 := by
  exact residue_coefficient_map_eq_zero
    (Germ.valueRingHom 1) hk hj
    (Germ.valueRingHom_coordinate (i := (0 : Fin 1))) hrec hjm

/-- All specialized coefficients below the largest controlled multiple of
`k` vanish. -/
theorem specialized_secondCoordinateTaylorCoefficient_eq_zero_of_lt
    {k m n : ℕ} {B : Germ 2}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun j ↦ Germ.secondCoordinateTaylorCoefficient j B) k m)
    (hn : n < ((m - 1) / k) * k) :
    Germ.valueRingHom 1 (Germ.secondCoordinateTaylorCoefficient n B) = 0 := by
  have hbound : ((m - 1) / k) * k ≤ m - 1 :=
    Nat.div_mul_le_self (m - 1) k
  have hnm : n < m := by omega
  by_cases hdiv : k ∣ n
  · obtain ⟨q, rfl⟩ := hdiv
    have hq : q < (m - 1) / k := by
      apply (Nat.mul_lt_mul_left (by omega : 0 < k)).mp
      simpa [Nat.mul_comm] using hn
    have hqk : (q + 1) * k < m := by
      have hle : (q + 1) * k ≤ ((m - 1) / k) * k :=
        Nat.mul_le_mul_right k (by omega)
      omega
    simpa [Nat.mul_comm] using
      Germ.specialized_secondCoordinateTaylorCoefficient_eq_zero
        hk (by omega) hrec hqk
  · rw [coefficient_eq_zero_of_not_dvd_over hk
      Germ.coordinate_zero_ne_zero hrec hnm hdiv, map_zero]

/-- The specialized odd coefficient `B(0,y)` is divisible by the largest
controlled power of `y` whose exponent is a multiple of `k`. -/
theorem specialized_quadratic_coefficient_dvd
    {k m : ℕ} {B : Germ 2}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun j ↦ Germ.secondCoordinateTaylorCoefficient j B) k m) :
    Germ.coordinate (0 : Fin 1) ^ (((m - 1) / k) * k) ∣
      Germ.hyperplaneRestriction 1 B := by
  rw [← Germ.vanishingOrder_le_iff_dvd,
    Germ.vanishingOrder_coordinate_pow]
  rw [← Germ.order_oneVariableTaylorSeries]
  apply PowerSeries.nat_le_order
  intro n hn
  have hcoefficient := congrArg (PowerSeries.coeff n)
    (Germ.mapped_secondFormal_eq_taylor_restriction B)
  rw [PowerSeries.coeff_map,
    Germ.secondCoordinateFormalRingHom_coeff] at hcoefficient
  change PowerSeries.coeff n
      (Germ.oneVariableTaylorRingHom (Germ.hyperplaneRestriction 1 B)) = 0
  rw [← hcoefficient]
  exact Germ.specialized_secondCoordinateTaylorCoefficient_eq_zero_of_lt
    hk hm hrec hn

/-- If no positive multiple of `k` is controlled and the specialized
constant coefficient vanishes, then `B(0,y)` is divisible by `y^m`. -/
theorem specialized_quadratic_coefficient_dvd_of_div_eq_zero
    {k m : ℕ} {B : Germ 2}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun j ↦ Germ.secondCoordinateTaylorCoefficient j B) k m)
    (hdivzero : (m - 1) / k = 0)
    (hconstant : Germ.valueRingHom 1
      (Germ.secondCoordinateTaylorCoefficient 0 B) = 0) :
    Germ.coordinate (0 : Fin 1) ^ m ∣
      Germ.hyperplaneRestriction 1 B := by
  rw [← Germ.vanishingOrder_le_iff_dvd,
    Germ.vanishingOrder_coordinate_pow]
  rw [← Germ.order_oneVariableTaylorSeries]
  apply PowerSeries.nat_le_order
  intro n hnm
  have hcoefficient := congrArg (PowerSeries.coeff n)
    (Germ.mapped_secondFormal_eq_taylor_restriction B)
  rw [PowerSeries.coeff_map,
    Germ.secondCoordinateFormalRingHom_coeff] at hcoefficient
  change PowerSeries.coeff n
      (Germ.oneVariableTaylorRingHom (Germ.hyperplaneRestriction 1 B)) = 0
  rw [← hcoefficient]
  by_cases hnzero : n = 0
  · simpa [hnzero] using hconstant
  · have hmk : m ≤ k := by
      have hlt : m - 1 < k := Nat.lt_of_div_eq_zero (by omega) hdivzero
      omega
    have hndvd : ¬ k ∣ n :=
      Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rw [coefficient_eq_zero_of_not_dvd_over hk
      Germ.coordinate_zero_ne_zero hrec hnm hndvd, map_zero]

/-- Divisibility of two one variable germs gives the corresponding order
bound after the odd branch substitution `y = t²`, `x = epsilon tᵏ`. -/
theorem odd_branch_analytic_divisible
    {A B : Germ 1} {m n k : ℕ} (epsilon : ℂ)
    (hA : Germ.coordinate (0 : Fin 1) ^ m ∣ A)
    (hB : Germ.coordinate (0 : Fin 1) ^ n ∣ B) :
    Germ.coordinate (0 : Fin 1) ^ min (2 * m) (k + 2 * n) ∣
      Germ.oneVariablePowerSubstitutionRingHom 2 (by omega) A +
        Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ k *
          Germ.oneVariablePowerSubstitutionRingHom 2 (by omega) B := by
  have hAcomp : Germ.coordinate (0 : Fin 1) ^ (2 * m) ∣
      Germ.oneVariablePowerSubstitutionRingHom 2 (by omega) A :=
    Germ.oneVariablePowerSubstitution_dvd (by omega) hA
  have hBcomp : Germ.coordinate (0 : Fin 1) ^ (2 * n) ∣
      Germ.oneVariablePowerSubstitutionRingHom 2 (by omega) B :=
    Germ.oneVariablePowerSubstitution_dvd (by omega) hB
  obtain ⟨R, hR⟩ := hBcomp
  have hshift : Germ.coordinate (0 : Fin 1) ^ (k + 2 * n) ∣
      Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ k *
        Germ.oneVariablePowerSubstitutionRingHom 2 (by omega) B := by
    refine ⟨Germ.constRingHom 1 epsilon * R, ?_⟩
    rw [hR, pow_add]
    ring
  have hleft : Germ.coordinate (0 : Fin 1) ^ min (2 * m) (k + 2 * n) ∣
      Germ.oneVariablePowerSubstitutionRingHom 2 (by omega) A :=
    (pow_dvd_pow (Germ.coordinate (0 : Fin 1))
      (min_le_left _ _)).trans hAcomp
  have hright : Germ.coordinate (0 : Fin 1) ^ min (2 * m) (k + 2 * n) ∣
      Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ k *
        Germ.oneVariablePowerSubstitutionRingHom 2 (by omega) B :=
    (pow_dvd_pow (Germ.coordinate (0 : Fin 1))
      (min_le_right _ _)).trans hshift
  exact dvd_add hleft hright

/-- Divisibility of two one variable germs gives the corresponding order
bound on either even branch `y = t`, `x = epsilon tᵃ`. -/
theorem even_branch_analytic_divisible
    {A B : Germ 1} {m n a : ℕ} (epsilon : ℂ)
    (hA : Germ.coordinate (0 : Fin 1) ^ m ∣ A)
    (hB : Germ.coordinate (0 : Fin 1) ^ n ∣ B) :
    Germ.coordinate (0 : Fin 1) ^ min m (a + n) ∣
      A + Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ a * B := by
  obtain ⟨R, hR⟩ := hB
  have hshift : Germ.coordinate (0 : Fin 1) ^ (a + n) ∣
      Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ a * B := by
    refine ⟨Germ.constRingHom 1 epsilon * R, ?_⟩
    rw [hR, pow_add]
    ring
  have hleft : Germ.coordinate (0 : Fin 1) ^ min m (a + n) ∣ A :=
    (pow_dvd_pow (Germ.coordinate (0 : Fin 1))
      (min_le_left _ _)).trans hA
  have hright : Germ.coordinate (0 : Fin 1) ^ min m (a + n) ∣
      Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ a * B :=
    (pow_dvd_pow (Germ.coordinate (0 : Fin 1))
      (min_le_right _ _)).trans hshift
  exact dvd_add hleft hright

/-- The analytic coefficient recurrence and derivative divisibility imply
the odd branch divisibility bound. -/
theorem odd_branch_specialized_dvd_of_derivative
    {k m : ℕ} {A B : Germ 2} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun j ↦ Germ.secondCoordinateTaylorCoefficient j B) k m)
    (hderivative : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.partialDerivative (1 : Fin 2) A) :
    Germ.coordinate (0 : Fin 1) ^
        min (2 * m) ((2 * ((m - 1) / k) + 1) * k) ∣
      Germ.oneVariablePowerSubstitutionRingHom 2 (by omega)
          (Germ.hyperplaneRestriction 1 A -
            Germ.constRingHom 1
              (Germ.valueRingHom 1
                (Germ.secondCoordinateTaylorCoefficient 0 A))) +
        Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ k *
          Germ.oneVariablePowerSubstitutionRingHom 2 (by omega)
            (Germ.hyperplaneRestriction 1 B) := by
  have hA :=
    Germ.hyperplaneRestriction_sub_constant_dvd_of_partialDerivative_dvd
      hm hderivative
  have hB := Germ.specialized_quadratic_coefficient_dvd hk hm hrec
  have hresult := Germ.odd_branch_analytic_divisible
    (k := k) epsilon hA hB
  have hexponent :
      k + 2 * (((m - 1) / k) * k) =
        (2 * ((m - 1) / k) + 1) * k := by ring
  simpa only [hexponent] using hresult

/-- The analytic coefficient recurrence and derivative divisibility imply
the even branch divisibility bound. -/
theorem even_branch_specialized_dvd_of_derivative
    {k m a : ℕ} {A B : Germ 2} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun j ↦ Germ.secondCoordinateTaylorCoefficient j B) k m)
    (hderivative : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.partialDerivative (1 : Fin 2) A) :
    Germ.coordinate (0 : Fin 1) ^
        min m (a + ((m - 1) / k) * k) ∣
      Germ.hyperplaneRestriction 1 A -
          Germ.constRingHom 1
            (Germ.valueRingHom 1
              (Germ.secondCoordinateTaylorCoefficient 0 A)) +
        Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ a *
          Germ.hyperplaneRestriction 1 B := by
  exact Germ.even_branch_analytic_divisible epsilon
    (Germ.hyperplaneRestriction_sub_constant_dvd_of_partialDerivative_dvd
      hm hderivative)
    (Germ.specialized_quadratic_coefficient_dvd hk hm hrec)

/-- Jacobian divisibility for the quadratic base decomposition implies the
odd branch divisibility bound. -/
theorem odd_branch_specialized_dvd_of_jacobian_dvd
    {k m : ℕ} {A B : Germ 2} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (Germ.quadraticBaseSubstitutionAlgHom k hk A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom k hk B)) :
    Germ.coordinate (0 : Fin 1) ^
        min (2 * m) ((2 * ((m - 1) / k) + 1) * k) ∣
      Germ.oneVariablePowerSubstitutionRingHom 2 (by omega)
          (Germ.hyperplaneRestriction 1 A -
            Germ.constRingHom 1
              (Germ.valueRingHom 1
                (Germ.secondCoordinateTaylorCoefficient 0 A))) +
        Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ k *
          Germ.oneVariablePowerSubstitutionRingHom 2 (by omega)
            (Germ.hyperplaneRestriction 1 B) := by
  have hcoefficients :=
    Germ.coefficient_divisibilities_of_jacobian k m hk A B hdiv
  exact Germ.odd_branch_specialized_dvd_of_derivative epsilon hk hm
    (Germ.satisfiesCoefficientRecurrenceOver_of_analytic_differential_dvd
      hk hcoefficients.2)
    hcoefficients.1

/-- Jacobian divisibility for the quadratic base decomposition implies the
even branch divisibility bound. -/
theorem even_branch_specialized_dvd_of_jacobian_dvd
    {k m a : ℕ} {A B : Germ 2} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (Germ.quadraticBaseSubstitutionAlgHom k hk A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom k hk B)) :
    Germ.coordinate (0 : Fin 1) ^
        min m (a + ((m - 1) / k) * k) ∣
      Germ.hyperplaneRestriction 1 A -
          Germ.constRingHom 1
            (Germ.valueRingHom 1
              (Germ.secondCoordinateTaylorCoefficient 0 A)) +
        Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ a *
          Germ.hyperplaneRestriction 1 B := by
  have hcoefficients :=
    Germ.coefficient_divisibilities_of_jacobian k m hk A B hdiv
  exact Germ.even_branch_specialized_dvd_of_derivative epsilon hk hm
    (Germ.satisfiesCoefficientRecurrenceOver_of_analytic_differential_dvd
      hk hcoefficients.2)
    hcoefficients.1

/-- If no positive multiple of `k` is controlled, the extra constant
coefficient condition gives order at least `2m` on the odd branch. -/
theorem odd_branch_specialized_dvd_of_div_eq_zero
    {k m : ℕ} {A B : Germ 2} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun j ↦ Germ.secondCoordinateTaylorCoefficient j B) k m)
    (hderivative : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.partialDerivative (1 : Fin 2) A)
    (hdivzero : (m - 1) / k = 0)
    (hconstant : Germ.valueRingHom 1
      (Germ.secondCoordinateTaylorCoefficient 0 B) = 0) :
    Germ.coordinate (0 : Fin 1) ^ (2 * m) ∣
      Germ.oneVariablePowerSubstitutionRingHom 2 (by omega)
          (Germ.hyperplaneRestriction 1 A -
            Germ.constRingHom 1
              (Germ.valueRingHom 1
                (Germ.secondCoordinateTaylorCoefficient 0 A))) +
        Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ k *
          Germ.oneVariablePowerSubstitutionRingHom 2 (by omega)
            (Germ.hyperplaneRestriction 1 B) := by
  have hweighted := Germ.odd_branch_analytic_divisible
    (k := k) epsilon
    (Germ.hyperplaneRestriction_sub_constant_dvd_of_partialDerivative_dvd
      hm hderivative)
    (Germ.specialized_quadratic_coefficient_dvd_of_div_eq_zero
      hk hm hrec hdivzero hconstant)
  have hmin : min (2 * m) (k + 2 * m) = 2 * m :=
    min_eq_left (by omega)
  simpa only [hmin] using hweighted

/-- If no positive multiple of `k` is controlled, the extra constant
coefficient condition gives order at least `m` on either even branch. -/
theorem even_branch_specialized_dvd_of_div_eq_zero
    {k m a : ℕ} {A B : Germ 2} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun j ↦ Germ.secondCoordinateTaylorCoefficient j B) k m)
    (hderivative : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.partialDerivative (1 : Fin 2) A)
    (hdivzero : (m - 1) / k = 0)
    (hconstant : Germ.valueRingHom 1
      (Germ.secondCoordinateTaylorCoefficient 0 B) = 0) :
    Germ.coordinate (0 : Fin 1) ^ m ∣
      Germ.hyperplaneRestriction 1 A -
          Germ.constRingHom 1
            (Germ.valueRingHom 1
              (Germ.secondCoordinateTaylorCoefficient 0 A)) +
        Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ a *
          Germ.hyperplaneRestriction 1 B := by
  have hweighted := Germ.even_branch_analytic_divisible
    (a := a) epsilon
    (Germ.hyperplaneRestriction_sub_constant_dvd_of_partialDerivative_dvd
      hm hderivative)
    (Germ.specialized_quadratic_coefficient_dvd_of_div_eq_zero
      hk hm hrec hdivzero hconstant)
  have hmin : min m (a + m) = m := min_eq_left (by omega)
  simpa only [hmin] using hweighted

/-- Divisibility by a coordinate power gives the corresponding lower bound
for the analytic order of vanishing. -/
theorem vanishingOrder_ge_of_coordinate_pow_dvd
    {n : ℕ} {f : Germ 1}
    (hdiv : Germ.coordinate (0 : Fin 1) ^ n ∣ f) :
    (n : ℕ∞) ≤ Germ.vanishingOrder f := by
  have horder := Germ.vanishingOrder_le_iff_dvd.mpr hdiv
  simpa only [Germ.vanishingOrder_coordinate_pow] using horder

/-- The odd branch restriction has at least the order forced by the
coefficient recurrence. -/
theorem odd_branch_specialized_vanishingOrder_of_derivative
    {k m : ℕ} {A B : Germ 2} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun j ↦ Germ.secondCoordinateTaylorCoefficient j B) k m)
    (hderivative : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.partialDerivative (1 : Fin 2) A) :
    ((min (2 * m) ((2 * ((m - 1) / k) + 1) * k) : ℕ) : ℕ∞) ≤
      Germ.vanishingOrder
        (Germ.oneVariablePowerSubstitutionRingHom 2 (by omega)
            (Germ.hyperplaneRestriction 1 A -
              Germ.constRingHom 1
                (Germ.valueRingHom 1
                  (Germ.secondCoordinateTaylorCoefficient 0 A))) +
          Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ k *
            Germ.oneVariablePowerSubstitutionRingHom 2 (by omega)
              (Germ.hyperplaneRestriction 1 B)) := by
  exact Germ.vanishingOrder_ge_of_coordinate_pow_dvd
    (Germ.odd_branch_specialized_dvd_of_derivative
      epsilon hk hm hrec hderivative)

/-- Each even branch restriction has at least the order forced by the
coefficient recurrence. -/
theorem even_branch_specialized_vanishingOrder_of_derivative
    {k m a : ℕ} {A B : Germ 2} (epsilon : ℂ)
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hrec : SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun j ↦ Germ.secondCoordinateTaylorCoefficient j B) k m)
    (hderivative : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.partialDerivative (1 : Fin 2) A) :
    ((min m (a + ((m - 1) / k) * k) : ℕ) : ℕ∞) ≤
      Germ.vanishingOrder
        (Germ.hyperplaneRestriction 1 A -
            Germ.constRingHom 1
              (Germ.valueRingHom 1
                (Germ.secondCoordinateTaylorCoefficient 0 A)) +
          Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ a *
            Germ.hyperplaneRestriction 1 B) := by
  exact Germ.vanishingOrder_ge_of_coordinate_pow_dvd
    (Germ.even_branch_specialized_dvd_of_derivative
      epsilon hk hm hrec hderivative)

end Germ

end OnLeConjecture.DTwo

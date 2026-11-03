/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LinearCoordinates
public import OnLeConjecture.Analytic.OneVariablePowerSubstitution
public import OnLeConjecture.PlaneCurve.Parametrization
public import OnLeConjecture.DTwo.QuadraticIntersectionMatrix

/-!
# Intersection multiplicity on an odd quadratic branch

For odd `k`, the parametrization `t ↦ (epsilon tᵏ,t²)` normalizes
`x²+yᵏ=0`. The determinant of the quadratic multiplication matrix becomes
the product of a branch restriction and its pullback under `t ↦ -t` after
the substitution `y=t²`.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.PlaneCurve
open Filter

namespace Germ

/-- The pointed equivalence represented by `t ↦ -t`. -/
@[expose] noncomputable def oneVariableNegPointedEquiv :
    PointedEquivGerm 1 :=
  Germ.pointedEquivGermOfContinuousLinearEquiv
    (ContinuousLinearEquiv.neg ℂ : Source 1 ≃L[ℂ] Source 1)

/-- Reparametrizing an odd branch by `t ↦ -t` changes the sign of
`epsilon`. -/
theorem oddQuadraticBranchMapGerm_neg_eq_comp_neg
    {k : ℕ} (hk : 1 ≤ k) (hkOdd : Odd k) (epsilon : ℂ) :
    Germ.oddQuadraticBranchMapGerm k hk (-epsilon) =
      (Germ.oddQuadraticBranchMapGerm k hk epsilon).comp
        Germ.oneVariableNegPointedEquiv.forward := by
  simp only [Germ.oddQuadraticBranchMapGerm,
    Germ.oneVariableNegPointedEquiv,
    Germ.pointedEquivGermOfContinuousLinearEquiv]
  rw [PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    ext i
    fin_cases i
    · change -epsilon * z 0 ^ k = epsilon * (-z 0) ^ k
      rw [hkOdd.neg_pow]
      ring
    · change z 0 ^ 2 = (-z 0) ^ 2
      ring

/-- The two signed odd parametrizations give restrictions of the same
vanishing order. -/
theorem vanishingOrder_oddQuadraticBranchMapGerm_neg
    {k : ℕ} (hk : 1 ≤ k) (hkOdd : Odd k) (epsilon : ℂ)
    (u : Germ 2) :
    Germ.vanishingOrder
        ((Germ.oddQuadraticBranchMapGerm k hk (-epsilon)).pullbackRingHom u) =
      Germ.vanishingOrder
        ((Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom u) := by
  rw [Germ.oddQuadraticBranchMapGerm_neg_eq_comp_neg hk hkOdd epsilon,
    PointedMapGerm.pullbackRingHom_comp]
  exact OnLeConjecture.Analytic.Germ.vanishingOrder_ringEquiv
    Germ.oneVariableNegPointedEquiv.pullbackRingEquiv _

/-- Restriction to an odd branch is evaluation of the quadratic remainder
after the substitution `y=t²`. -/
theorem oddQuadraticBranchMapGerm_pullback_eq_remainder
    (k : ℕ) (hk : 1 ≤ k) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (u : Germ 2) :
    (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom u =
      (OnLeConjecture.Analytic.Germ.oneVariablePowerMapGerm
          2 (by omega)).pullbackRingHom
          (quadraticBaseRemainder k hk u 0) +
        Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ k *
          (OnLeConjecture.Analytic.Germ.oneVariablePowerMapGerm
            2 (by omega)).pullbackRingHom
            (quadraticBaseRemainder k hk u 1) := by
  change (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom u =
    (OnLeConjecture.Analytic.Germ.oneVariablePowerMapGerm
        2 (by omega)).pullbackRingHom
        (Germ.hyperplaneRestriction 1
          (quadraticBaseCoefficientPair k hk u).1) +
      Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ k *
        (OnLeConjecture.Analytic.Germ.oneVariablePowerMapGerm
          2 (by omega)).pullbackRingHom
          (Germ.hyperplaneRestriction 1
            (quadraticBaseCoefficientPair k hk u).2)
  conv_lhs =>
    rw [quadraticBaseCoefficientPair_spec k hk u]
  rw [map_add, map_mul,
    Germ.oddQuadraticBranchMapGerm_pullback_quadraticBaseSubstitution
      k hk epsilon hepsilon,
    Germ.oddQuadraticBranchMapGerm_pullback_coordinate_zero,
    Germ.oddQuadraticBranchMapGerm_pullback_quadraticBaseSubstitution
      k hk epsilon hepsilon]
  rfl

/-- After `y=t²`, the determinant of quadratic multiplication factors as
the product of the two signed odd branch restrictions. -/
theorem oneVariablePower_pullback_det_quadraticRemainderMultiplication
    (k : ℕ) (hk : 1 ≤ k) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (u : Germ 2) :
    (OnLeConjecture.Analytic.Germ.oneVariablePowerMapGerm
      2 (by omega)).pullbackRingHom
        (LinearMap.det (quadraticRemainderMultiplication k hk u)) =
      (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom u *
        (Germ.oddQuadraticBranchMapGerm k hk (-epsilon)).pullbackRingHom u := by
  have hnegative : (-epsilon) ^ 2 = -1 := by
    rw [neg_sq, hepsilon]
  rw [det_quadraticRemainderMultiplication,
    map_add, map_pow, map_mul, map_pow,
    OnLeConjecture.Analytic.Germ.oneVariablePowerMapGerm_pullback_coordinate,
    Germ.oddQuadraticBranchMapGerm_pullback_eq_remainder
      k hk epsilon hepsilon u,
    Germ.oddQuadraticBranchMapGerm_pullback_eq_remainder
      k hk (-epsilon) hnegative u]
  have hepsilonGerm :
      (Germ.constRingHom 1 epsilon : Germ 1) ^ 2 = -1 := by
    rw [← map_pow, hepsilon]
    simp
  simp only [map_neg]
  rw [map_pow]
  rw [show (Germ.coordinate (0 : Fin 1) ^ 2) ^ k =
      (Germ.coordinate (0 : Fin 1) ^ k) ^ 2 by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega]
  ring_nf
  rw [hepsilonGerm]
  ring

/-- Finite intersection with the quadratic equation makes its odd branch
restriction nonzero. -/
theorem oddQuadraticBranchMapGerm_pullback_ne_zero_of_base
    (k : ℕ) (hk : 1 ≤ k) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (u : Germ 2)
    (hfinite : HasFiniteIntersection (quadraticBaseEquation k) u) :
    (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom u ≠ 0 := by
  intro hu
  rcases (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le
    (quadraticBaseEquation k) u).mp hfinite with ⟨N, hN⟩
  have hy : Germ.coordinate (1 : Fin 2) ^ N ∈ Germ.maximalIdeal 2 ^ N :=
    Ideal.pow_mem_pow (Germ.coordinate_mem_maximalIdeal 1) N
  have hpair : Germ.coordinate (1 : Fin 2) ^ N ∈
      pairIdeal (quadraticBaseEquation k) u := hN hy
  have hkernel : pairIdeal (quadraticBaseEquation k) u ≤
      RingHom.ker
        (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom := by
    rw [pairIdeal, Ideal.span_le]
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · change
        (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom
          (quadraticBaseEquation k) = 0
      exact Germ.oddQuadraticBranchMapGerm_pullback_equation
        k hk epsilon hepsilon
    · change
        (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom q = 0
      exact hu
  have hyZero := hkernel hpair
  rw [RingHom.mem_ker, map_pow,
    Germ.oddQuadraticBranchMapGerm_pullback_coordinate_one] at hyZero
  exact (pow_ne_zero N
    (pow_ne_zero 2 Germ.coordinate_zero_ne_zero)) hyZero

/-- For odd `k`, local intersection with `x²+yᵏ` equals the vanishing order
along its normalization parametrization. -/
theorem intersectionMultiplicity_odd_quadratic_eq_branch_order
    (k : ℕ) (hk : 1 ≤ k) (hkOdd : Odd k) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (u : Germ 2)
    (hfinite : HasFiniteIntersection (quadraticBaseEquation k) u) :
    intersectionMultiplicity (quadraticBaseEquation k) u hfinite =
      (Germ.vanishingOrder
        ((Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom u)
      ).toNat := by
  let detu := LinearMap.det (quadraticRemainderMultiplication k hk u)
  let pPlus :=
    (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom u
  let pMinus :=
    (Germ.oddQuadraticBranchMapGerm k hk (-epsilon)).pullbackRingHom u
  have hnegative : (-epsilon) ^ 2 = -1 := by
    rw [neg_sq, hepsilon]
  have hplus : pPlus ≠ 0 :=
    Germ.oddQuadraticBranchMapGerm_pullback_ne_zero_of_base
      k hk epsilon hepsilon u hfinite
  have hminus : pMinus ≠ 0 :=
    Germ.oddQuadraticBranchMapGerm_pullback_ne_zero_of_base
      k hk (-epsilon) hnegative u hfinite
  have hdet : detu ≠ 0 := by
    intro hdetZero
    have hpull := Germ.oneVariablePower_pullback_det_quadraticRemainderMultiplication
      k hk epsilon hepsilon u
    rw [show LinearMap.det
        (quadraticRemainderMultiplication k hk u) = detu by rfl,
      hdetZero, map_zero] at hpull
    exact (mul_ne_zero hplus hminus) hpull.symm
  have hdetTop : Germ.vanishingOrder detu ≠ ⊤ := by
    rw [ne_eq, Germ.vanishingOrder_eq_top_iff]
    exact hdet
  have hplusTop : Germ.vanishingOrder pPlus ≠ ⊤ := by
    rw [ne_eq, Germ.vanishingOrder_eq_top_iff]
    exact hplus
  have hminusTop : Germ.vanishingOrder pMinus ≠ ⊤ := by
    rw [ne_eq, Germ.vanishingOrder_eq_top_iff]
    exact hminus
  have hminusOrder : Germ.vanishingOrder pMinus =
      Germ.vanishingOrder pPlus := by
    exact Germ.vanishingOrder_oddQuadraticBranchMapGerm_neg
      hk hkOdd epsilon u
  have hfactor : Germ.vanishingOrder
      ((OnLeConjecture.Analytic.Germ.oneVariablePowerMapGerm
        2 (by omega)).pullbackRingHom detu) =
      Germ.vanishingOrder (pPlus * pMinus) :=
    congrArg Germ.vanishingOrder
      (Germ.oneVariablePower_pullback_det_quadraticRemainderMultiplication
        k hk epsilon hepsilon u)
  have horder : 2 * (Germ.vanishingOrder detu).toNat =
      2 * (Germ.vanishingOrder pPlus).toNat := by
    rw [OnLeConjecture.Analytic.Germ.vanishingOrder_oneVariablePowerMapGerm_pullback,
      two_nsmul, Germ.vanishingOrder_mul, hminusOrder] at hfactor
    have hfactorNat := congrArg ENat.toNat hfactor
    rw [ENat.toNat_add hdetTop hdetTop,
      ENat.toNat_add hplusTop hplusTop] at hfactorNat
    omega
  have hordersEqual : (Germ.vanishingOrder detu).toNat =
      (Germ.vanishingOrder pPlus).toNat := by
    omega
  calc
    intersectionMultiplicity (quadraticBaseEquation k) u hfinite =
        (Germ.vanishingOrder detu).toNat :=
      intersectionMultiplicity_quadraticBaseEquation_eq_det_order
        k hk u hfinite hdet
    _ = (Germ.vanishingOrder pPlus).toNat := hordersEqual

end Germ

end OnLeConjecture.DTwo

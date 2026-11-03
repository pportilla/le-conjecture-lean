/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.AnalyticCoefficientSpecialization

/-!
# Pullback to the branches of a quadratic plane curve

This file defines the one variable parametrizations used for the curve
`x² + yᵏ = 0`. It identifies pullback of a quadratic base decomposition with
the one variable expressions in the coefficient recurrence estimates.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open Filter

namespace Germ

/-- The map `t ↦ (epsilon tᵏ, t²)`. -/
@[expose]
noncomputable def oddQuadraticBranchMap
    (k : ℕ) (epsilon : ℂ) (z : Source 1) : Source 2 :=
  fun i ↦ Fin.cases (epsilon * z 0 ^ k) (fun _ ↦ z 0 ^ 2) i

@[simp]
theorem oddQuadraticBranchMap_apply_zero
    (k : ℕ) (epsilon : ℂ) (z : Source 1) :
    Germ.oddQuadraticBranchMap k epsilon z 0 = epsilon * z 0 ^ k := by
  simp [Germ.oddQuadraticBranchMap]

@[simp]
theorem oddQuadraticBranchMap_apply_one
    (k : ℕ) (epsilon : ℂ) (z : Source 1) :
    Germ.oddQuadraticBranchMap k epsilon z 1 = z 0 ^ 2 := by
  rfl

theorem oddQuadraticBranchMap_analyticAt (k : ℕ) (epsilon : ℂ) :
    AnalyticAt ℂ (Germ.oddQuadraticBranchMap k epsilon) 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · change AnalyticAt ℂ (fun z : Source 1 ↦ epsilon * z 0 ^ k) 0
    exact analyticAt_const.mul
      (((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)).analyticAt 0).pow k)
  · change AnalyticAt ℂ (fun z : Source 1 ↦ z 0 ^ 2) 0
    exact ((ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)).analyticAt 0).pow 2

theorem oddQuadraticBranchMap_zero
    {k : ℕ} (hk : 1 ≤ k) (epsilon : ℂ) :
    Germ.oddQuadraticBranchMap k epsilon (0 : Source 1) = 0 := by
  ext i
  fin_cases i
  · exact Germ.oddQuadraticBranchMap_apply_zero k epsilon 0 |>.trans (by
      simp [zero_pow (by omega : k ≠ 0)])
  · exact Germ.oddQuadraticBranchMap_apply_one k epsilon 0 |>.trans (by simp)

/-- The pointed germ represented by `t ↦ (epsilon tᵏ, t²)`. -/
@[expose]
noncomputable def oddQuadraticBranchMapGerm
    (k : ℕ) (hk : 1 ≤ k) (epsilon : ℂ) : PointedMapGerm 1 2 :=
  PointedMapGerm.ofFunction (Germ.oddQuadraticBranchMap k epsilon)
    (Germ.oddQuadraticBranchMap_analyticAt k epsilon)
    (Germ.oddQuadraticBranchMap_zero hk epsilon)

/-- The map `t ↦ (epsilon tᵃ, t)`. Its values at `epsilon` and
`-epsilon` parametrize the two branches when `k = 2a`. -/
@[expose]
noncomputable def evenQuadraticBranchMap
    (a : ℕ) (epsilon : ℂ) (z : Source 1) : Source 2 :=
  fun i ↦ Fin.cases (epsilon * z 0 ^ a) (fun _ ↦ z 0) i

@[simp]
theorem evenQuadraticBranchMap_apply_zero
    (a : ℕ) (epsilon : ℂ) (z : Source 1) :
    Germ.evenQuadraticBranchMap a epsilon z 0 = epsilon * z 0 ^ a := by
  simp [Germ.evenQuadraticBranchMap]

@[simp]
theorem evenQuadraticBranchMap_apply_one
    (a : ℕ) (epsilon : ℂ) (z : Source 1) :
    Germ.evenQuadraticBranchMap a epsilon z 1 = z 0 := by
  rfl

theorem evenQuadraticBranchMap_analyticAt (a : ℕ) (epsilon : ℂ) :
    AnalyticAt ℂ (Germ.evenQuadraticBranchMap a epsilon) 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · change AnalyticAt ℂ (fun z : Source 1 ↦ epsilon * z 0 ^ a) 0
    exact analyticAt_const.mul
      (((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)).analyticAt 0).pow a)
  · change AnalyticAt ℂ (fun z : Source 1 ↦ z 0) 0
    exact (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)).analyticAt 0

theorem evenQuadraticBranchMap_zero
    {a : ℕ} (ha : 1 ≤ a) (epsilon : ℂ) :
    Germ.evenQuadraticBranchMap a epsilon (0 : Source 1) = 0 := by
  ext i
  fin_cases i
  · exact Germ.evenQuadraticBranchMap_apply_zero a epsilon 0 |>.trans (by
      simp [zero_pow (by omega : a ≠ 0)])
  · exact Germ.evenQuadraticBranchMap_apply_one a epsilon 0 |>.trans (by simp)

/-- The pointed germ represented by `t ↦ (epsilon tᵃ, t)`. -/
@[expose]
noncomputable def evenQuadraticBranchMapGerm
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) : PointedMapGerm 1 2 :=
  PointedMapGerm.ofFunction (Germ.evenQuadraticBranchMap a epsilon)
    (Germ.evenQuadraticBranchMap_analyticAt a epsilon)
    (Germ.evenQuadraticBranchMap_zero ha epsilon)

@[simp]
theorem oddQuadraticBranchMapGerm_pullback_coordinate_zero
    (k : ℕ) (hk : 1 ≤ k) (epsilon : ℂ) :
    (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom
        (Germ.coordinate (0 : Fin 2)) =
      Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ k := by
  rw [PointedMapGerm.pullback_coordinate]
  simp only [Germ.oddQuadraticBranchMapGerm, PointedMapGerm.ofFunction]
  apply Subtype.ext
  rw [MapGerm.component_ofFunction]
  rfl

@[simp]
theorem oddQuadraticBranchMapGerm_pullback_coordinate_one
    (k : ℕ) (hk : 1 ≤ k) (epsilon : ℂ) :
    (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom
        (Germ.coordinate (1 : Fin 2)) =
      Germ.coordinate (0 : Fin 1) ^ 2 := by
  rw [PointedMapGerm.pullback_coordinate]
  simp only [Germ.oddQuadraticBranchMapGerm, PointedMapGerm.ofFunction]
  apply Subtype.ext
  rw [MapGerm.component_ofFunction]
  rfl

@[simp]
theorem evenQuadraticBranchMapGerm_pullback_coordinate_zero
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) :
    (Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom
        (Germ.coordinate (0 : Fin 2)) =
      Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ a := by
  rw [PointedMapGerm.pullback_coordinate]
  simp only [Germ.evenQuadraticBranchMapGerm, PointedMapGerm.ofFunction]
  apply Subtype.ext
  rw [MapGerm.component_ofFunction]
  rfl

@[simp]
theorem evenQuadraticBranchMapGerm_pullback_coordinate_one
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) :
    (Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom
        (Germ.coordinate (1 : Fin 2)) =
      Germ.coordinate (0 : Fin 1) := by
  rw [PointedMapGerm.pullback_coordinate]
  simp only [Germ.evenQuadraticBranchMapGerm, PointedMapGerm.ofFunction]
  apply Subtype.ext
  rw [MapGerm.component_ofFunction]
  rfl

/-- The odd parametrization factors through `x² + yᵏ = 0`. -/
theorem oddQuadraticBranchMapGerm_pullback_equation
    (k : ℕ) (hk : 1 ≤ k) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) :
    (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k) = 0 := by
  rw [map_add, map_pow, map_pow,
    Germ.oddQuadraticBranchMapGerm_pullback_coordinate_zero,
    Germ.oddQuadraticBranchMapGerm_pullback_coordinate_one]
  rw [mul_pow, ← map_pow, hepsilon, map_neg, map_one]
  rw [← pow_mul, Nat.mul_comm k 2]
  ring

/-- If `k = 2a`, the parametrization `t ↦ (epsilon tᵃ,t)` factors
through `x² + yᵏ = 0`. -/
theorem evenQuadraticBranchMapGerm_pullback_equation
    (k a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hk : k = 2 * a) (hepsilon : epsilon ^ 2 = -1) :
    (Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k) = 0 := by
  subst k
  rw [map_add, map_pow, map_pow,
    Germ.evenQuadraticBranchMapGerm_pullback_coordinate_zero,
    Germ.evenQuadraticBranchMapGerm_pullback_coordinate_one]
  rw [mul_pow, ← map_pow, hepsilon, map_neg, map_one]
  ring

/-- The second parametrization `t ↦ (-epsilon tᵃ,t)` also factors
through `x² + y²ᵃ = 0`. -/
theorem evenQuadraticNegativeBranchMapGerm_pullback_equation
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) :
    (Germ.evenQuadraticBranchMapGerm a ha (-epsilon)).pullbackRingHom
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ (2 * a)) = 0 := by
  apply Germ.evenQuadraticBranchMapGerm_pullback_equation
    (k := 2 * a) (a := a) ha (-epsilon) rfl
  rw [neg_sq, hepsilon]

/-- In quadratic base coordinates, the odd parametrization is
`t ↦ (0,t²)`. -/
theorem quadraticBaseMapGerm_comp_oddQuadraticBranchMapGerm
    (k : ℕ) (hk : 1 ≤ k) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) :
    (Germ.quadraticBaseMapGerm k hk).comp
        (Germ.oddQuadraticBranchMapGerm k hk epsilon) =
      (Germ.hyperplaneInclusionGerm 1).comp
        (Germ.oneVariablePowerMapGerm 2 (by omega)) := by
  rw [Germ.quadraticBaseMapGerm, PointedMapGerm.comp_assoc]
  simp only [Germ.quadraticBaseShiftGerm, Germ.quadraticMapGerm,
    Germ.oddQuadraticBranchMapGerm, Germ.hyperplaneInclusionGerm,
    Germ.oneVariablePowerMapGerm, PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    ext i
    fin_cases i
    · change (epsilon * z 0 ^ k) ^ 2 + (z 0 ^ 2) ^ k = 0
      rw [mul_pow, hepsilon, ← pow_mul, Nat.mul_comm k 2]
      ring
    · rfl

/-- In quadratic base coordinates, either even parametrization is
`t ↦ (0,t)`. -/
theorem quadraticBaseMapGerm_comp_evenQuadraticBranchMapGerm
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) :
    (Germ.quadraticBaseMapGerm (2 * a) (by omega)).comp
        (Germ.evenQuadraticBranchMapGerm a ha epsilon) =
      Germ.hyperplaneInclusionGerm 1 := by
  rw [Germ.quadraticBaseMapGerm, PointedMapGerm.comp_assoc]
  simp only [Germ.quadraticBaseShiftGerm, Germ.quadraticMapGerm,
    Germ.evenQuadraticBranchMapGerm, Germ.hyperplaneInclusionGerm,
    PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    ext i
    fin_cases i
    · change (epsilon * z 0 ^ a) ^ 2 + z 0 ^ (2 * a) = 0
      rw [mul_pow, hepsilon, pow_mul]
      ring
    · rfl

/-- Pullback of a base germ along the odd parametrization is obtained by
first setting `g = 0` and then substituting `y = t²`. -/
theorem oddQuadraticBranchMapGerm_pullback_quadraticBaseSubstitution
    (k : ℕ) (hk : 1 ≤ k) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (q : Germ 2) :
    (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom
        (Germ.quadraticBaseSubstitutionAlgHom k hk q) =
      Germ.oneVariablePowerSubstitutionRingHom 2 (by omega)
        (Germ.hyperplaneRestriction 1 q) := by
  rw [Germ.quadraticBaseSubstitutionAlgHom_apply]
  change
    ((Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom.comp
      (Germ.quadraticBaseMapGerm k hk).pullbackRingHom) q =
    ((Germ.oneVariablePowerMapGerm 2 (by omega)).pullbackRingHom.comp
      (Germ.hyperplaneInclusionGerm 1).pullbackRingHom) q
  rw [← PointedMapGerm.pullbackRingHom_comp,
    ← PointedMapGerm.pullbackRingHom_comp,
    Germ.quadraticBaseMapGerm_comp_oddQuadraticBranchMapGerm
      k hk epsilon hepsilon]

/-- Pullback of a base germ along either even parametrization is obtained by
setting `g = 0`. -/
theorem evenQuadraticBranchMapGerm_pullback_quadraticBaseSubstitution
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (q : Germ 2) :
    (Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom
        (Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) q) =
      Germ.hyperplaneRestriction 1 q := by
  rw [Germ.quadraticBaseSubstitutionAlgHom_apply]
  change
    ((Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom.comp
      (Germ.quadraticBaseMapGerm (2 * a) (by omega)).pullbackRingHom) q =
    (Germ.hyperplaneInclusionGerm 1).pullbackRingHom q
  rw [← PointedMapGerm.pullbackRingHom_comp,
    Germ.quadraticBaseMapGerm_comp_evenQuadraticBranchMapGerm
      a ha epsilon hepsilon]

/-- The quadratic base decomposition after subtracting its coefficient
independent of `y`. -/
@[expose]
noncomputable def centeredQuadraticBaseDecomposition
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2) : Germ 2 :=
  Germ.quadraticBaseSubstitutionAlgHom k hk
      (A - Germ.secondCoordinateConstantExtension
        (Germ.secondCoordinateTaylorCoefficient 0 A)) +
    Germ.coordinate (0 : Fin 2) *
      Germ.quadraticBaseSubstitutionAlgHom k hk B

/-- Centering subtracts the analytic function of `g = x²+yᵏ` whose
coefficient is the constant term of `A` in `y`. -/
theorem centeredQuadraticBaseDecomposition_eq
    (k : ℕ) (hk : 1 ≤ k) (A B : Germ 2) :
    Germ.centeredQuadraticBaseDecomposition k hk A B =
      (Germ.quadraticBaseSubstitutionAlgHom k hk A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom k hk B) -
        Germ.quadraticBaseSubstitutionAlgHom k hk
          (Germ.secondCoordinateConstantExtension
            (Germ.secondCoordinateTaylorCoefficient 0 A)) := by
  rw [Germ.centeredQuadraticBaseDecomposition, map_sub]
  ring

/-- Pullback of the centered decomposition along the odd branch is the
specialized expression in the odd branch order estimate. -/
theorem oddQuadraticBranchMapGerm_pullback_centeredDecomposition
    (k : ℕ) (hk : 1 ≤ k) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (A B : Germ 2) :
    (Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom
        (Germ.centeredQuadraticBaseDecomposition k hk A B) =
      Germ.oneVariablePowerSubstitutionRingHom 2 (by omega)
          (Germ.hyperplaneRestriction 1 A -
            Germ.constRingHom 1
              (Germ.valueRingHom 1
                (Germ.secondCoordinateTaylorCoefficient 0 A))) +
        Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ k *
          Germ.oneVariablePowerSubstitutionRingHom 2 (by omega)
            (Germ.hyperplaneRestriction 1 B) := by
  rw [Germ.centeredQuadraticBaseDecomposition, map_add, map_mul,
    Germ.oddQuadraticBranchMapGerm_pullback_quadraticBaseSubstitution
      k hk epsilon hepsilon,
    Germ.oddQuadraticBranchMapGerm_pullback_coordinate_zero,
    Germ.oddQuadraticBranchMapGerm_pullback_quadraticBaseSubstitution
      k hk epsilon hepsilon,
    map_sub, Germ.hyperplaneRestriction_secondCoordinateConstantExtension
  ]

/-- Pullback of the centered decomposition along an even branch is the
specialized expression in the even branch order estimate. -/
theorem evenQuadraticBranchMapGerm_pullback_centeredDecomposition
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (A B : Germ 2) :
    (Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom
        (Germ.centeredQuadraticBaseDecomposition (2 * a) (by omega) A B) =
      Germ.hyperplaneRestriction 1 A -
          Germ.constRingHom 1
            (Germ.valueRingHom 1
              (Germ.secondCoordinateTaylorCoefficient 0 A)) +
        Germ.constRingHom 1 epsilon * Germ.coordinate (0 : Fin 1) ^ a *
          Germ.hyperplaneRestriction 1 B := by
  rw [Germ.centeredQuadraticBaseDecomposition, map_add, map_mul,
    Germ.evenQuadraticBranchMapGerm_pullback_quadraticBaseSubstitution
      a ha epsilon hepsilon,
    Germ.evenQuadraticBranchMapGerm_pullback_coordinate_zero,
    Germ.evenQuadraticBranchMapGerm_pullback_quadraticBaseSubstitution
      a ha epsilon hepsilon,
    map_sub, Germ.hyperplaneRestriction_secondCoordinateConstantExtension]

/-- The coefficient recurrence gives the odd branch order bound for the
pullback of the centered decomposition. -/
theorem oddQuadraticBranch_centered_vanishingOrder_of_derivative
    {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1) (A B : Germ 2)
    (hrec : SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun j ↦ Germ.secondCoordinateTaylorCoefficient j B) k m)
    (hderivative : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.partialDerivative (1 : Fin 2) A) :
    ((min (2 * m) ((2 * ((m - 1) / k) + 1) * k) : ℕ) : ℕ∞) ≤
      Germ.vanishingOrder
        ((Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom
          (Germ.centeredQuadraticBaseDecomposition k hk A B)) := by
  rw [Germ.oddQuadraticBranchMapGerm_pullback_centeredDecomposition
    k hk epsilon hepsilon A B]
  exact Germ.odd_branch_specialized_vanishingOrder_of_derivative
    epsilon hk hm hrec hderivative

/-- Jacobian divisibility gives the odd branch order bound from the article. -/
theorem oddQuadraticBranch_centered_vanishingOrder_of_jacobian_dvd
    {k m : ℕ} (hkOdd : Odd k) (hm : 1 ≤ m)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1) (A B : Germ 2)
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (Germ.quadraticBaseSubstitutionAlgHom k (by
            obtain ⟨r, hr⟩ := hkOdd
            omega) A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom k (by
              obtain ⟨r, hr⟩ := hkOdd
              omega) B)) :
    let hk : 1 ≤ k := by
      obtain ⟨r, hr⟩ := hkOdd
      omega
    ((min (2 * m) ((2 * ((m - 1) / k) + 1) * k) : ℕ) : ℕ∞) ≤
      Germ.vanishingOrder
        ((Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom
          (Germ.centeredQuadraticBaseDecomposition k hk A B)) := by
  dsimp only
  let hk : 1 ≤ k := by
    obtain ⟨r, hr⟩ := hkOdd
    omega
  have hcoefficients :=
    Germ.coefficient_divisibilities_of_jacobian k m hk A B hdiv
  exact Germ.oddQuadraticBranch_centered_vanishingOrder_of_derivative
    hk hm epsilon hepsilon A B
      (Germ.satisfiesCoefficientRecurrenceOver_of_analytic_differential_dvd
        hk hcoefficients.2)
      hcoefficients.1

/-- When the recurrence quotient is zero, a zero differential improves the
odd branch order bound to `2m`. -/
theorem oddQuadraticBranch_centered_vanishingOrder_of_div_eq_zero
    {k m : ℕ} (hkOdd : Odd k) (hm : 1 ≤ m)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1) (A B : Germ 2)
    (hdivzero : (m - 1) / k = 0)
    (hjacobian : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (Germ.quadraticBaseSubstitutionAlgHom k (by
            obtain ⟨r, hr⟩ := hkOdd
            omega) A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom k (by
              obtain ⟨r, hr⟩ := hkOdd
              omega) B))
    (hdifferential : Germ.differential
      (Germ.quadraticBaseSubstitutionAlgHom k (by
          obtain ⟨r, hr⟩ := hkOdd
          omega) A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom k (by
            obtain ⟨r, hr⟩ := hkOdd
            omega) B) = 0) :
    let hk : 1 ≤ k := by
      obtain ⟨r, hr⟩ := hkOdd
      omega
    ((2 * m : ℕ) : ℕ∞) ≤ Germ.vanishingOrder
      ((Germ.oddQuadraticBranchMapGerm k hk epsilon).pullbackRingHom
        (Germ.centeredQuadraticBaseDecomposition k hk A B)) := by
  dsimp only
  let hk : 1 ≤ k := by
    obtain ⟨r, hr⟩ := hkOdd
    omega
  have hcoefficients :=
    Germ.coefficient_divisibilities_of_jacobian k m hk A B hjacobian
  have hconstant :=
    Germ.specialized_constant_eq_zero_of_differential_zero
      k hk A B hdifferential
  rw [Germ.oddQuadraticBranchMapGerm_pullback_centeredDecomposition
    k hk epsilon hepsilon A B]
  exact Germ.vanishingOrder_ge_of_coordinate_pow_dvd
    (Germ.odd_branch_specialized_dvd_of_div_eq_zero
      epsilon hk hm
      (Germ.satisfiesCoefficientRecurrenceOver_of_analytic_differential_dvd
        hk hcoefficients.2)
      hcoefficients.1 hdivzero hconstant)

/-- Jacobian divisibility gives the article's order bound on an even branch. -/
theorem evenQuadraticBranch_centered_vanishingOrder_of_jacobian_dvd
    {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1) (A B : Germ 2)
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ (2 * a))
        (Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) B)) :
    ((min m (a + ((m - 1) / (2 * a)) * (2 * a)) : ℕ) : ℕ∞) ≤
      Germ.vanishingOrder
        ((Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom
          (Germ.centeredQuadraticBaseDecomposition
            (2 * a) (by omega) A B)) := by
  have hcoefficients := Germ.coefficient_divisibilities_of_jacobian
    (2 * a) m (by omega) A B hdiv
  rw [Germ.evenQuadraticBranchMapGerm_pullback_centeredDecomposition
    a ha epsilon hepsilon A B]
  exact Germ.even_branch_specialized_vanishingOrder_of_derivative
    epsilon (by omega) hm
      (Germ.satisfiesCoefficientRecurrenceOver_of_analytic_differential_dvd
        (by omega) hcoefficients.2)
      hcoefficients.1

/-- The same even branch order bound holds simultaneously on
`x = epsilon yᵃ` and `x = -epsilon yᵃ`. -/
theorem evenQuadraticBranches_centered_vanishingOrder_of_jacobian_dvd
    {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1) (A B : Germ 2)
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ (2 * a))
        (Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) B)) :
    let bound : ℕ∞ :=
      (min m (a + ((m - 1) / (2 * a)) * (2 * a)) : ℕ)
    bound ≤ Germ.vanishingOrder
        ((Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom
          (Germ.centeredQuadraticBaseDecomposition
            (2 * a) (by omega) A B)) ∧
      bound ≤ Germ.vanishingOrder
        ((Germ.evenQuadraticBranchMapGerm a ha (-epsilon)).pullbackRingHom
          (Germ.centeredQuadraticBaseDecomposition
            (2 * a) (by omega) A B)) := by
  dsimp only
  constructor
  · exact Germ.evenQuadraticBranch_centered_vanishingOrder_of_jacobian_dvd
      ha hm epsilon hepsilon A B hdiv
  · have hnegative : (-epsilon) ^ 2 = -1 := by
      rw [neg_sq, hepsilon]
    exact Germ.evenQuadraticBranch_centered_vanishingOrder_of_jacobian_dvd
      ha hm (-epsilon) hnegative A B hdiv

/-- When the recurrence quotient is zero, a zero differential gives order
at least `m` on an even branch. -/
theorem evenQuadraticBranch_centered_vanishingOrder_of_div_eq_zero
    {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1) (A B : Germ 2)
    (hdivzero : (m - 1) / (2 * a) = 0)
    (hjacobian : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ (2 * a))
        (Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) B))
    (hdifferential : Germ.differential
      (Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) B) = 0) :
    (m : ℕ∞) ≤ Germ.vanishingOrder
      ((Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom
        (Germ.centeredQuadraticBaseDecomposition
          (2 * a) (by omega) A B)) := by
  have hcoefficients := Germ.coefficient_divisibilities_of_jacobian
    (2 * a) m (by omega) A B hjacobian
  have hconstant :=
    Germ.specialized_constant_eq_zero_of_differential_zero
      (2 * a) (by omega) A B hdifferential
  rw [Germ.evenQuadraticBranchMapGerm_pullback_centeredDecomposition
    a ha epsilon hepsilon A B]
  exact Germ.vanishingOrder_ge_of_coordinate_pow_dvd
    (Germ.even_branch_specialized_dvd_of_div_eq_zero
      epsilon (by omega) hm
      (Germ.satisfiesCoefficientRecurrenceOver_of_analytic_differential_dvd
        (by omega) hcoefficients.2)
      hcoefficients.1 hdivzero hconstant)

/-- In the zero quotient case, both even branches have order at least `m`. -/
theorem evenQuadraticBranches_centered_vanishingOrder_of_div_eq_zero
    {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1) (A B : Germ 2)
    (hdivzero : (m - 1) / (2 * a) = 0)
    (hjacobian : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ (2 * a))
        (Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) B))
    (hdifferential : Germ.differential
      (Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) B) = 0) :
    (m : ℕ∞) ≤ Germ.vanishingOrder
        ((Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom
          (Germ.centeredQuadraticBaseDecomposition
            (2 * a) (by omega) A B)) ∧
      (m : ℕ∞) ≤ Germ.vanishingOrder
        ((Germ.evenQuadraticBranchMapGerm a ha (-epsilon)).pullbackRingHom
          (Germ.centeredQuadraticBaseDecomposition
            (2 * a) (by omega) A B)) := by
  constructor
  · exact Germ.evenQuadraticBranch_centered_vanishingOrder_of_div_eq_zero
      ha hm epsilon hepsilon A B hdivzero hjacobian hdifferential
  · have hnegative : (-epsilon) ^ 2 = -1 := by
      rw [neg_sq, hepsilon]
    exact Germ.evenQuadraticBranch_centered_vanishingOrder_of_div_eq_zero
      ha hm (-epsilon) hnegative A B hdivzero hjacobian hdifferential

end Germ

end OnLeConjecture.DTwo

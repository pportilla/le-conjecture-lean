/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.ParametricMorse

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Tschirnhausen transformations of plane analytic germs

This file proves the analytic coordinate transformations that remove the
next to leading coefficient of a monic cubic or quartic in the first source
coordinate. The coefficients are analytic germs in the second coordinate.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

private theorem cubic_shift_identity {R : Type*} [CommRing R]
    (x b c d r s : R) (hthree : 3 * r = 1)
    (hs : s = 2 * r ^ 3) :
    (x - r * b) ^ 3 + b * (x - r * b) ^ 2 + c * (x - r * b) + d =
      x ^ 3 + (c - r * b ^ 2) * x +
        (d - r * (c * b) + s * b ^ 3) := by
  rw [hs]
  linear_combination
    (-b * x ^ 2 + r * b ^ 2 * x - r ^ 2 * b ^ 3) * hthree

private theorem quartic_shift_identity {R : Type*} [CommRing R]
    (x b c d e r : R) (hfour : 4 * r = 1) :
    (x - r * b) ^ 4 + b * (x - r * b) ^ 3 +
        c * (x - r * b) ^ 2 + d * (x - r * b) + e =
      x ^ 4 + (c - 6 * r ^ 2 * b ^ 2) * x ^ 2 +
        (d - 2 * r * (c * b) + 8 * r ^ 3 * b ^ 3) * x +
        (e - r * (d * b) + r ^ 2 * (c * b ^ 2) -
          3 * r ^ 4 * b ^ 4) := by
  linear_combination (-b * (x - r * b) ^ 3) * hfour

/-- Extension of a one variable coefficient to a plane germ, regarded as a
complex algebra homomorphism. -/
@[expose] noncomputable def planeCoefficientExtension :
    Germ 1 →ₐ[ℂ] Germ 2 :=
  { Germ.hyperplaneExtension 1 with
    commutes' := fun c ↦ by
      change (hyperplaneTailGerm 1).pullbackRingHom
          (Germ.constRingHom 1 c) = Germ.constRingHom 2 c
      exact PointedMapGerm.pullback_constRingHom
        (hyperplaneTailGerm 1) c }

theorem planeCoefficientExtension_apply (q : Germ 1) :
    Germ.planeCoefficientExtension q = Germ.hyperplaneExtension 1 q :=
  rfl

/-- A monic cubic in the first coordinate with coefficients in the second
coordinate. -/
@[expose] noncomputable def monicCubic
    (a₂ a₁ a₀ : Germ 1) : Germ 2 :=
  Germ.coordinate (0 : Fin 2) ^ 3 +
    Germ.planeCoefficientExtension a₂ *
      Germ.coordinate (0 : Fin 2) ^ 2 +
    Germ.planeCoefficientExtension a₁ * Germ.coordinate (0 : Fin 2) +
    Germ.planeCoefficientExtension a₀

/-- The linear coefficient after the cubic Tschirnhausen transformation. -/
@[expose] noncomputable def depressedCubicLinear
    (a₂ a₁ : Germ 1) : Germ 1 :=
  a₁ - (3 : ℂ)⁻¹ • a₂ ^ 2

/-- The constant coefficient after the cubic Tschirnhausen transformation. -/
@[expose] noncomputable def depressedCubicConstant
    (a₂ a₁ a₀ : Germ 1) : Germ 1 :=
  a₀ - (3 : ℂ)⁻¹ • (a₁ * a₂) + (2 / 27 : ℂ) • a₂ ^ 3

/-- The cubic Tschirnhausen coordinate transformation fixes every germ in
the second coordinate and removes the quadratic term. -/
theorem exists_cubic_tschirnhausen
    (a₂ a₁ a₀ : Germ 1) (ha₂ : a₂ ∈ Germ.maximalIdeal 1) :
    ∃ e : PointedEquivGerm 2,
      e.pullbackAlgEquiv (Germ.monicCubic a₂ a₁ a₀) =
        Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension
              (Germ.depressedCubicLinear a₂ a₁) *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension
            (Germ.depressedCubicConstant a₂ a₁ a₀) ∧
      ∀ q : Germ 1,
        e.pullbackAlgEquiv (Germ.planeCoefficientExtension q) =
          Germ.planeCoefficientExtension q := by
  let shift : Germ 1 := -((3 : ℂ)⁻¹) • a₂
  let shiftedCoordinate : Germ 2 :=
    Germ.coordinate (0 : Fin 2) + Germ.planeCoefficientExtension shift
  have hshift : shift ∈ Germ.maximalIdeal 1 := by
    exact (Germ.maximalIdeal 1).smul_mem _ ha₂
  have hshifted : shiftedCoordinate ∈ Germ.maximalIdeal 2 := by
    apply (Germ.maximalIdeal 2).add_mem
    · exact Germ.coordinate_mem_maximalIdeal _
    · exact (hyperplaneTailGerm 1).pullback_mem_maximalIdeal hshift
  have hextDifferential : Germ.differential
      (Germ.planeCoefficientExtension shift)
      (Germ.firstCoordinateVector 1) = 0 := by
    change Germ.differential (Germ.hyperplaneExtension 1 shift)
      (Germ.coordinateVector (0 : Fin 2)) = 0
    rw [← Germ.valueRingHom_partialDerivative,
      Germ.partialDerivative_zero_hyperplaneExtension]
    exact map_zero (Germ.valueRingHom 2)
  have hregular : Germ.differential shiftedCoordinate
      (Germ.firstCoordinateVector 1) ≠ 0 := by
    rw [Germ.differential_add]
    change Germ.differential (Germ.coordinate (0 : Fin 2))
        (Germ.firstCoordinateVector 1) +
      Germ.differential (Germ.planeCoefficientExtension shift)
        (Germ.firstCoordinateVector 1) ≠ 0
    rw [Germ.differential_coordinate_apply, hextDifferential, add_zero]
    simp [Germ.firstCoordinateVector]
  obtain ⟨e, heCoordinate, heCoefficient⟩ :=
    Germ.exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension
      shiftedCoordinate hshifted hregular
  have hePlane (q : Germ 1) :
      e.pullbackAlgEquiv (Germ.planeCoefficientExtension q) =
        Germ.planeCoefficientExtension q := by
    change e.pullbackAlgEquiv (Germ.hyperplaneExtension 1 q) =
      Germ.hyperplaneExtension 1 q
    exact heCoefficient q
  let scalarThird : Germ 2 :=
    (algebraMap ℂ (Germ 2)) (1 / 3 : ℂ)
  let scalarTwoTwentySeven : Germ 2 :=
    (algebraMap ℂ (Germ 2)) (2 / 27 : ℂ)
  have hthree : 3 * scalarThird = 1 := by
    dsimp only [scalarThird]
    change (algebraMap ℂ (Germ 2)) (3 : ℂ) *
      (algebraMap ℂ (Germ 2)) (1 / 3 : ℂ) =
        (algebraMap ℂ (Germ 2)) (1 : ℂ)
    rw [← map_mul]
    norm_num
  have htwoTwentySeven :
      scalarTwoTwentySeven = 2 * scalarThird ^ 3 := by
    dsimp only [scalarTwoTwentySeven, scalarThird]
    change (algebraMap ℂ (Germ 2)) (2 / 27 : ℂ) =
      (algebraMap ℂ (Germ 2)) (2 : ℂ) *
        (algebraMap ℂ (Germ 2)) (1 / 3 : ℂ) ^ 3
    rw [← map_pow, ← map_mul]
    norm_num
  have hidentity := cubic_shift_identity
    (Germ.coordinate (0 : Fin 2))
    (Germ.planeCoefficientExtension a₂)
    (Germ.planeCoefficientExtension a₁)
    (Germ.planeCoefficientExtension a₀)
    scalarThird scalarTwoTwentySeven hthree htwoTwentySeven
  refine ⟨e, ?_, ?_⟩
  · simp only [Germ.monicCubic, map_add, map_mul, map_pow,
      heCoordinate]
    rw [hePlane a₂, hePlane a₁, hePlane a₀]
    simpa [shift, shiftedCoordinate, Germ.depressedCubicLinear,
      Germ.depressedCubicConstant, scalarThird,
      scalarTwoTwentySeven, Algebra.smul_def, sub_eq_add_neg,
      div_eq_mul_inv] using hidentity
  · intro q
    exact heCoefficient q

/-- A monic quartic in the first coordinate with coefficients in the second
coordinate. -/
@[expose] noncomputable def monicQuartic
    (a₃ a₂ a₁ a₀ : Germ 1) : Germ 2 :=
  Germ.coordinate (0 : Fin 2) ^ 4 +
    Germ.planeCoefficientExtension a₃ *
      Germ.coordinate (0 : Fin 2) ^ 3 +
    Germ.planeCoefficientExtension a₂ *
      Germ.coordinate (0 : Fin 2) ^ 2 +
    Germ.planeCoefficientExtension a₁ * Germ.coordinate (0 : Fin 2) +
    Germ.planeCoefficientExtension a₀

/-- The quadratic coefficient after the quartic Tschirnhausen
transformation. -/
@[expose] noncomputable def depressedQuarticQuadratic
    (a₃ a₂ : Germ 1) : Germ 1 :=
  a₂ - (3 / 8 : ℂ) • a₃ ^ 2

/-- The linear coefficient after the quartic Tschirnhausen transformation. -/
@[expose] noncomputable def depressedQuarticLinear
    (a₃ a₂ a₁ : Germ 1) : Germ 1 :=
  a₁ - (1 / 2 : ℂ) • (a₂ * a₃) + (1 / 8 : ℂ) • a₃ ^ 3

/-- The constant coefficient after the quartic Tschirnhausen
transformation. -/
@[expose] noncomputable def depressedQuarticConstant
    (a₃ a₂ a₁ a₀ : Germ 1) : Germ 1 :=
  a₀ - (1 / 4 : ℂ) • (a₁ * a₃) +
    (1 / 16 : ℂ) • (a₂ * a₃ ^ 2) - (3 / 256 : ℂ) • a₃ ^ 4

/-- The quartic Tschirnhausen coordinate transformation fixes every germ in
the second coordinate and removes the cubic term. -/
theorem exists_quartic_tschirnhausen
    (a₃ a₂ a₁ a₀ : Germ 1) (ha₃ : a₃ ∈ Germ.maximalIdeal 1) :
    ∃ e : PointedEquivGerm 2,
      e.pullbackAlgEquiv (Germ.monicQuartic a₃ a₂ a₁ a₀) =
        Germ.coordinate (0 : Fin 2) ^ 4 +
          Germ.planeCoefficientExtension
              (Germ.depressedQuarticQuadratic a₃ a₂) *
            Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.planeCoefficientExtension
              (Germ.depressedQuarticLinear a₃ a₂ a₁) *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension
            (Germ.depressedQuarticConstant a₃ a₂ a₁ a₀) ∧
      ∀ q : Germ 1,
        e.pullbackAlgEquiv (Germ.planeCoefficientExtension q) =
          Germ.planeCoefficientExtension q := by
  let shift : Germ 1 := -((4 : ℂ)⁻¹) • a₃
  let shiftedCoordinate : Germ 2 :=
    Germ.coordinate (0 : Fin 2) + Germ.planeCoefficientExtension shift
  have hshift : shift ∈ Germ.maximalIdeal 1 := by
    exact (Germ.maximalIdeal 1).smul_mem _ ha₃
  have hshifted : shiftedCoordinate ∈ Germ.maximalIdeal 2 := by
    apply (Germ.maximalIdeal 2).add_mem
    · exact Germ.coordinate_mem_maximalIdeal _
    · exact (hyperplaneTailGerm 1).pullback_mem_maximalIdeal hshift
  have hextDifferential : Germ.differential
      (Germ.planeCoefficientExtension shift)
      (Germ.firstCoordinateVector 1) = 0 := by
    change Germ.differential (Germ.hyperplaneExtension 1 shift)
      (Germ.coordinateVector (0 : Fin 2)) = 0
    rw [← Germ.valueRingHom_partialDerivative,
      Germ.partialDerivative_zero_hyperplaneExtension]
    exact map_zero (Germ.valueRingHom 2)
  have hregular : Germ.differential shiftedCoordinate
      (Germ.firstCoordinateVector 1) ≠ 0 := by
    rw [Germ.differential_add]
    change Germ.differential (Germ.coordinate (0 : Fin 2))
        (Germ.firstCoordinateVector 1) +
      Germ.differential (Germ.planeCoefficientExtension shift)
        (Germ.firstCoordinateVector 1) ≠ 0
    rw [Germ.differential_coordinate_apply, hextDifferential, add_zero]
    simp [Germ.firstCoordinateVector]
  obtain ⟨e, heCoordinate, heCoefficient⟩ :=
    Germ.exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension
      shiftedCoordinate hshifted hregular
  have hePlane (q : Germ 1) :
      e.pullbackAlgEquiv (Germ.planeCoefficientExtension q) =
        Germ.planeCoefficientExtension q := by
    change e.pullbackAlgEquiv (Germ.hyperplaneExtension 1 q) =
      Germ.hyperplaneExtension 1 q
    exact heCoefficient q
  let scalarFourth : Germ 2 :=
    (algebraMap ℂ (Germ 2)) (1 / 4 : ℂ)
  have hfour : 4 * scalarFourth = 1 := by
    dsimp only [scalarFourth]
    change (algebraMap ℂ (Germ 2)) (4 : ℂ) *
      (algebraMap ℂ (Germ 2)) (1 / 4 : ℂ) =
        (algebraMap ℂ (Germ 2)) (1 : ℂ)
    rw [← map_mul]
    norm_num
  have hthreeEighths :
      (algebraMap ℂ (Germ 2)) (3 / 8 : ℂ) =
        6 * (algebraMap ℂ (Germ 2)) (1 / 4 : ℂ) ^ 2 := by
    change (algebraMap ℂ (Germ 2)) (3 / 8 : ℂ) =
      (algebraMap ℂ (Germ 2)) (6 : ℂ) *
        (algebraMap ℂ (Germ 2)) (1 / 4 : ℂ) ^ 2
    rw [← map_pow, ← map_mul]
    norm_num
  have hhalf :
      (algebraMap ℂ (Germ 2)) (1 / 2 : ℂ) =
        2 * (algebraMap ℂ (Germ 2)) (1 / 4 : ℂ) := by
    change (algebraMap ℂ (Germ 2)) (1 / 2 : ℂ) =
      (algebraMap ℂ (Germ 2)) (2 : ℂ) *
        (algebraMap ℂ (Germ 2)) (1 / 4 : ℂ)
    rw [← map_mul]
    norm_num
  have heighth :
      (algebraMap ℂ (Germ 2)) (1 / 8 : ℂ) =
        8 * (algebraMap ℂ (Germ 2)) (1 / 4 : ℂ) ^ 3 := by
    change (algebraMap ℂ (Germ 2)) (1 / 8 : ℂ) =
      (algebraMap ℂ (Germ 2)) (8 : ℂ) *
        (algebraMap ℂ (Germ 2)) (1 / 4 : ℂ) ^ 3
    rw [← map_pow, ← map_mul]
    norm_num
  have hsixteenth :
      (algebraMap ℂ (Germ 2)) (1 / 16 : ℂ) =
        (algebraMap ℂ (Germ 2)) (1 / 4 : ℂ) ^ 2 := by
    rw [← map_pow]
    norm_num
  have hthreeTwoFiftySix :
      (algebraMap ℂ (Germ 2)) (3 / 256 : ℂ) =
        3 * (algebraMap ℂ (Germ 2)) (1 / 4 : ℂ) ^ 4 := by
    change (algebraMap ℂ (Germ 2)) (3 / 256 : ℂ) =
      (algebraMap ℂ (Germ 2)) (3 : ℂ) *
        (algebraMap ℂ (Germ 2)) (1 / 4 : ℂ) ^ 4
    rw [← map_pow, ← map_mul]
    norm_num
  have hhalfInv :
      (algebraMap ℂ (Germ 2)) (2 : ℂ)⁻¹ =
        2 * (algebraMap ℂ (Germ 2)) (4 : ℂ)⁻¹ := by
    simpa only [div_eq_mul_inv, one_mul] using hhalf
  have heighthInv :
      (algebraMap ℂ (Germ 2)) (8 : ℂ)⁻¹ =
        8 * (algebraMap ℂ (Germ 2)) (4 : ℂ)⁻¹ ^ 3 := by
    simpa only [div_eq_mul_inv, one_mul] using heighth
  have hsixteenthInv :
      (algebraMap ℂ (Germ 2)) (16 : ℂ)⁻¹ =
        (algebraMap ℂ (Germ 2)) (4 : ℂ)⁻¹ ^ 2 := by
    simpa only [div_eq_mul_inv, one_mul] using hsixteenth
  have hidentity := quartic_shift_identity
    (Germ.coordinate (0 : Fin 2))
    (Germ.planeCoefficientExtension a₃)
    (Germ.planeCoefficientExtension a₂)
    (Germ.planeCoefficientExtension a₁)
    (Germ.planeCoefficientExtension a₀)
    scalarFourth hfour
  refine ⟨e, ?_, ?_⟩
  · simp only [Germ.monicQuartic, map_add, map_mul, map_pow,
      heCoordinate]
    rw [hePlane a₃, hePlane a₂, hePlane a₁, hePlane a₀]
    simpa [shift, shiftedCoordinate, Germ.depressedQuarticQuadratic,
      Germ.depressedQuarticLinear, Germ.depressedQuarticConstant,
      scalarFourth, Algebra.smul_def, sub_eq_add_neg,
      hthreeEighths, hhalf, heighth, hsixteenth,
      hthreeTwoFiftySix, hhalfInv, heighthInv,
      hsixteenthInv] using hidentity
  · intro q
    exact heCoefficient q

end Germ

end OnLeConjecture.Analytic

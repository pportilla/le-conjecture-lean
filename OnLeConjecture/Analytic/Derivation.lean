/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Jet
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivatives of analytic germs

This file defines directional and coordinate derivatives of complex analytic
germs. It proves the linearity and product formulas and defines the Jacobian
of two plane germs.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- The derivative of a function germ in a fixed vector direction. -/
@[expose] noncomputable def directionalDerivativeFunctionGerm {n : ℕ}
    (v : Source n) (g : FunctionGerm n) : FunctionGerm n :=
  g.liftOn
    (fun f =>
      ((fun z : Source n => fderiv ℂ f z v) : FunctionGerm n))
    (fun f h hfh => by
      apply Filter.Germ.coe_eq.mpr
      exact (hfh.fderiv (𝕜 := ℂ)).mono fun z hz =>
        congrArg (fun L : Source n →L[ℂ] ℂ => L v) hz)

@[simp]
theorem directionalDerivativeFunctionGerm_ofFun {n : ℕ}
    (v : Source n) (f : Source n → ℂ) :
    directionalDerivativeFunctionGerm v (f : FunctionGerm n) =
      ((fun z : Source n => fderiv ℂ f z v) : FunctionGerm n) :=
  rfl

/-- Directional differentiation preserves analyticity. -/
theorem isAnalytic_directionalDerivativeFunctionGerm {n : ℕ}
    (v : Source n) {g : FunctionGerm n} (hg : IsAnalyticGerm g) :
    IsAnalyticGerm (directionalDerivativeFunctionGerm v g) := by
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      rw [isAnalyticGerm_ofFun] at hg
      rw [directionalDerivativeFunctionGerm_ofFun,
        isAnalyticGerm_ofFun]
      exact ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt
        (fderiv ℂ f 0)).comp hg.fderiv

/-- The directional derivative of an analytic germ. -/
@[expose] noncomputable def directionalDerivative {n : ℕ}
    (v : Source n) (g : Germ n) : Germ n :=
  ⟨directionalDerivativeFunctionGerm v g.1,
    isAnalytic_directionalDerivativeFunctionGerm v g.2⟩

@[simp]
theorem directionalDerivative_ofFunction {n : ℕ}
    (v : Source n) (f : Source n → ℂ) (hf : AnalyticAt ℂ f 0) :
    directionalDerivative v (Germ.ofFunction f hf) =
      Germ.ofFunction (fun z => fderiv ℂ f z v)
        (((ContinuousLinearMap.apply ℂ ℂ v).analyticAt
          (fderiv ℂ f 0)).comp hf.fderiv) :=
  rfl

/-- The standard coordinate vector. -/
@[expose] noncomputable def coordinateVector {n : ℕ} (i : Fin n) :
    Source n :=
  Pi.single i 1

@[simp]
theorem coordinateVector_apply {n : ℕ} (i j : Fin n) :
    coordinateVector i j = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [coordinateVector]
  · simp [coordinateVector, hij]

/-- Partial differentiation with respect to one coordinate. -/
@[expose] noncomputable def partialDerivative {n : ℕ}
    (i : Fin n) (g : Germ n) : Germ n :=
  directionalDerivative (coordinateVector i) g

/-- The derivative of the zero germ vanishes. -/
@[simp]
theorem directionalDerivative_zero {n : ℕ} (v : Source n) :
    directionalDerivative v (0 : Germ n) = 0 := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by simp

/-- Directional differentiation is additive. -/
theorem directionalDerivative_add {n : ℕ} (v : Source n)
    (g h : Germ n) :
    directionalDerivative v (g + h) =
      directionalDerivative v g + directionalDerivative v h := by
  rcases g with ⟨g, hg⟩
  rcases h with ⟨h, hh⟩
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      induction h using Filter.Germ.inductionOn with
      | _ q =>
          rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hg hh
          apply Subtype.ext
          apply Filter.Germ.coe_eq.mpr
          filter_upwards [hg.eventually_analyticAt,
            hh.eventually_analyticAt] with z hfz hqz
          have hadd :=
            fderiv_add hfz.differentiableAt hqz.differentiableAt
          exact congrArg (fun L : Source n →L[ℂ] ℂ => L v) hadd

/-- Directional differentiation satisfies the product formula. -/
theorem directionalDerivative_mul {n : ℕ} (v : Source n)
    (g h : Germ n) :
    directionalDerivative v (g * h) =
      directionalDerivative v g * h +
        g * directionalDerivative v h := by
  rcases g with ⟨g, hg⟩
  rcases h with ⟨h, hh⟩
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      induction h using Filter.Germ.inductionOn with
      | _ q =>
          rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hg hh
          apply Subtype.ext
          apply Filter.Germ.coe_eq.mpr
          filter_upwards [hg.eventually_analyticAt,
            hh.eventually_analyticAt] with z hfz hqz
          have hmul :=
            fderiv_mul hfz.differentiableAt hqz.differentiableAt
          have happly :=
            congrArg (fun L : Source n →L[ℂ] ℂ => L v) hmul
          change (fderiv ℂ (f * q) z) v =
            (fderiv ℂ f z) v * q z + f z * (fderiv ℂ q z) v
          calc
            (fderiv ℂ (f * q) z) v =
                f z * (fderiv ℂ q z) v +
                  q z * (fderiv ℂ f z) v := happly
            _ = (fderiv ℂ f z) v * q z +
                f z * (fderiv ℂ q z) v := by ring

/-- The derivative of a constant germ vanishes. -/
@[simp]
theorem directionalDerivative_const {n : ℕ} (v : Source n) (c : ℂ) :
    directionalDerivative v (Germ.constRingHom n c) = 0 := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by simp

/-- Directional differentiation is linear over the constants. -/
theorem directionalDerivative_smul {n : ℕ} (v : Source n)
    (c : ℂ) (g : Germ n) :
    directionalDerivative v (c • g) =
      c • directionalDerivative v g := by
  change directionalDerivative v (Germ.constRingHom n c * g) =
    Germ.constRingHom n c * directionalDerivative v g
  rw [directionalDerivative_mul, directionalDerivative_const]
  ring

/-- Directional differentiation as a complex linear map. -/
@[expose] noncomputable def directionalDerivativeLinearMap {n : ℕ}
    (v : Source n) : Germ n →ₗ[ℂ] Germ n where
  toFun := directionalDerivative v
  map_add' := directionalDerivative_add v
  map_smul' := directionalDerivative_smul v

@[simp]
theorem directionalDerivativeLinearMap_apply {n : ℕ}
    (v : Source n) (g : Germ n) :
    directionalDerivativeLinearMap v g = directionalDerivative v g :=
  rfl

/-- Directional differentiation as a derivation of the analytic local ring.
-/
@[expose] noncomputable def directionalDerivation {n : ℕ}
    (v : Source n) : Derivation ℂ (Germ n) (Germ n) :=
  Derivation.mk' (directionalDerivativeLinearMap v) fun g h => by
    change directionalDerivative v (g * h) =
      g * directionalDerivative v h + h * directionalDerivative v g
    rw [directionalDerivative_mul]
    ring

@[simp]
theorem directionalDerivation_apply {n : ℕ}
    (v : Source n) (g : Germ n) :
    directionalDerivation v g = directionalDerivative v g :=
  rfl

@[simp]
theorem partialDerivative_zero {n : ℕ} (i : Fin n) :
    partialDerivative i (0 : Germ n) = 0 :=
  directionalDerivative_zero _

theorem partialDerivative_add {n : ℕ} (i : Fin n) (g h : Germ n) :
    partialDerivative i (g + h) =
      partialDerivative i g + partialDerivative i h :=
  directionalDerivative_add _ _ _

theorem partialDerivative_mul {n : ℕ} (i : Fin n) (g h : Germ n) :
    partialDerivative i (g * h) =
      partialDerivative i g * h + g * partialDerivative i h :=
  directionalDerivative_mul _ _ _

theorem partialDerivative_smul {n : ℕ} (i : Fin n)
    (c : ℂ) (g : Germ n) :
    partialDerivative i (c • g) = c • partialDerivative i g :=
  directionalDerivative_smul _ _ _

theorem partialDerivative_neg {n : ℕ} (i : Fin n) (g : Germ n) :
    partialDerivative i (-g) = -partialDerivative i g := by
  have h := partialDerivative_smul i (-1 : ℂ) g
  simpa using h

theorem partialDerivative_sub {n : ℕ} (i : Fin n) (g h : Germ n) :
    partialDerivative i (g - h) =
      partialDerivative i g - partialDerivative i h := by
  rw [sub_eq_add_neg, partialDerivative_add, partialDerivative_neg,
    sub_eq_add_neg]

/-- Partial differentiation as a derivation. -/
@[expose] noncomputable def partialDerivation {n : ℕ}
    (i : Fin n) : Derivation ℂ (Germ n) (Germ n) :=
  directionalDerivation (coordinateVector i)

@[simp]
theorem partialDerivation_apply {n : ℕ} (i : Fin n) (g : Germ n) :
    partialDerivation i g = partialDerivative i g :=
  rfl

/-- The derivative of a power. -/
theorem partialDerivative_pow {n : ℕ} (i : Fin n)
    (g : Germ n) (k : ℕ) :
    partialDerivative i (g ^ k) =
      k • g ^ (k - 1) • partialDerivative i g := by
  exact (partialDerivation i).leibniz_pow g k

@[simp]
theorem partialDerivative_const {n : ℕ} (i : Fin n) (c : ℂ) :
    partialDerivative i (Germ.constRingHom n c) = 0 :=
  directionalDerivative_const _ _

/-- The directional derivative of a coordinate is the corresponding constant.
-/
theorem directionalDerivative_coordinate {n : ℕ}
    (v : Source n) (i : Fin n) :
    directionalDerivative v (Germ.coordinate i) =
      Germ.constRingHom n (v i) := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by
    change fderiv ℂ
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin n => ℂ) i) z v = v i
    rw [ContinuousLinearMap.fderiv]
    rfl

/-- Coordinate derivatives satisfy the Kronecker delta formula. -/
theorem partialDerivative_coordinate {n : ℕ} (i j : Fin n) :
    partialDerivative i (Germ.coordinate j) =
      Germ.constRingHom n (if i = j then 1 else 0) := by
  rw [partialDerivative, directionalDerivative_coordinate,
    coordinateVector_apply]

@[simp]
theorem partialDerivative_coordinate_same {n : ℕ} (i : Fin n) :
    partialDerivative i (Germ.coordinate i) = 1 := by
  rw [partialDerivative_coordinate, if_pos rfl]
  rfl

@[simp]
theorem partialDerivative_coordinate_ne {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) :
    partialDerivative i (Germ.coordinate j) = 0 := by
  rw [partialDerivative_coordinate, if_neg hij]
  rfl

/-- Evaluation at the origin of a directional derivative is the differential
at the origin applied to the same vector. -/
theorem valueRingHom_directionalDerivative {n : ℕ}
    (v : Source n) (g : Germ n) :
    Germ.valueRingHom n (directionalDerivative v g) =
      Germ.differential g v := by
  rcases g with ⟨g, hg⟩
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      rfl

/-- Evaluation of a partial derivative is the corresponding component of the
differential. -/
theorem valueRingHom_partialDerivative {n : ℕ}
    (i : Fin n) (g : Germ n) :
    Germ.valueRingHom n (partialDerivative i g) =
      Germ.differential g (coordinateVector i) :=
  valueRingHom_directionalDerivative _ _

/-- A scalar germ has zero differential exactly when all of its coordinate
derivatives vanish at the origin. -/
theorem differential_eq_zero_iff_partialDerivatives_vanish {n : ℕ}
    (g : Germ n) :
    Germ.differential g = 0 ↔
      ∀ i, Germ.valueRingHom n (partialDerivative i g) = 0 := by
  constructor
  · intro h i
    rw [valueRingHom_partialDerivative, h]
    rfl
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = ∑ i : Fin n, v i • coordinateVector i := by
      funext j
      classical
      simp [coordinateVector, Pi.single_apply]
    rw [hv, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_smul]
    have hi : Germ.differential g (coordinateVector i) = 0 := by
      simpa only [valueRingHom_partialDerivative] using h i
    rw [hi, smul_zero]

/-- A scalar germ has zero differential exactly when all of its partial
derivatives belong to the maximal ideal. -/
theorem differential_eq_zero_iff_partialDerivatives_mem_maximalIdeal
    {n : ℕ} (g : Germ n) :
    Germ.differential g = 0 ↔
      ∀ i, partialDerivative i g ∈ Germ.maximalIdeal n := by
  rw [differential_eq_zero_iff_partialDerivatives_vanish]
  constructor <;> intro h i
  · rw [Germ.mem_maximalIdeal_iff]
    exact h i
  · exact Germ.mem_maximalIdeal_iff.mp (h i)

/-- The Jacobian determinant of two plane analytic germs. -/
@[expose] noncomputable def jacobian (g h : Germ 2) : Germ 2 :=
  partialDerivative (0 : Fin 2) g * partialDerivative (1 : Fin 2) h -
    partialDerivative (1 : Fin 2) g * partialDerivative (0 : Fin 2) h

theorem jacobian_eq (g h : Germ 2) :
    jacobian g h =
      partialDerivative (0 : Fin 2) g *
          partialDerivative (1 : Fin 2) h -
        partialDerivative (1 : Fin 2) g *
          partialDerivative (0 : Fin 2) h :=
  rfl

theorem jacobian_swap (g h : Germ 2) :
    jacobian h g = -jacobian g h := by
  rw [jacobian_eq, jacobian_eq]
  ring

theorem jacobian_add_left (g h q : Germ 2) :
    jacobian (g + h) q = jacobian g q + jacobian h q := by
  simp only [jacobian_eq, partialDerivative_add]
  ring

theorem jacobian_add_right (g h q : Germ 2) :
    jacobian q (g + h) = jacobian q g + jacobian q h := by
  simp only [jacobian_eq, partialDerivative_add]
  ring

theorem jacobian_mul_left (g h q : Germ 2) :
    jacobian (g * h) q = g * jacobian h q + h * jacobian g q := by
  simp only [jacobian_eq, partialDerivative_mul]
  ring

theorem jacobian_mul_right (g h q : Germ 2) :
    jacobian q (g * h) = g * jacobian q h + h * jacobian q g := by
  simp only [jacobian_eq, partialDerivative_mul]
  ring

@[simp]
theorem jacobian_const_left (c : ℂ) (g : Germ 2) :
    jacobian (Germ.constRingHom 2 c) g = 0 := by
  simp only [jacobian_eq, partialDerivative_const]
  ring

@[simp]
theorem jacobian_const_right (g : Germ 2) (c : ℂ) :
    jacobian g (Germ.constRingHom 2 c) = 0 := by
  simp only [jacobian_eq, partialDerivative_const]
  ring

@[simp]
theorem jacobian_self (g : Germ 2) :
    jacobian g g = 0 := by
  rw [jacobian_eq]
  ring

/-- The Jacobian with the first coordinate is the negative second partial
derivative. -/
theorem jacobian_coordinate_zero_right (g : Germ 2) :
    jacobian g (Germ.coordinate (0 : Fin 2)) =
      -partialDerivative (1 : Fin 2) g := by
  rw [jacobian_eq, partialDerivative_coordinate_same,
    partialDerivative_coordinate_ne (by decide)]
  ring

/-- The Jacobian with the second coordinate is the first partial derivative.
-/
theorem jacobian_coordinate_one_right (g : Germ 2) :
    jacobian g (Germ.coordinate (1 : Fin 2)) =
      partialDerivative (0 : Fin 2) g := by
  rw [jacobian_eq, partialDerivative_coordinate_same,
    partialDerivative_coordinate_ne (by decide)]
  ring

/-- The Jacobian with the first coordinate on the left is the second partial
derivative. -/
theorem jacobian_coordinate_zero_left (g : Germ 2) :
    jacobian (Germ.coordinate (0 : Fin 2)) g =
      partialDerivative (1 : Fin 2) g := by
  rw [jacobian_swap, jacobian_coordinate_zero_right]
  ring

/-- The Jacobian with the second coordinate on the left is the negative first
partial derivative. -/
theorem jacobian_coordinate_one_left (g : Germ 2) :
    jacobian (Germ.coordinate (1 : Fin 2)) g =
      -partialDerivative (0 : Fin 2) g := by
  rw [jacobian_swap, jacobian_coordinate_one_right]

end Germ

end OnLeConjecture.Analytic

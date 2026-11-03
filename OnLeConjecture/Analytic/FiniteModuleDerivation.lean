/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Derivation
public import OnLeConjecture.Analytic.Coordinates
public import OnLeConjecture.Analytic.FiniteDimensionalNoetherian
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Derivations of analytic germs with finite module values

A complex derivation into a finite module over the analytic germ ring is
determined by its values on the source coordinates. Hadamard division shows
that a derivation vanishing on those coordinates takes values in every
maximal-ideal power. Krull intersection then makes it zero. This proves the
analytic chain rule without a separate continuity hypothesis on derivations.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace OnLeConjecture.Analytic.Germ

/-- A derivation vanishing on every coordinate takes every value in every
power of the maximal ideal times its target module. -/
theorem derivation_mem_pow_smul_of_coordinates_eq_zero
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (Germ n) M]
    [IsScalarTower ℂ (Germ n) M]
    (D : Derivation ℂ (Germ n) M) (hD : ∀ i, D (coordinate i) = 0)
    (k : ℕ) (f : Germ n) :
    D f ∈ maximalIdeal n ^ k • (⊤ : Submodule (Germ n) M) := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    have hf : f - constRingHom n (valueRingHom n f) ∈ maximalIdeal n := by
      rw [mem_maximalIdeal_iff]
      simp
    obtain ⟨a, ha⟩ := exists_eq_sum_coordinate_mul hf
    have hconst : D (constRingHom n (valueRingHom n f)) = 0 :=
      D.map_algebraMap _
    have heq := congrArg D ha
    simp only [map_sub, hconst, sub_zero, map_sum, D.leibniz, hD, smul_zero,
      add_zero] at heq
    rw [heq, pow_succ', mul_smul]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (coordinate_mem_maximalIdeal i) (ih (a i))

/-- A complex derivation with finite analytic module values vanishes when
it vanishes on the source coordinates. -/
theorem derivation_eq_zero_of_coordinates_eq_zero
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (Germ n) M]
    [IsScalarTower ℂ (Germ n) M] [Module.Finite (Germ n) M]
    (D : Derivation ℂ (Germ n) M) (hD : ∀ i, D (coordinate i) = 0) : D = 0 := by
  let _ := isNoetherianRing_all n
  ext f
  apply (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal (Germ n)) M).haus
  intro k
  rw [SModEq.zero, ← maximalIdeal_eq_isLocalRing]
  exact derivation_mem_pow_smul_of_coordinates_eq_zero D hD k f

/-- The analytic chain rule for any complex derivation into a finite
module over the source analytic ring. -/
theorem derivation_eq_sum_partialDerivatives_smul
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (Germ n) M]
    [IsScalarTower ℂ (Germ n) M] [Module.Finite (Germ n) M]
    (D : Derivation ℂ (Germ n) M) (f : Germ n) :
    D f = ∑ i : Fin n, partialDerivative i f • D (coordinate i) := by
  classical
  let E : Derivation ℂ (Germ n) M :=
    ∑ i : Fin n, (LinearMap.toSpanSingleton (Germ n) M (D (coordinate i))).compDer
      (partialDerivation i)
  have hE (h : Germ n) : E h = ∑ i : Fin n, partialDerivative i h • D (coordinate i) := by
    change Derivation.coeFnAddMonoidHom
      (∑ i : Fin n, (LinearMap.toSpanSingleton (Germ n) M (D (coordinate i))).compDer
        (partialDerivation i)) h = _
    rw [map_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have hcoord (j : Fin n) : (D - E) (coordinate j) = 0 := by
    simp [hE, partialDerivative_coordinate]
  have heq := derivation_eq_zero_of_coordinates_eq_zero (D - E) hcoord
  have h := congrArg (fun δ : Derivation ℂ (Germ n) M => δ f) heq
  simpa only [Derivation.sub_apply, Derivation.zero_apply, sub_eq_zero, hE] using h

end OnLeConjecture.Analytic.Germ

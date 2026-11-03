/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentTensorLowerBound
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Balanced finite Laurent tensor products

The tensor differential is the sum of the single-factor differentials.
The product of the previously constructed Laurent cocycles is defined using
Mathlib's finite tensor universal property, including the empty tensor product.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti PiTensorProduct CategoryTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K] {n : ι → ℕ} (G : ∀ i, GridDiagram (n i))

/-- The finite tensor product balanced over the Laurent ring. -/
abbrev LaurentFiniteTensor := PiTensorProduct (LaurentPolynomial K) (fun i => LaurentChain K (n i))

/-- Apply the grid differential to one tensor factor. -/
def laurentFiniteFactorDifferential (i : ι) :
    LaurentFiniteTensor (K := K) (n := n) →ₗ[LaurentPolynomial K]
      LaurentFiniteTensor (K := K) (n := n) :=
  PiTensorProduct.map fun j => if i = j then laurentDifferential (G j) K else LinearMap.id

omit [Fintype ι] in
/-- The one-factor map on a pure tensor is a dependent coordinate update. -/
theorem laurentFiniteFactorDifferential_tprod (i : ι) (x : ∀ j, LaurentChain K (n j)) :
    laurentFiniteFactorDifferential G i (tprod (LaurentPolynomial K) x) =
      tprod (LaurentPolynomial K) (Function.update x i (laurentDifferential (G i) K (x i))) := by
  rw [laurentFiniteFactorDifferential, PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

omit [Fintype ι] in
/-- Differentiating distinct factors commutes, including the tautological equal-factor case. -/
theorem laurentFiniteFactorDifferential_comm (i j : ι) :
    (laurentFiniteFactorDifferential (K := K) G i).comp
        (laurentFiniteFactorDifferential G j) =
      (laurentFiniteFactorDifferential (K := K) G j).comp
        (laurentFiniteFactorDifferential G i) := by
  rw [laurentFiniteFactorDifferential, laurentFiniteFactorDifferential,
    ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext k
  by_cases hi : i = k <;> by_cases hj : j = k <;> simp [hi, hj]

/-- The sum of all one-factor differentials. -/
def laurentFiniteDifferential :
    LaurentFiniteTensor (K := K) (n := n) →ₗ[LaurentPolynomial K]
      LaurentFiniteTensor (K := K) (n := n) := ∑ i, laurentFiniteFactorDifferential G i

@[simp]
theorem laurentFiniteDifferential_tprod (x : ∀ i, LaurentChain K (n i)) :
    laurentFiniteDifferential G (tprod (LaurentPolynomial K) x) =
      ∑ i, tprod (LaurentPolynomial K)
        (Function.update x i (laurentDifferential (G i) K (x i))) := by
  simp [laurentFiniteDifferential, laurentFiniteFactorDifferential_tprod]

/-- The product of finitely many Laurent-linear functionals. -/
def laurentFinitePairing
    (Λ : ∀ i, LaurentChain K (n i) →ₗ[LaurentPolynomial K] LaurentPolynomial K) :
    LaurentFiniteTensor (K := K) (n := n) →ₗ[LaurentPolynomial K] LaurentPolynomial K :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra (LaurentPolynomial K) ι (LaurentPolynomial K)).compLinearMap Λ)

omit [DecidableEq ι] in
@[simp]
theorem laurentFinitePairing_tprod
    (Λ : ∀ i, LaurentChain K (n i) →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (x : ∀ i, LaurentChain K (n i)) :
    laurentFinitePairing Λ (tprod (LaurentPolynomial K) x) = ∏ i, Λ i (x i) := by
  simp [laurentFinitePairing]

/-- The finite product cocycle annihilates the tensor differential. -/
theorem laurentFinitePairing_differential
    (Λ : ∀ i, LaurentChain K (n i) →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (hΛ : ∀ i x, Λ i (laurentDifferential (G i) K x) = 0)
    (z : LaurentFiniteTensor (K := K) (n := n)) :
    laurentFinitePairing Λ (laurentFiniteDifferential G z) = 0 := by
  have h : (laurentFinitePairing Λ).comp (laurentFiniteDifferential G) = 0 := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      laurentFiniteDifferential_tprod, map_sum, laurentFinitePairing_tprod, LinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro i hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hΛ])
  exact LinearMap.congr_fun h z

variable [CharP K 2]

omit [Fintype ι] in
/-- Each one-factor differential squares to zero. -/
theorem laurentFiniteFactorDifferential_sq (i : ι) :
    (laurentFiniteFactorDifferential (K := K) G i).comp
        (laurentFiniteFactorDifferential G i) = 0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    laurentFiniteFactorDifferential_tprod, LinearMap.zero_apply, Function.update_self,
    laurentDifferential_sq_eq_zero, Function.update_idem]
  exact (tprod (LaurentPolynomial K)).map_update_zero x i

/-- The actual finite tensor differential squares to zero in characteristic two. -/
theorem laurentFiniteDifferential_sq_eq_zero (z : LaurentFiniteTensor (K := K) (n := n)) :
    laurentFiniteDifferential G (laurentFiniteDifferential G z) = 0 := by
  have hsum : ∀ s : Finset ι,
      (∑ i ∈ s, laurentFiniteFactorDifferential (K := K) G i).comp
        (∑ i ∈ s, laurentFiniteFactorDifferential G i) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, LinearMap.add_comp, LinearMap.comp_add,
        LinearMap.comp_add, laurentFiniteFactorDifferential_sq, ih, zero_add, add_zero]
      have hcomm : (laurentFiniteFactorDifferential (K := K) G i).comp
          (∑ j ∈ s, laurentFiniteFactorDifferential G j) =
          (∑ j ∈ s, laurentFiniteFactorDifferential G j).comp
            (laurentFiniteFactorDifferential G i) := by
        apply LinearMap.ext
        intro z
        simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
        exact Finset.sum_congr rfl fun j _ =>
          LinearMap.congr_fun (laurentFiniteFactorDifferential_comm G i j) z
      rw [hcomm]
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      rw [← two_smul K, htwo, zero_smul]
  exact LinearMap.congr_fun (hsum Finset.univ) z

end OnLeConjecture.KnotFloer.GridFull

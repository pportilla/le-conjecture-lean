/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurentBifiltration
public import OnLeConjecture.KnotFloer.GridFullLaurentMaslov

/-!
# Laurent matrix bounds and homogeneous filtered maps

Coefficient bounds imply degree and filtration bounds for arbitrary Laurent-linear maps.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {R : Type*} [CommRing R]

/-- A Laurent-linear map acts by multiplying its matrix coefficients. -/
theorem laurentMap_apply_apply {ι κ : Type*}
    (f : (ι →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R] (κ →₀ LaurentPolynomial R))
    (c : ι →₀ LaurentPolynomial R) (y : κ) :
    f c y = c.sum (fun x a => a * f (single x 1) y) := by
  classical
  have hs (x : ι) (a : LaurentPolynomial R) : f (single x a) = a • f (single x 1) := by
    rw [← Finsupp.smul_single_one, map_smul]
  conv_lhs => rw [← Finsupp.sum_single c, map_finsuppSum]
  simp only [Finsupp.sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [hs, Finsupp.smul_apply, smul_eq_mul]

/-- A nonzero output exponent comes from an input exponent and a matrix coefficient. -/
theorem exists_support_laurentMap {ι κ : Type*}
    (f : (ι →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R] (κ →₀ LaurentPolynomial R))
    (c : ι →₀ LaurentPolynomial R) {y : κ} {k : ℤ}
    (hk : k ∈ (f c y).coeff.support) :
    ∃ x : ι, ∃ j ∈ (c x).coeff.support, ∃ d ∈ (f (single x 1) y).coeff.support, k = j + d := by
  classical
  rw [laurentMap_apply_apply, Finsupp.sum, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨j, hj, d, hd, heq⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hx)
  exact ⟨x, j, hj, d, hd, heq.symm⟩

/-- Matrix degrees determine the degree of a Laurent-linear grid map. -/
theorem laurentMap_mem_maslovPiece {n p : ℕ} (G : GridDiagram n) (H : GridDiagram p)
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R p) (q : ℤ)
    (hf : ∀ x y k, k ∈ (f (single x 1) y).coeff.support →
      H.maslovOℤ y - 2 * k = G.maslovOℤ x + q)
    {m : ℤ} {c : LaurentChain R n} (hc : c ∈ laurentMaslovPiece G R m) :
    f c ∈ laurentMaslovPiece H R (m + q) := by
  intro y k hk
  obtain ⟨x, j, hj, d, hd, rfl⟩ := exists_support_laurentMap f c hk
  have hm := hf x y d hd
  have hx := hc x j hj
  change G.maslovOℤ x - 2 * j = m at hx
  change H.maslovOℤ y - 2 * (j + d) = m + q
  omega

/-- Matrix coordinate bounds determine the filtration of a Laurent-linear grid map. -/
theorem laurentMap_mem_bifiltrationLevel {n p : ℕ} (G : GridDiagram n) (H : GridDiagram p)
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R p) (a : ℚ)
    (hf : ∀ x y k, k ∈ (f (single x 1) y).coeff.support →
      -(k : ℚ) ≤ 0 ∧ H.alexander y - k ≤ G.alexander x + a)
    {u v : ℝ} {c : LaurentChain R n} (hc : c ∈ laurentBifiltrationLevel G R u v) :
    f c ∈ laurentBifiltrationLevel H R u (v + a) := by
  intro y k hk
  obtain ⟨x, j, hj, d, hd, rfl⟩ := exists_support_laurentMap f c hk
  obtain ⟨hfirst, hsecond⟩ := hf x y d hd
  have hfirst' : -(d : ℝ) ≤ 0 := by exact_mod_cast hfirst
  have hsecond' : (H.alexander y : ℝ) - d ≤ (G.alexander x : ℝ) + a := by
    exact_mod_cast hsecond
  obtain ⟨hx, hy⟩ := hc x j hj
  push_cast
  constructor <;> linarith

end OnLeConjecture.KnotFloer.GridFull

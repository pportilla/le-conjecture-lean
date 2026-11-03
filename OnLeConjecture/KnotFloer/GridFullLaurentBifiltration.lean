/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurent
public import OnLeConjecture.KnotFloer.GridFullBifiltration

/-!
# The two-coordinate filtration of full Laurent grid chains

A Laurent monomial state `T^k x` has coordinates `(-k, A(x)-k)`, with `k` any integer.
Levels are submodules over the base coefficient ring. Multiplication by `T` decreases both
coordinates and multiplication by its inverse increases both coordinates.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R]

/-- Laurent grid chains satisfying both coordinate bounds at each nonzero coefficient. -/
noncomputable def laurentBifiltrationLevel (a b : ℝ) : Submodule R (LaurentChain R n) where
  carrier := {c | ∀ x k, k ∈ (c x).coeff.support →
    -(k : ℝ) ≤ a ∧ (G.alexander x : ℝ) - k ≤ b}
  zero_mem' := by simp
  add_mem' := by
    classical
    intro c d hc hd x k hk
    have h : k ∈ (c x).coeff.support ∪ (d x).coeff.support :=
      Finsupp.support_add (by simpa only [Finsupp.add_apply, AddMonoidAlgebra.coeff_add] using hk)
    exact (Finset.mem_union.mp h).elim (hc x k) (hd x k)
  smul_mem' := by
    intro a c hc x k hk
    apply hc x k
    exact Finsupp.support_smul (by
      simpa only [Finsupp.smul_apply, AddMonoidAlgebra.coeff_smul] using hk)

@[simp]
theorem mem_laurentBifiltrationLevel_iff (a b : ℝ) (c : LaurentChain R n) :
    c ∈ laurentBifiltrationLevel G R a b ↔ ∀ x k, k ∈ (c x).coeff.support →
      -(k : ℝ) ≤ a ∧ (G.alexander x : ℝ) - k ≤ b := Iff.rfl

/-- Increasing both bounds enlarges the Laurent filtration. -/
theorem laurentBifiltrationLevel_mono {a b a' b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    laurentBifiltrationLevel G R a b ≤ laurentBifiltrationLevel G R a' b' :=
  fun _ hc x k hk => ⟨(hc x k hk).1.trans ha, (hc x k hk).2.trans hb⟩

/-- Every full Laurent rectangle term decreases its first coordinate by its O count
and its second coordinate by its X count. -/
theorem laurentRectangle_coordinates_le {x y : GridState n}
    (r : GridRectangleBetween x y) (k : ℤ) :
    -((k + ((G.OColumns r.toGridRectangle).card : ℤ) : ℤ) : ℝ) ≤ -(k : ℝ) ∧
      (G.alexander y : ℝ) - (k + ((G.OColumns r.toGridRectangle).card : ℤ) : ℤ) ≤
        (G.alexander x : ℝ) - k := by
  have h := G.alexander_sub_alexander_eq_card_sub_card r
  rw [← G.card_OColumns r.toGridRectangle] at h
  have hreal : (G.alexander x : ℝ) - (G.alexander y : ℝ) =
      ((G.XSet ∩ r.toGridRectangle.coveredSquares).card : ℝ) -
        (G.OColumns r.toGridRectangle).card := by exact_mod_cast h
  have hO := Nat.cast_nonneg (α := ℝ) (G.OColumns r.toGridRectangle).card
  have hX := Nat.cast_nonneg (α := ℝ) (G.XSet ∩ r.toGridRectangle.coveredSquares).card
  push_cast
  constructor <;> linarith

/-- The actual Laurent differential preserves both coordinate bounds. -/
theorem laurentDifferential_mem_bifiltrationLevel (a b : ℝ) (c : LaurentChain R n)
    (hc : c ∈ laurentBifiltrationLevel G R a b) :
    laurentDifferential G R c ∈ laurentBifiltrationLevel G R a b := by
  intro y k hk
  obtain ⟨x, j, hj, r, _, rfl⟩ :=
    exists_rectangle_of_mem_support_laurentDifferential G R c hk
  have hb := hc x j hj
  have hr := laurentRectangle_coordinates_le G r j
  exact ⟨hr.1.trans hb.1, hr.2.trans hb.2⟩

/-- Multiplication by any Laurent power translates both filtration coordinates by
minus that exponent. Negative powers therefore raise the filtration. -/
theorem T_smul_mem_laurentBifiltrationLevel (j : ℤ) {a b : ℝ} (c : LaurentChain R n)
    (hc : c ∈ laurentBifiltrationLevel G R a b) :
    (LaurentPolynomial.T j : LaurentPolynomial R) • c ∈
      laurentBifiltrationLevel G R (a - j) (b - j) := by
  classical
  intro x k hk
  change k ∈ (LaurentPolynomial.T j * c x).coeff.support at hk
  have hk' := AddMonoidAlgebra.support_coeff_single_mul_subset (c x) (1 : R) j hk
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk'
  obtain ⟨ha, hb⟩ := hc x l hl
  push_cast
  constructor <;> linarith

end OnLeConjecture.KnotFloer.GridFull

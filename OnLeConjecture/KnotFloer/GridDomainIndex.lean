/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridDomainBasic
import Mathlib.Tactic

/-!
# Index identities for integral domains on a toroidal grid

This file proves the index identities of the written proof for integral domains on the
`k × k` toroidal grid, stated for four times the index (`GridDomain.index4`).

* `GridDomain.index4_add`: the index is additive under concatenation of domains. The proof is
  the symmetric identity `GridDomain.sum_boundary_mul_cornerSum_comm`, obtained by cyclic
  reindexing.
* `GridRectangleBetween.index4_domain`: an empty rectangle has index one.
* `GridDomain.exists_eq_add_of_boundary_eq_zero` and `GridDomain.index4_periodic`: a domain
  with zero mixed difference has the form `a c + b r`, and its index between any two states is
  `2 ∑ a + 2 ∑ b`.
* `GridDomain.four_le_index4`: a nonnegative domain between distinct states has index at
  least one.
* `GridDomain.exists_rectangle_of_index4_eq_four`: a nonnegative domain of index one between
  distinct states is the domain of an empty rectangle.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
open scoped BigOperators

variable {k : ℕ} [NeZero k]

/-- Crossing `c - 1 → c` changes membership in `[a, b)_cyc` only at the endpoints. -/
theorem sub_one_mem_cIco_iff {a b c : Fin k} (hca : c ≠ a) (hcb : c ≠ b) :
    c - 1 ∈ Grid.cIco a b ↔ c ∈ Grid.cIco a b := by
  have h := ite_mem_cIco_sub_one a b c
  rw [if_neg hca, if_neg hcb] at h
  by_cases h1 : c - 1 ∈ Grid.cIco a b <;> by_cases h2 : c ∈ Grid.cIco a b <;>
    simp only [h1, h2, if_true, if_false] at h <;> simp_all

namespace GridDomain

variable {D E : GridDomain k} {u v w : GridState k}

/-! ### Pairings and cyclic reindexing -/

omit [NeZero k] in
/-- Pairing with the indicator of a grid state evaluates at its points. -/
theorem sum_indicator_mul (u : GridState k) (X : Fin k → Fin k → ℤ) :
    ∑ c, ∑ r, gridStateIndicator u c r * X c r = ∑ c, X c (u c) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [gridStateIndicator]

/-- A sum of column differences over the torus vanishes. -/
theorem sum_sum_sub_col (F : Fin k → Fin k → ℤ) :
    ∑ c, ∑ r, (F c r - F (c - 1) r) = 0 := by
  simp only [Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  exact (sum_comp_sub_one (fun c => ∑ r, F c r)).symm

/-- A sum of row differences over the torus vanishes. -/
theorem sum_sum_sub_row (F : Fin k → Fin k → ℤ) :
    ∑ c, ∑ r, (F c r - F c (r - 1)) = 0 := by
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact (sum_comp_sub_one (F c)).symm

/-- The symmetric identity `∑ ∂D · A(E) = ∑ ∂E · A(D)`, written with corner sums. -/
theorem sum_boundary_mul_cornerSum_comm (D E : GridDomain k) :
    ∑ c, ∑ r, D.boundary c r * E.cornerSum c r =
      ∑ c, ∑ r, E.boundary c r * D.cornerSum c r := by
  rw [← sub_eq_zero]
  have key : ∀ c r, D.boundary c r * E.cornerSum c r - E.boundary c r * D.cornerSum c r =
      2 * (D c r * E (c - 1) r - D c (r - 1) * E (c - 1) (r - 1)) +
        2 * (D c r * E c (r - 1) - D (c - 1) r * E (c - 1) (r - 1)) -
        2 * (D c (r - 1) * E c r - D (c - 1) (r - 1) * E (c - 1) r) -
        2 * (D (c - 1) r * E c r - D (c - 1) (r - 1) * E c (r - 1)) := by
    intro c r
    simp only [boundary, cornerSum]
    ring
  have h1 := sum_sum_sub_row fun c r => D c r * E (c - 1) r
  have h2 := sum_sum_sub_col fun c r => D c r * E c (r - 1)
  have h3 := sum_sum_sub_col fun c r => D c (r - 1) * E c r
  have h4 := sum_sum_sub_row fun c r => D (c - 1) r * E c r
  have hsum : ∑ c, ∑ r, (D.boundary c r * E.cornerSum c r -
      E.boundary c r * D.cornerSum c r) = 0 := by
    simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_sub_distrib] at h1 h2 h3 h4
    linear_combination 2 * h1 + 2 * h2 - 2 * h3 - 2 * h4
  simp only [Finset.sum_sub_distrib] at hsum
  exact hsum

/-! ### Linearity of the index for fixed endpoints -/

theorem index4_eq_sum (D : GridDomain k) (u v : GridState k) :
    D.index4 u v = ∑ c, D.cornerSum c (u c) + ∑ c, D.cornerSum c (v c) :=
  Finset.sum_add_distrib

theorem index4_comm (D : GridDomain k) (u v : GridState k) : D.index4 u v = D.index4 v u := by
  simp only [index4, add_comm]

@[simp]
theorem index4_zero (u v : GridState k) : (0 : GridDomain k).index4 u v = 0 := by
  simp [index4, cornerSum]

/-- The index is additive in the domain for fixed endpoint states. -/
theorem index4_linear_add (D E : GridDomain k) (u v : GridState k) :
    (D + E).index4 u v = D.index4 u v + E.index4 u v := by
  simp only [index4, cornerSum_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- The index of the negative domain for fixed endpoint states. -/
theorem index4_neg (D : GridDomain k) (u v : GridState k) :
    (-D).index4 u v = -D.index4 u v := by
  simp only [index4, cornerSum_neg, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- The index is subtractive in the domain for fixed endpoint states. -/
theorem index4_linear_sub (D E : GridDomain k) (u v : GridState k) :
    (D - E).index4 u v = D.index4 u v - E.index4 u v := by
  rw [sub_eq_add_neg, index4_linear_add, index4_neg, sub_eq_add_neg]

/-- The difference of the corner sums at two endpoint states is a pairing with a boundary. -/
theorem sum_cornerSum_sub_sum_cornerSum (hD : D.IsFrom u v) (E : GridDomain k) :
    ∑ c, E.cornerSum c (u c) - ∑ c, E.cornerSum c (v c) =
      ∑ c, ∑ r, D.boundary c r * E.cornerSum c r := by
  have hD' : ∀ c r, D.boundary c r = gridStateIndicator u c r - gridStateIndicator v c r := hD
  simp only [hD', sub_mul, Finset.sum_sub_distrib, sum_indicator_mul]

/-! ### Additivity under concatenation -/

/-- Additivity of the index under concatenation of domains. -/
theorem index4_add (hD : D.IsFrom u v) (hE : E.IsFrom v w) :
    (D + E).index4 u w = D.index4 u v + E.index4 v w := by
  rw [index4_linear_add, index4_eq_sum, index4_eq_sum, index4_eq_sum, index4_eq_sum]
  have h1 := sum_cornerSum_sub_sum_cornerSum hD E
  have h2 := sum_cornerSum_sub_sum_cornerSum hE D
  have h3 := sum_boundary_mul_cornerSum_comm D E
  linarith

/-- The index of a difference of domains with a common terminal state. -/
theorem index4_sub (hD : D.IsFrom u v) (hE : E.IsFrom w v) :
    (D - E).index4 u w = D.index4 u v - E.index4 w v := by
  have h := index4_add (hD.sub hE) hE
  rw [sub_add_cancel] at h
  linarith

/-! ### Periodic domains -/

/-- A domain with zero mixed difference is a sum of a column function and a row function. -/
theorem exists_eq_add_of_boundary_eq_zero (h : ∀ c r, D.boundary c r = 0) :
    ∃ a b : Fin k → ℤ, ∀ c r, D c r = a c + b r := by
  refine ⟨fun c => D c 0, fun r => D 0 r - D 0 0, fun c r => ?_⟩
  revert c
  refine cyclic_induction (P := fun r => ∀ c, D c r = D c 0 + (D 0 r - D 0 0)) 0 ?_ ?_ r
  · intro c
    ring
  · intro r hr c
    refine cyclic_induction (P := fun c => D c r = D c 0 + (D 0 r - D 0 0)) 0 ?_ ?_ c
    · ring
    · intro c hc
      have hb := h c r
      simp only [boundary] at hb
      have h1 := hr c
      have h2 := hr (c - 1)
      linarith

/-- Four times the corner sums of a periodic domain along a grid state. -/
theorem sum_cornerSum_periodic (a b : Fin k → ℤ) (w : GridState k) :
    ∑ c, GridDomain.cornerSum (fun c r => a c + b r) c (w c) =
      4 * (∑ c, a c + ∑ r, b r) := by
  have e1 : ∑ c, a (c - 1) = ∑ c, a c := sum_comp_sub_one a
  have e2 : ∑ c, b (w c) = ∑ r, b r := Equiv.sum_comp w.toPerm b
  have e3 : ∑ c, b (w c - 1) = ∑ r, b r :=
    (Equiv.sum_comp w.toPerm fun r => b (r - 1)).trans (sum_comp_sub_one b)
  simp only [cornerSum]
  calc ∑ c, (a c + b (w c) + (a (c - 1) + b (w c - 1)) + (a (c - 1) + b (w c)) +
          (a c + b (w c - 1)))
        = 2 * ∑ c, a c + 2 * ∑ c, a (c - 1) + 2 * ∑ c, b (w c) +
            2 * ∑ c, b (w c - 1) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ = 4 * (∑ c, a c + ∑ r, b r) := by
          rw [e1, e2, e3]
          ring

/-- The index of a periodic domain between any two states. -/
theorem index4_periodic (a b : Fin k → ℤ) (u v : GridState k) :
    GridDomain.index4 (fun c r => a c + b r) u v = 8 * (∑ c, a c + ∑ r, b r) := by
  rw [index4_eq_sum, sum_cornerSum_periodic, sum_cornerSum_periodic]
  ring

/-- The index of a periodic domain between equal endpoint states. -/
theorem index4_add_periodic (a b : Fin k → ℤ) (u : GridState k) :
    GridDomain.index4 (fun c r => a c + b r) u u = 8 * (∑ c, a c + ∑ r, b r) :=
  index4_periodic a b u u

/-- The index of a domain from a state to itself is divisible by eight. -/
theorem eight_dvd_index4_self (h : D.IsFrom u u) : 8 ∣ D.index4 u u := by
  obtain ⟨a, b, hab⟩ :=
    exists_eq_add_of_boundary_eq_zero (isFrom_self_iff_boundary_eq_zero.mp h)
  have hD : D = fun c r => a c + b r := funext fun c => funext fun r => hab c r
  rw [hD, index4_add_periodic]
  exact Dvd.intro _ rfl

/-- The column annulus has index two. -/
theorem index4_column (i : Fin k) (u : GridState k) : (column i).index4 u u = 8 := by
  have h : column i = fun c r =>
      (fun c => if c = i then (1 : ℤ) else 0) c + (fun _ => (0 : ℤ)) r := by
    funext c r
    simp [column]
  rw [h, index4_add_periodic]
  simp

/-- The row annulus has index two. -/
theorem index4_row (j : Fin k) (u : GridState k) : (row j).index4 u u = 8 := by
  have h : row j = fun c r =>
      (fun _ => (0 : ℤ)) c + (fun r => if r = j then (1 : ℤ) else 0) r := by
    funext c r
    simp [row]
  rw [h, index4_add_periodic]
  simp

end GridDomain

/-! ### Rectangle domains -/

end OnLeConjecture.KnotFloer.GridFull

namespace TauCeti.GridRectangleBetween
open OnLeConjecture.KnotFloer.GridFull

variable {k : ℕ} [NeZero k] {x y : GridState k}

/-- The corner sum of a rectangle domain is a product of two endpoint counts. -/
theorem domain_cornerSum (R : GridRectangleBetween x y) (c r : Fin k) :
    R.domain.cornerSum c r =
      (2 * (if c ∈ Grid.cIco R.left R.right then 1 else 0) - (if c = R.left then 1 else 0) +
          (if c = R.right then 1 else 0)) *
        (2 * (if r ∈ Grid.cIco (x R.left) (x R.right) then 1 else 0) -
          (if r = x R.left then 1 else 0) + (if r = x R.right then 1 else 0)) := by
  simp only [GridDomain.cornerSum, domain_apply, ite_and_one_zero]
  rw [ite_mem_cIco_sub_one R.left R.right c,
    ite_mem_cIco_sub_one (x R.left) (x R.right) r]
  ring

/-- An empty rectangle has index one. -/
theorem index4_domain (R : GridRectangleBetween x y) (h : R.IsEmpty) :
    R.domain.index4 x y = 4 := by
  have hab := R.left_ne_right
  have hxab : x R.left ≠ x R.right := fun h => hab (x.toPerm.injective h)
  rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo] at h
  unfold GridDomain.index4
  rw [Fintype.sum_eq_add R.left R.right hab]
  · have hA := Grid.left_mem_cIco hab
    have hB := Grid.right_notMem_cIco R.left R.right
    have hxA := Grid.left_mem_cIco hxab
    have hxB := Grid.right_notMem_cIco (x R.left) (x R.right)
    simp only [domain_cornerSum, R.map_left, R.map_right, hA, hB, hxA, hxB, hab, Ne.symm hab,
      hxab, Ne.symm hxab, ↓reduceIte]
    norm_num
  · rintro c ⟨hca, hcb⟩
    rw [R.map_of_ne c hca hcb]
    have hxca : x c ≠ x R.left := fun h' => hca (x.toPerm.injective h')
    have hxcb : x c ≠ x R.right := fun h' => hcb (x.toPerm.injective h')
    simp only [domain_cornerSum, if_neg hca, if_neg hcb, if_neg hxca, if_neg hxcb]
    by_cases hc : c ∈ Grid.cIco R.left R.right
    · have hc' := Grid.mem_cIoo_of_mem_cIco hc hca
      have hxc : x c ∉ Grid.cIco (x R.left) (x R.right) := by
        intro hxc
        exact h c hc' (Grid.mem_cIoo_of_mem_cIco hxc hxca)
      simp [hc, hxc]
    · simp [hc]

omit [NeZero k] in
/-- A rectangle whose domain vanishes at every source point between its sides is empty. -/
theorem isEmpty_of_domain_apply_eq_zero (R : GridRectangleBetween x y)
    (hzero : ∀ c, c ≠ R.left → c ≠ R.right → R.domain c (x c) = 0) : R.IsEmpty := by
  rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
  intro c hc hxc
  have h0 := hzero c (Grid.ne_left_of_mem_cIoo hc) (Grid.ne_right_of_mem_cIoo hc)
  rw [domain_apply, if_pos ⟨Grid.cIoo_subset_cIco _ _ hc, Grid.cIoo_subset_cIco _ _ hxc⟩] at h0
  exact one_ne_zero h0

end TauCeti.GridRectangleBetween

namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti

variable {k : ℕ} [NeZero k]

namespace GridDomain

variable {D : GridDomain k} {u v : GridState k}

/-! ### Nonnegative domains -/

theorem cornerSum_nonneg (hpos : ∀ c r, 0 ≤ D c r) (c r : Fin k) : 0 ≤ D.cornerSum c r := by
  have h1 := hpos c r
  have h2 := hpos (c - 1) (r - 1)
  have h3 := hpos (c - 1) r
  have h4 := hpos c (r - 1)
  simp only [cornerSum]
  omega

/-- A nonnegative domain has positive corner sum at every vertex of nonzero mixed difference. -/
theorem one_le_cornerSum (hpos : ∀ c r, 0 ≤ D c r) {c r : Fin k}
    (h : D.boundary c r ≠ 0) : 1 ≤ D.cornerSum c r := by
  have h1 := hpos c r
  have h2 := hpos (c - 1) (r - 1)
  have h3 := hpos (c - 1) r
  have h4 := hpos c (r - 1)
  simp only [cornerSum, boundary] at h ⊢
  omega

/-- A nonnegative domain has zero multiplicity on the four squares at a vertex of corner sum
zero. -/
theorem eq_zero_of_cornerSum_eq_zero (hpos : ∀ c r, 0 ≤ D c r) {c r : Fin k}
    (h : D.cornerSum c r = 0) :
    D c r = 0 ∧ D (c - 1) (r - 1) = 0 ∧ D (c - 1) r = 0 ∧ D c (r - 1) = 0 := by
  have h1 := hpos c r
  have h2 := hpos (c - 1) (r - 1)
  have h3 := hpos (c - 1) r
  have h4 := hpos c (r - 1)
  simp only [cornerSum] at h
  omega

theorem boundary_source (hD : D.IsFrom u v) {c : Fin k} (hc : u c ≠ v c) :
    D.boundary c (u c) = 1 := by
  rw [hD]
  simp [gridStateIndicator, Ne.symm hc]

theorem boundary_target (hD : D.IsFrom u v) {c : Fin k} (hc : u c ≠ v c) :
    D.boundary c (v c) = -1 := by
  rw [hD]
  simp [gridStateIndicator, hc]

omit [NeZero k] in
/-- Two distinct grid states differ in two distinct columns `A` and `B` with `u B = v A`. -/
theorem exists_two_changed_columns (huv : u ≠ v) :
    ∃ A B : Fin k, A ≠ B ∧ u A ≠ v A ∧ u B ≠ v B ∧ u B = v A := by
  obtain ⟨A, hA⟩ : ∃ A, u A ≠ v A := by
    by_contra hcon
    exact huv (GridState.ext fun c => by
      by_contra h
      exact hcon ⟨c, h⟩)
  have huB : u (u.toPerm.symm (v A)) = v A := u.toPerm.apply_symm_apply (v A)
  have hAB : A ≠ u.toPerm.symm (v A) := by
    intro h
    apply hA
    calc u A = u (u.toPerm.symm (v A)) := by rw [← h]
      _ = v A := huB
  refine ⟨A, u.toPerm.symm (v A), hAB, hA, ?_, huB⟩
  intro h
  exact hAB (v.toPerm.injective (huB.symm.trans h))

/-- A changed column contributes at least two to four times the index of a nonnegative
domain. -/
theorem two_le_cornerSum_add (hD : D.IsFrom u v) (hpos : ∀ c r, 0 ≤ D c r) {c : Fin k}
    (hc : u c ≠ v c) :
    1 ≤ D.cornerSum c (u c) ∧ 1 ≤ D.cornerSum c (v c) := by
  refine ⟨one_le_cornerSum hpos ?_, one_le_cornerSum hpos ?_⟩
  · rw [boundary_source hD hc]
    norm_num
  · rw [boundary_target hD hc]
    norm_num

/-- A nonnegative domain between distinct states has index at least one. -/
theorem four_le_index4 (hD : D.IsFrom u v) (hpos : ∀ c r, 0 ≤ D c r) (huv : u ≠ v) :
    4 ≤ D.index4 u v := by
  obtain ⟨A, B, hAB, hA, hB, -⟩ := exists_two_changed_columns huv
  have hA' := two_le_cornerSum_add hD hpos hA
  have hB' := two_le_cornerSum_add hD hpos hB
  have hsum : D.cornerSum A (u A) + D.cornerSum A (v A) +
      (D.cornerSum B (u B) + D.cornerSum B (v B)) ≤ D.index4 u v :=
    Finset.add_le_sum (fun c _ => add_nonneg (cornerSum_nonneg hpos c (u c))
      (cornerSum_nonneg hpos c (v c))) (Finset.mem_univ A) (Finset.mem_univ B) hAB
  omega

end GridDomain

end OnLeConjecture.KnotFloer.GridFull

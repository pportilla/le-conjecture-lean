/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Rectangle.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Integral domains on a toroidal grid

An integral domain on the `k × k` toroidal grid is an integer-valued function on its squares.
A square is indexed by its lower-left vertex, and all index arithmetic is cyclic in `Fin k`.

This file defines the mixed difference `GridDomain.boundary` of a domain, the predicate
`GridDomain.IsFrom` for a domain from one grid state to another, the corner sums and four times
the index `GridDomain.index4`, the domain `GridRectangleBetween.domain` of an oriented rectangle,
the column and row annuli, and the point-count grading `gridMarkMaslov` attached to an auxiliary
permutation of marks. The main result is `GridRectangleBetween.domain_isFrom`: the domain of an
oriented rectangle from `x` to `y` is a domain from `x` to `y`.

The file also records two cyclic tools used later: the boundary rule
`ite_mem_cIco_sub_one` for half-open cyclic intervals and the induction principle
`cyclic_induction` along predecessors in `Fin k`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
open scoped BigOperators

variable {k : ℕ} [NeZero k]

/-- An integral domain on the `k × k` toroidal grid. The value at `(c, r)` is the multiplicity
of the square whose lower-left vertex is `(c, r)`. -/
abbrev GridDomain (k : ℕ) := Fin k → Fin k → ℤ

/-- The indicator function of the points of a grid state. -/
def gridStateIndicator (u : GridState k) (c r : Fin k) : ℤ :=
  if u c = r then 1 else 0

namespace GridDomain

/-- The mixed difference of a domain at the vertex `(c, r)`. -/
def boundary (D : GridDomain k) (c r : Fin k) : ℤ :=
  D c r + D (c - 1) (r - 1) - D (c - 1) r - D c (r - 1)

/-- A domain from `u` to `v`: its mixed difference is `[u] - [v]`. -/
def IsFrom (D : GridDomain k) (u v : GridState k) : Prop :=
  ∀ c r, D.boundary c r = gridStateIndicator u c r - gridStateIndicator v c r

/-- The sum of the four multiplicities around the vertex `(c, r)`. -/
def cornerSum (D : GridDomain k) (c r : Fin k) : ℤ :=
  D c r + D (c - 1) (r - 1) + D (c - 1) r + D c (r - 1)

/-- Four times the index ι(D;u,v) of the written proof. -/
def index4 (D : GridDomain k) (u v : GridState k) : ℤ :=
  ∑ c, (D.cornerSum c (u c) + D.cornerSum c (v c))

/-- The column annulus of multiplicity one at column `i`. -/
def column (i : Fin k) : GridDomain k := fun c _ => if c = i then 1 else 0

/-- The row annulus of multiplicity one at row `j`. -/
def row (j : Fin k) : GridDomain k := fun _ r => if r = j then 1 else 0

end GridDomain

/-- Indicator of `[R.left, R.right)_cyc × [x R.left, x R.right)_cyc`. -/
def _root_.TauCeti.GridRectangleBetween.domain {x y : GridState k}
    (R : GridRectangleBetween x y) : GridDomain k :=
  fun c r =>
    if c ∈ Grid.cIco R.left R.right ∧ r ∈ Grid.cIco (x R.left) (x R.right) then 1 else 0

/-- Point-count grading for an auxiliary permutation `O` of marks at `(c+1/2, O c+1/2)`. -/
def gridMarkMaslov (O : Equiv.Perm (Fin k)) (u : GridState k) : ℤ :=
  ((Finset.univ.filter fun p : Fin k × Fin k => p.1 < p.2 ∧ u p.1 < u p.2).card : ℤ) -
    ((Finset.univ.filter fun p : Fin k × Fin k => p.1 ≤ p.2 ∧ u p.1 ≤ O p.2).card : ℤ) -
    ((Finset.univ.filter fun p : Fin k × Fin k => p.1 < p.2 ∧ O p.1 < u p.2).card : ℤ) +
    ((Finset.univ.filter fun p : Fin k × Fin k => p.1 < p.2 ∧ O p.1 < O p.2).card : ℤ)

/-! ### Cyclic tools -/

/-- The value of the cyclic predecessor in `Fin k`. -/
theorem val_sub_one_cyclic (c : Fin k) :
    ((c - 1 : Fin k) : ℕ) = if (c : ℕ) = 0 then k - 1 else c - 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos k)).symm⟩
  rw [Fin.coe_sub_one]
  by_cases h : c = 0
  · subst h
    simp
  · have h' : (c : ℕ) ≠ 0 := fun h'' => h (Fin.ext h'')
    rw [if_neg h, if_neg h']

/-- Boundary rule for a half-open cyclic interval: passing from `c - 1` to `c` enters
`[a, b)_cyc` at `a` and leaves it at `b`. -/
theorem ite_mem_cIco_sub_one (a b c : Fin k) :
    (if c - 1 ∈ Grid.cIco a b then (1 : ℤ) else 0) =
      (if c ∈ Grid.cIco a b then 1 else 0) - (if c = a then 1 else 0) +
        (if c = b then 1 else 0) := by
  have hc := c.isLt
  have ha := a.isLt
  have hb := b.isLt
  have h1 := val_sub_one_cyclic c
  simp only [Grid.mem_cIco, Fin.ext_iff, ne_eq, ite_prop_iff_or]
  rw [h1]
  split_ifs <;> omega

/-- The predecessor of the initial endpoint is not in a half-open cyclic interval. -/
theorem sub_one_notMem_cIco (a b : Fin k) : a - 1 ∉ Grid.cIco a b := by
  intro h
  have key := ite_mem_cIco_sub_one a b a
  rw [if_pos h, if_pos rfl] at key
  by_cases hab : a = b
  · subst hab
    simp at h
  · rw [if_pos (Grid.left_mem_cIco hab), if_neg hab] at key
    norm_num at key

open Fin.NatCast in
/-- Induction along cyclic predecessors: a property of one point that passes from `c - 1` to
`c` holds at every point of `Fin k`. -/
theorem cyclic_induction {P : Fin k → Prop} (a : Fin k) (ha : P a)
    (hstep : ∀ c, P (c - 1) → P c) (c : Fin k) : P c := by
  have key : ∀ j : ℕ, ∀ c : Fin k, P (c - (j : Fin k)) → P c := by
    intro j
    induction j with
    | zero =>
      intro c hc
      simpa using hc
    | succ j ih =>
      intro c hc
      apply hstep
      apply ih
      rwa [Nat.cast_succ, sub_add_eq_sub_sub_swap] at hc
  apply key (c - a).val
  rwa [Fin.cast_val_eq_self, sub_sub_cancel]

/-- Reindexing a sum over `Fin k` by the cyclic predecessor. -/
theorem sum_comp_sub_one {M : Type*} [AddCommMonoid M] (f : Fin k → M) :
    ∑ c, f (c - 1) = ∑ c, f c :=
  (Equiv.subRight (1 : Fin k)).sum_comp f

/-- An indicator of a conjunction is the product of the indicators. -/
theorem ite_and_one_zero (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℤ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

namespace GridDomain

variable {D E : GridDomain k} {u v w : GridState k}

/-! ### Linearity of the mixed difference and of the corner sums -/

@[simp]
theorem boundary_add (D E : GridDomain k) (c r : Fin k) :
    (D + E).boundary c r = D.boundary c r + E.boundary c r := by
  simp only [boundary, Pi.add_apply]
  ring

@[simp]
theorem boundary_neg (D : GridDomain k) (c r : Fin k) :
    (-D).boundary c r = -D.boundary c r := by
  simp only [boundary, Pi.neg_apply]
  ring

@[simp]
theorem boundary_sub (D E : GridDomain k) (c r : Fin k) :
    (D - E).boundary c r = D.boundary c r - E.boundary c r := by
  simp only [boundary, Pi.sub_apply]
  ring

@[simp]
theorem boundary_zero (c r : Fin k) : (0 : GridDomain k).boundary c r = 0 := by
  simp [boundary]

@[simp]
theorem cornerSum_add (D E : GridDomain k) (c r : Fin k) :
    (D + E).cornerSum c r = D.cornerSum c r + E.cornerSum c r := by
  simp only [cornerSum, Pi.add_apply]
  ring

@[simp]
theorem cornerSum_neg (D : GridDomain k) (c r : Fin k) :
    (-D).cornerSum c r = -D.cornerSum c r := by
  simp only [cornerSum, Pi.neg_apply]
  ring

@[simp]
theorem cornerSum_sub (D E : GridDomain k) (c r : Fin k) :
    (D - E).cornerSum c r = D.cornerSum c r - E.cornerSum c r := by
  simp only [cornerSum, Pi.sub_apply]
  ring

/-! ### Domains between grid states -/

/-- Concatenation of domains: a domain from `u` to `v` plus a domain from `v` to `w`. -/
theorem IsFrom.add (hD : D.IsFrom u v) (hE : E.IsFrom v w) : (D + E).IsFrom u w := by
  intro c r
  rw [boundary_add, hD, hE]
  ring

/-- Reversal of a domain. -/
theorem IsFrom.neg (hD : D.IsFrom u v) : (-D).IsFrom v u := by
  intro c r
  rw [boundary_neg, hD]
  ring

/-- Difference of two domains with a common terminal state. -/
theorem IsFrom.sub (hD : D.IsFrom u v) (hE : E.IsFrom w v) : (D - E).IsFrom u w := by
  intro c r
  rw [boundary_sub, hD, hE]
  ring

/-- The zero domain is a domain from any state to itself. -/
theorem isFrom_zero (u : GridState k) : (0 : GridDomain k).IsFrom u u := by
  intro c r
  simp

/-- A domain from a state to itself is exactly a domain with zero mixed difference. -/
theorem isFrom_self_iff_boundary_eq_zero :
    D.IsFrom u u ↔ ∀ c r, D.boundary c r = 0 := by
  simp only [IsFrom, sub_self]

/-- The column annulus has zero mixed difference. -/
theorem column_isFrom (i : Fin k) (u : GridState k) : (column i).IsFrom u u := by
  rw [isFrom_self_iff_boundary_eq_zero]
  intro c r
  simp only [boundary, column]
  ring

/-- The row annulus has zero mixed difference. -/
theorem row_isFrom (j : Fin k) (u : GridState k) : (row j).IsFrom u u := by
  rw [isFrom_self_iff_boundary_eq_zero]
  intro c r
  simp only [boundary, row]
  ring

end GridDomain

/-! ### Rectangle domains -/

end OnLeConjecture.KnotFloer.GridFull

namespace TauCeti.GridRectangleBetween
open OnLeConjecture.KnotFloer.GridFull

variable {k : ℕ} [NeZero k] {x y : GridState k}

omit [NeZero k] in
theorem domain_apply (R : GridRectangleBetween x y) (c r : Fin k) :
    R.domain c r =
      if c ∈ Grid.cIco R.left R.right ∧ r ∈ Grid.cIco (x R.left) (x R.right) then 1 else 0 :=
  rfl

/-- The mixed difference of a rectangle domain is a product of two endpoint differences. -/
theorem domain_boundary (R : GridRectangleBetween x y) (c r : Fin k) :
    R.domain.boundary c r =
      ((if c = R.left then 1 else 0) - (if c = R.right then 1 else 0)) *
        ((if r = x R.left then 1 else 0) - (if r = x R.right then 1 else 0)) := by
  simp only [GridDomain.boundary, domain_apply, ite_and_one_zero]
  rw [ite_mem_cIco_sub_one R.left R.right c,
    ite_mem_cIco_sub_one (x R.left) (x R.right) r]
  ring

/-- The domain of an oriented rectangle from `x` to `y` is a domain from `x` to `y`. -/
theorem domain_isFrom (R : GridRectangleBetween x y) : R.domain.IsFrom x y := by
  intro c r
  have hab := R.left_ne_right
  have hxab : x R.left ≠ x R.right := fun h => hab (x.toPerm.injective h)
  rw [domain_boundary]
  simp only [gridStateIndicator]
  by_cases hca : c = R.left
  · subst hca
    rw [R.map_left]
    by_cases h1 : r = x R.left
    · subst h1
      simp [hab, hxab, Ne.symm hab]
    · by_cases h2 : r = x R.right
      · subst h2
        simp [hab, hxab.symm]
      · simp [hab, h1, h2, Ne.symm h1, Ne.symm h2]
  · by_cases hcb : c = R.right
    · subst hcb
      rw [R.map_right]
      by_cases h1 : r = x R.left
      · subst h1
        simp [hca, hxab]
      · by_cases h2 : r = x R.right
        · subst h2
          simp [hca, hxab.symm, Ne.symm hca]
        · simp [hca, h1, h2, Ne.symm h1, Ne.symm h2]
    · rw [R.map_of_ne c hca hcb]
      simp [hca, hcb]

end TauCeti.GridRectangleBetween

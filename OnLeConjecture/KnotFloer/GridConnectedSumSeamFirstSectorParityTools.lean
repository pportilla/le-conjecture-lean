/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridDomainIndexOne
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFrozenColumnsCount
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFlatPathExclusion
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFivePoint
import Mathlib.Tactic

/-!
# Tools for the fixed-second correction paths

This file collects the generic statements used in the proof of Theorem
J05:thm:seam-first-long-empty.

* `GridDomain.eq_ite_of_index4_le_periodic`: a nonnegative domain with zero mixed difference has
  index at least twice its multiplicity at any cell, and in the case of equality it is the sum of
  a multiple of one column annulus and a multiple of one row annulus.
* `gridRectangle_domain_eq_zero_of_ne_sides`: an empty rectangle domain vanishes on the four
  cells adjacent to a source point outside its side columns.
* `seamCorrectionPath_isEmpty_of_le_two`: on a seam with both parameters at most two, no
  correction path has three or more internal transitions.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
open scoped BigOperators

/-! ### Periodic domains -/

namespace GridDomain

variable {K : ℕ} [NeZero K] {E : GridDomain K}

/-- A nonnegative domain with zero mixed difference is `a c + b r` with `a, b ≥ 0`. -/
theorem exists_nonneg_periodic_of_boundary_eq_zero (hpos : ∀ c r, 0 ≤ E c r)
    (h : ∀ c r, E.boundary c r = 0) :
    ∃ a b : Fin K → ℤ, (∀ c r, E c r = a c + b r) ∧ (∀ c, 0 ≤ a c) ∧ (∀ r, 0 ≤ b r) := by
  obtain ⟨a, b, hab⟩ := exists_eq_add_of_boundary_eq_zero h
  obtain ⟨c0, -, hc0⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  refine ⟨fun c => a c - a c0, fun r => b r + a c0, fun c r => by rw [hab]; ring,
    fun c => ?_, fun r => ?_⟩
  · have := hc0 c (Finset.mem_univ _)
    simp only
    linarith
  · have := hpos c0 r
    rw [hab] at this
    simp only
    linarith

/-- A nonnegative domain `E` with zero mixed difference satisfies `8 E(i₀, j₀) ≤ index4 E u u`.
If equality holds, then `E` is a nonnegative multiple of the column annulus at `i₀` plus a
nonnegative multiple of the row annulus at `j₀`. -/
theorem eq_ite_of_index4_le_periodic (hpos : ∀ c r, 0 ≤ E c r)
    (h : ∀ c r, E.boundary c r = 0) (u : GridState K) (i₀ j₀ : Fin K) :
    8 * E i₀ j₀ ≤ E.index4 u u ∧
      (E.index4 u u ≤ 8 * E i₀ j₀ → ∃ α β : ℤ, 0 ≤ α ∧ 0 ≤ β ∧
        ∀ c r, E c r = (if c = i₀ then α else 0) + (if r = j₀ then β else 0)) := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_nonneg_periodic_of_boundary_eq_zero hpos h
  have hE : E = fun c r => a c + b r := funext fun c => funext fun r => hab c r
  have hidx : E.index4 u u = 8 * (∑ c, a c + ∑ r, b r) := by
    rw [hE, index4_add_periodic]
  have hsa := Finset.add_sum_erase Finset.univ a (Finset.mem_univ i₀)
  have hsb := Finset.add_sum_erase Finset.univ b (Finset.mem_univ j₀)
  have hea : 0 ≤ ∑ c ∈ Finset.univ.erase i₀, a c := Finset.sum_nonneg fun c _ => ha c
  have heb : 0 ≤ ∑ r ∈ Finset.univ.erase j₀, b r := Finset.sum_nonneg fun r _ => hb r
  refine ⟨by rw [hidx, hab]; linarith, fun hle => ?_⟩
  rw [hidx, hab] at hle
  have hza : ∑ c ∈ Finset.univ.erase i₀, a c = 0 := by linarith
  have hzb : ∑ r ∈ Finset.univ.erase j₀, b r = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg fun c _ => ha c] at hza
  rw [Finset.sum_eq_zero_iff_of_nonneg fun r _ => hb r] at hzb
  refine ⟨a i₀, b j₀, ha i₀, hb j₀, fun c r => ?_⟩
  rw [hab]
  congr 1
  · by_cases hc : c = i₀
    · rw [if_pos hc, hc]
    · rw [if_neg hc]
      exact hza c (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩)
  · by_cases hr : r = j₀
    · rw [if_pos hr, hr]
    · rw [if_neg hr]
      exact hzb r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩)

end GridDomain

/-! ### Rectangle domains -/

section Rectangle

variable {K : ℕ} [NeZero K] {x y : GridState K}

omit [NeZero K] in
/-- A rectangle domain vanishes in its terminal side column. -/
theorem gridRectangle_domain_right_eq_zero (R : GridRectangleBetween x y) (r : Fin K) :
    R.domain R.right r = 0 := by
  unfold GridRectangleBetween.domain
  rw [if_neg]
  exact fun h => Grid.right_notMem_cIco _ _ h.1

/-- An empty rectangle domain vanishes on the four cells adjacent to a source point outside its
side columns. -/
theorem gridRectangle_domain_eq_zero_of_ne_sides (R : GridRectangleBetween x y) (hR : R.IsEmpty)
    {c : Fin K} (hl : c ≠ R.left) (hr : c ≠ R.right) {a b : Fin K} (ha : a = c ∨ a = c - 1)
    (hb : b = x c ∨ b = x c - 1) : R.domain a b = 0 := by
  unfold GridRectangleBetween.domain
  rw [if_neg]
  rintro ⟨hac, hbc⟩
  have hc : c ∈ Grid.cIco R.left R.right := by
    rcases ha with rfl | rfl
    · exact hac
    · exact (sub_one_mem_cIco_iff hl hr).mp hac
  have hxl : x c ≠ x R.left := fun h => hl (x.toPerm.injective h)
  have hxr : x c ≠ x R.right := fun h => hr (x.toPerm.injective h)
  have hxc : x c ∈ Grid.cIco (x R.left) (x R.right) := by
    rcases hb with rfl | rfl
    · exact hbc
    · exact (sub_one_mem_cIco_iff hxl hxr).mp hbc
  rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo] at hR
  exact hR c (Grid.mem_cIoo_of_mem_cIco hc hl) (Grid.mem_cIoo_of_mem_cIco hxc hxl)

end Rectangle

/-! ### Small seams -/

/-- On a seam with both parameters at most two, no correction path has three or more internal
transitions. -/
theorem seamCorrectionPath_isEmpty_of_le_two {n m k : ℕ} (hn : n ≤ 2) (hm : m ≤ 2)
    (hk : 3 ≤ k) (p q : SeamRetainedIndex n m) : IsEmpty (SeamCorrectionPath k p q) := by
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · exact seamCorrectionPath_isEmpty_of_left_le_one (by omega) (by omega) p q
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · exact seamCorrectionPath_isEmpty_of_right_le_one (by omega) (by omega) p q
  obtain rfl : n = 2 := by omega
  obtain rfl : m = 2 := by omega
  exact seamCorrectionPath_two_two_isEmpty hk p q

/-- A correction path with at least three internal transitions cannot keep fixed every west
column except two and every column strictly between `n` and `n + m` with a high initial row. -/
theorem SeamCorrectionPath.false_of_fixesColumn {n m k : ℕ} (hk : 3 ≤ k)
    {p q : SeamRetainedIndex n m} (π : SeamCorrectionPath k p q) (L R : Fin (n + m + 1))
    (hwest : ∀ c : Fin (n + m + 1), c.val < n → c ≠ L → c ≠ R → π.FixesColumn c)
    (heast : ∀ c : Fin (n + m + 1), n < c.val → c.val < n + m →
      n < (seamState p.1 p.2 c).val → π.FixesColumn c) : False := by
  obtain ⟨n', m', p', q', hn', hm', ⟨π'⟩⟩ := π.exists_small_of_fixesColumn L R hwest heast
  exact (seamCorrectionPath_isEmpty_of_le_two hn' hm' hk p' q').false π'

end OnLeConjecture.KnotFloer.GridFull

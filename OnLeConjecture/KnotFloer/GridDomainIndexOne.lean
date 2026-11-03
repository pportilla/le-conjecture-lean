/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridDomainIndex
import Mathlib.Tactic

/-!
# Nonnegative domains of index one

Let `D` be a nonnegative integral domain from distinct grid states `u` to `v` whose index is
one, that is `D.index4 u v = 4`. Then `D` is the domain of an empty rectangle from `u` to `v`
(`GridDomain.exists_rectangle_of_index4_eq_four`).

The proof follows the written proof. The lower bound of `GridDomain.four_le_index4` forces
the states to differ in exactly two columns `A` and `B` and forces every corner sum at an
unchanged source point to vanish. The mixed difference then shows that `D` is constant on each
of the four products of the cyclic intervals `[A, B)`, `[B, A)` and `[u A, u B)`, `[u B, u A)`.
The corner sum and the mixed difference at `(A, u A)` determine the four constants.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
open scoped BigOperators

variable {k : ℕ} [NeZero k]

namespace GridDomain

variable {D : GridDomain k} {u v : GridState k}

/-- For a nonnegative domain of index one between states with changed columns `A ≠ B`, the
states agree outside `A` and `B`, every corner sum at an unchanged source point vanishes, and
the corner sum at `(A, u A)` is one. -/
theorem index4_eq_four_structure (hD : D.IsFrom u v) (hpos : ∀ c r, 0 ≤ D c r)
    {A B : Fin k} (hAB : A ≠ B) (hA : u A ≠ v A) (hB : u B ≠ v B) (h4 : D.index4 u v = 4) :
    (∀ c, c ≠ A → c ≠ B → u c = v c ∧ D.cornerSum c (u c) = 0) ∧
      D.cornerSum A (u A) = 1 := by
  have hidx : ∑ c, (D.cornerSum c (u c) + D.cornerSum c (v c)) = 4 := h4
  have ht0 : ∀ c, 0 ≤ D.cornerSum c (u c) + D.cornerSum c (v c) := fun c =>
    add_nonneg (cornerSum_nonneg hpos c (u c)) (cornerSum_nonneg hpos c (v c))
  have hA' := two_le_cornerSum_add hD hpos hA
  have hB' := two_le_cornerSum_add hD hpos hB
  have hAB_le : D.cornerSum A (u A) + D.cornerSum A (v A) +
      (D.cornerSum B (u B) + D.cornerSum B (v B)) ≤ 4 :=
    hidx ▸ Finset.add_le_sum (fun c _ => ht0 c) (Finset.mem_univ A) (Finset.mem_univ B) hAB
  refine ⟨fun c hcA hcB => ?_, by omega⟩
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun c => D.cornerSum c (u c) + D.cornerSum c (v c))
    (Finset.subset_univ ({A, B, c} : Finset (Fin k))) (fun i _ _ => ht0 i)
  have hAn : A ∉ ({B, c} : Finset (Fin k)) := by simp [hAB, Ne.symm hcA]
  have hBn : B ∉ ({c} : Finset (Fin k)) := by simp [Ne.symm hcB]
  simp only [Finset.sum_insert hAn, Finset.sum_insert hBn, Finset.sum_singleton, hidx] at hsub
  have hc0 := ht0 c
  have huvc : u c = v c := by
    by_contra hne
    have := two_le_cornerSum_add hD hpos hne
    omega
  refine ⟨huvc, ?_⟩
  have hcu := cornerSum_nonneg hpos c (u c)
  rw [← huvc] at hsub
  omega

/-- A nonnegative domain of index one between distinct states is the domain of an empty
rectangle. -/
theorem exists_rectangle_of_index4_eq_four (hD : D.IsFrom u v) (hpos : ∀ c r, 0 ≤ D c r)
    (huv : u ≠ v) (h4 : D.index4 u v = 4) :
    ∃ R : GridRectangleBetween u v, R.IsEmpty ∧ D = R.domain := by
  obtain ⟨A, B, hAB, hA, hB, huB⟩ := exists_two_changed_columns huv
  obtain ⟨hrest, hcsA⟩ := index4_eq_four_structure hD hpos hAB hA hB h4
  have huvc : ∀ c, c ≠ A → c ≠ B → v c = u c := fun c h1 h2 => ((hrest c h1 h2).1).symm
  have huAB : u A ≠ u B := fun h => hAB (u.toPerm.injective h)
  -- The second changed column exchanges the two rows.
  have hvB : v B = u A := by
    have huc' : u (u.toPerm.symm (v B)) = v B := u.toPerm.apply_symm_apply (v B)
    by_cases h1 : u.toPerm.symm (v B) = A
    · rw [← huc', h1]
    · by_cases h2 : u.toPerm.symm (v B) = B
      · exfalso
        apply hB
        rw [← huc', h2]
      · exfalso
        exact h2 (v.toPerm.injective ((huvc _ h1 h2).trans huc'))
  -- The four squares at an unchanged source point have multiplicity zero.
  have hzero : ∀ c, c ≠ A → c ≠ B →
      D c (u c) = 0 ∧ D (c - 1) (u c - 1) = 0 ∧ D (c - 1) (u c) = 0 ∧ D c (u c - 1) = 0 :=
    fun c h1 h2 => eq_zero_of_cornerSum_eq_zero hpos (hrest c h1 h2).2
  -- Crossing an unchanged column does not change the multiplicity.
  have hcol : ∀ c, c ≠ A → c ≠ B → ∀ r, D c r = D (c - 1) r := by
    intro c h1 h2 r
    have hbd : ∀ r, D.boundary c r = 0 := by
      intro r
      rw [hD c r]
      simp [gridStateIndicator, huvc c h1 h2]
    refine cyclic_induction (P := fun r => D c r = D (c - 1) r) (u c) ?_ ?_ r
    · rw [(hzero c h1 h2).1, (hzero c h1 h2).2.2.1]
    · intro r hr
      have := hbd r
      simp only [boundary] at this
      linarith
  -- Crossing an unchanged row does not change the multiplicity.
  have hrow : ∀ r, r ≠ u A → r ≠ u B → ∀ c, D c r = D c (r - 1) := by
    intro r h1 h2 c
    have hc₀ : u (u.toPerm.symm r) = r := u.toPerm.apply_symm_apply r
    have hc₀A : u.toPerm.symm r ≠ A := fun h => h1 (by rw [← hc₀, h])
    have hc₀B : u.toPerm.symm r ≠ B := fun h => h2 (by rw [← hc₀, h])
    have hvc₀ : v (u.toPerm.symm r) = r := (huvc _ hc₀A hc₀B).trans hc₀
    have hbd : ∀ c', D.boundary c' r = 0 := by
      intro c'
      rw [hD c' r]
      have hiff : (u c' = r) ↔ (v c' = r) := by
        constructor
        · intro h
          have : c' = u.toPerm.symm r := u.toPerm.injective (h.trans hc₀.symm)
          rw [this, hvc₀]
        · intro h
          have : c' = u.toPerm.symm r := v.toPerm.injective (h.trans hvc₀.symm)
          rw [this, hc₀]
      simp only [gridStateIndicator, hiff, sub_self]
    refine cyclic_induction (P := fun c => D c r = D c (r - 1)) (u.toPerm.symm r) ?_ ?_ c
    · have hz := hzero _ hc₀A hc₀B
      rw [hc₀] at hz
      rw [hz.1, hz.2.2.2]
    · intro c hc
      have := hbd c
      simp only [boundary] at this
      linarith
  -- Constancy in the column direction on `[A, B)` and on its complement.
  have hcolblock : ∀ c r, D c r = if c ∈ Grid.cIco A B then D A r else D B r := by
    intro c r
    refine cyclic_induction
      (P := fun c => D c r = if c ∈ Grid.cIco A B then D A r else D B r) A ?_ ?_ c
    · rw [if_pos (Grid.left_mem_cIco hAB)]
    · intro c hc
      by_cases h1 : c = A
      · rw [h1, if_pos (Grid.left_mem_cIco hAB)]
      by_cases h2 : c = B
      · rw [h2, if_neg (Grid.right_notMem_cIco A B)]
      rw [hcol c h1 h2 r, hc]
      simp only [sub_one_mem_cIco_iff h1 h2]
  -- Constancy in the row direction on `[u A, u B)` and on its complement.
  have hrowblock : ∀ c r,
      D c r = if r ∈ Grid.cIco (u A) (u B) then D c (u A) else D c (u B) := by
    intro c r
    refine cyclic_induction
      (P := fun r => D c r = if r ∈ Grid.cIco (u A) (u B) then D c (u A) else D c (u B))
      (u A) ?_ ?_ r
    · rw [if_pos (Grid.left_mem_cIco huAB)]
    · intro r hr
      by_cases h1 : r = u A
      · rw [h1, if_pos (Grid.left_mem_cIco huAB)]
      by_cases h2 : r = u B
      · rw [h2, if_neg (Grid.right_notMem_cIco (u A) (u B))]
      rw [hrow r h1 h2 c, hr]
      simp only [sub_one_mem_cIco_iff h1 h2]
  have hblock : ∀ c r, D c r =
      if c ∈ Grid.cIco A B then
        (if r ∈ Grid.cIco (u A) (u B) then D A (u A) else D A (u B))
      else (if r ∈ Grid.cIco (u A) (u B) then D B (u A) else D B (u B)) := by
    intro c r
    rw [hcolblock c r, hrowblock A r, hrowblock B r]
  -- The corner sum and the mixed difference at `(A, u A)` determine the four constants.
  have hA1 := sub_one_notMem_cIco A B
  have huA1 := sub_one_notMem_cIco (u A) (u B)
  have hAmem := Grid.left_mem_cIco hAB
  have huAmem := Grid.left_mem_cIco huAB
  have e1 : D (A - 1) (u A - 1) = D B (u B) := by
    rw [hblock (A - 1) (u A - 1), if_neg hA1, if_neg huA1]
  have e2 : D (A - 1) (u A) = D B (u A) := by
    rw [hblock (A - 1) (u A), if_neg hA1, if_pos huAmem]
  have e3 : D A (u A - 1) = D A (u B) := by
    rw [hblock A (u A - 1), if_pos hAmem, if_neg huA1]
  have hcs := hcsA
  simp only [cornerSum] at hcs
  have hbdA := boundary_source hD hA
  simp only [boundary] at hbdA
  rw [e1, e2, e3] at hcs hbdA
  have p1 := hpos A (u A)
  have p2 := hpos A (u B)
  have p3 := hpos B (u A)
  have p4 := hpos B (u B)
  have hβ : D A (u B) = 0 := by omega
  have hγ : D B (u A) = 0 := by omega
  have hcases : (D A (u A) = 1 ∧ D B (u B) = 0) ∨ (D A (u A) = 0 ∧ D B (u B) = 1) := by
    omega
  rcases hcases with ⟨hα, hδ⟩ | ⟨hα, hδ⟩
  · -- The rectangle with sides `A` and `B`.
    have hDR : D = (⟨A, B, hAB, huB.symm, hvB, fun c h1 h2 => huvc c h1 h2⟩ :
        GridRectangleBetween u v).domain := by
      funext c r
      rw [hblock c r, GridRectangleBetween.domain_apply]
      dsimp only
      by_cases hc : c ∈ Grid.cIco A B <;> by_cases hr : r ∈ Grid.cIco (u A) (u B) <;>
        simp only [hc, hr, ↓reduceIte, and_true, and_false, hα, hβ, hγ, hδ]
    refine ⟨_, GridRectangleBetween.isEmpty_of_domain_apply_eq_zero _ fun c h1 h2 => ?_, hDR⟩
    rw [← hDR]
    exact (hzero c h1 h2).1
  · -- The rectangle with sides `B` and `A`.
    have hDR : D = (⟨B, A, hAB.symm, hvB, huB.symm, fun c h1 h2 => huvc c h2 h1⟩ :
        GridRectangleBetween u v).domain := by
      funext c r
      have hc2 : c ∈ Grid.cIco B A ↔ c ∉ Grid.cIco A B :=
        (Grid.notMem_cIco_iff_mem_cIco_swap hAB).symm
      have hr2 : r ∈ Grid.cIco (u B) (u A) ↔ r ∉ Grid.cIco (u A) (u B) :=
        (Grid.notMem_cIco_iff_mem_cIco_swap huAB).symm
      rw [hblock c r, GridRectangleBetween.domain_apply]
      dsimp only
      simp only [hc2, hr2]
      by_cases hc : c ∈ Grid.cIco A B <;> by_cases hr : r ∈ Grid.cIco (u A) (u B) <;>
        simp only [hc, hr, ↓reduceIte, not_true_eq_false, not_false_eq_true, and_true,
          and_false, hα, hβ, hγ, hδ]
    refine ⟨_, GridRectangleBetween.isEmpty_of_domain_apply_eq_zero _ fun c h1 h2 => ?_, hDR⟩
    rw [← hDR]
    exact (hzero c h2 h1).1

end GridDomain

end OnLeConjecture.KnotFloer.GridFull

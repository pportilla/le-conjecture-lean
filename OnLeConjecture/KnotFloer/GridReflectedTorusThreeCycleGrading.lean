/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusAnchor
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Grading.Southwest

/-!
# Alexander grading for the reflected torus three-cycle states

The southwest-count formula reduces the grading changes to three column
contributions. These are the states that occur in the first proposed
torus representative after the rectangle cancellations.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

private theorem card_fin_filter_interval (N l u : ℕ) (hu : u ≤ N) :
    (Finset.univ.filter fun d : Fin N => l ≤ d.val ∧ d.val < u).card = u - l := by
  classical
  rw [← Nat.card_Ico]
  refine Finset.card_bij (fun d _ => d.val) ?_ ?_ ?_
  · intro d hd
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hd).2
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro b hb
    have h := Finset.mem_Ico.mp hb
    exact ⟨⟨b, h.2.trans_le hu⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

/-- Explicit row of an X marking in the reflected torus diagram. -/
theorem reflectedTorusGrid_X_val (n : ℕ) (c : Fin (consecutiveTorusGridSize n)) :
    ((reflectedTorusGrid n).X c : ℕ) =
      if c.val ≤ n then n - c.val else 3 * n + 3 - c.val := by
  rw [reflectedTorusGrid_X_apply, Fin.val_rev, Fin.coe_finRotate_pow]
  have hc := c.isLt
  unfold consecutiveTorusGridSize at *
  by_cases h : c.val ≤ n
  · rw [Nat.mod_eq_of_lt (by omega), if_pos h]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), if_neg h]
    omega

/-- The southwest O count is the length of one interval of columns. -/
theorem southwestCount_reflectedTorus_O (n : ℕ)
    (c r : Fin (consecutiveTorusGridSize n)) :
    (reflectedTorusGrid n).O.southwestCount c r =
      c.val - (consecutiveTorusGridSize n - r.val) := by
  classical
  rw [GridState.southwestCount_def]
  have heq : (Finset.univ.filter fun d : Fin (consecutiveTorusGridSize n) =>
      d < c ∧ (reflectedTorusGrid n).O d < r) =
      Finset.univ.filter (fun d => consecutiveTorusGridSize n - r.val ≤ d.val ∧ d.val < c.val) := by
    ext d
    have hd := d.isLt
    have hr := r.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def,
      reflectedTorusGrid_O_apply, Fin.val_rev]
    omega
  rw [heq, card_fin_filter_interval _ _ _ c.isLt.le]

/-- The southwest X count is the sum of the lengths of two disjoint intervals. -/
theorem southwestCount_reflectedTorus_X (n : ℕ)
    (c r : Fin (consecutiveTorusGridSize n)) :
    (reflectedTorusGrid n).X.southwestCount c r =
      (min c.val (n + 1) - (n + 1 - r.val)) + (c.val - (3 * n + 4 - r.val)) := by
  classical
  let A := Finset.univ.filter fun d : Fin (consecutiveTorusGridSize n) =>
    n + 1 - r.val ≤ d.val ∧ d.val < min c.val (n + 1)
  let B := Finset.univ.filter fun d : Fin (consecutiveTorusGridSize n) =>
    3 * n + 4 - r.val ≤ d.val ∧ d.val < c.val
  have hc := c.isLt
  have hr := r.isLt
  have heq : (Finset.univ.filter fun d : Fin (consecutiveTorusGridSize n) =>
      d < c ∧ (reflectedTorusGrid n).X d < r) = A ∪ B := by
    ext d
    have hd := d.isLt
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Fin.lt_def, reflectedTorusGrid_X_val]
    unfold consecutiveTorusGridSize at *
    split_ifs <;> omega
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro d hdA hdB
    have hA := (Finset.mem_filter.mp hdA).2
    have hB := (Finset.mem_filter.mp hdB).2
    unfold consecutiveTorusGridSize at *
    omega
  rw [GridState.southwestCount_def, heq, Finset.card_union_of_disjoint hdisj]
  rw [show A.card = min c.val (n + 1) - (n + 1 - r.val) from
    card_fin_filter_interval _ _ _ ((min_le_left _ _).trans hc.le)]
  rw [show B.card = c.val - (3 * n + 4 - r.val) from
    card_fin_filter_interval _ _ _ hc.le]

/-- The column contribution when its row comes from another anchor column. -/
def reflectedTorusColumnPotential (n c b : ℕ) : ℤ :=
  ((min c (n + 1) - (b - (n + 2)) : ℕ) : ℤ) +
    ((c - (b + n + 1) : ℕ) : ℤ) - ((c - b : ℕ) : ℤ)

/-- An explicit integer formula for each southwest-count difference. -/
theorem southwestCount_reflectedTorus_anchor_difference (n : ℕ)
    (c b : Fin (consecutiveTorusGridSize n)) :
    ((reflectedTorusGrid n).X.southwestCount c (reflectedTorusAnchor n b) : ℤ) -
      (reflectedTorusGrid n).O.southwestCount c (reflectedTorusAnchor n b) =
      reflectedTorusColumnPotential n c.val b.val := by
  rw [southwestCount_reflectedTorus_X, southwestCount_reflectedTorus_O,
    reflectedTorusAnchor_val]
  have hc := c.isLt
  have hb := b.isLt
  simp only [reflectedTorusColumnPotential, Nat.cast_add, Fin.ext_iff, Fin.val_zero]
  unfold consecutiveTorusGridSize at *
  split_ifs <;> omega

private theorem potential_three_cycle_bounds (n a b c : ℕ)
    (hab : a < b) (hbc : b < c) (hc : c < 2 * n + 3)
    (hgap1 : b - a ≤ n + 2) (hgap2 : c - b ≤ n + 2)
    (hgap3 : 2 * n + 3 - c + a ≤ n + 2) :
    (n : ℤ) + 1 ≤
      reflectedTorusColumnPotential n a a + reflectedTorusColumnPotential n b b +
        reflectedTorusColumnPotential n c c -
        (reflectedTorusColumnPotential n a c + reflectedTorusColumnPotential n b a +
          reflectedTorusColumnPotential n c b) ∧
    (n : ℤ) + 1 ≤
      reflectedTorusColumnPotential n a a + reflectedTorusColumnPotential n b b +
        reflectedTorusColumnPotential n c c -
        (reflectedTorusColumnPotential n a b + reflectedTorusColumnPotential n b c +
          reflectedTorusColumnPotential n c a) := by
  unfold reflectedTorusColumnPotential
  omega

private theorem sum_three_of_zero_off {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℤ) (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hzero : ∀ d, d ∉ ({a, b, c} : Finset α) → f d = 0) :
    (∑ d, f d) = f a + f b + f c := by
  calc
    (∑ d, f d) = ∑ d ∈ ({a, b, c} : Finset α), f d :=
      (Finset.sum_subset (Finset.subset_univ _) (fun d _ hd => hzero d hd)).symm
    _ = _ := by simp [hab, hac, hbc, add_assoc]

private theorem alexanderTwo_sub_of_three_columns (n : ℕ)
    (x : GridState (consecutiveTorusGridSize n))
    (a b c u v w : Fin (consecutiveTorusGridSize n))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : x a = reflectedTorusAnchor n u)
    (hb : x b = reflectedTorusAnchor n v)
    (hc : x c = reflectedTorusAnchor n w)
    (hoff : ∀ d, d ≠ a → d ≠ b → d ≠ c → x d = reflectedTorusAnchor n d) :
    (reflectedTorusGrid n).alexanderTwoℤ x -
      (reflectedTorusGrid n).alexanderTwoℤ (reflectedTorusAnchor n) =
      2 * (reflectedTorusColumnPotential n a.val u.val +
        reflectedTorusColumnPotential n b.val v.val +
        reflectedTorusColumnPotential n c.val w.val -
        (reflectedTorusColumnPotential n a.val a.val +
          reflectedTorusColumnPotential n b.val b.val +
          reflectedTorusColumnPotential n c.val c.val)) := by
  classical
  let G := reflectedTorusGrid n
  let f := fun d : Fin (consecutiveTorusGridSize n) =>
    ((G.X.southwestCount d (x d) : ℤ) - G.O.southwestCount d (x d)) -
      ((G.X.southwestCount d (reflectedTorusAnchor n d) : ℤ) -
        G.O.southwestCount d (reflectedTorusAnchor n d))
  have hsum := sum_three_of_zero_off f a b c hab hac hbc (by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    dsimp [f]
    rw [hoff d hd.1 hd.2.1 hd.2.2, sub_self])
  have hA : G.alexanderTwoℤ x - G.alexanderTwoℤ (reflectedTorusAnchor n) =
      2 * ∑ d, f d := by
    rw [G.alexanderTwoℤ_eq_sum_southwestCount,
      G.alexanderTwoℤ_eq_sum_southwestCount]
    dsimp only [f]
    simp only [Finset.sum_sub_distrib]
    ring
  rw [hA, hsum]
  dsimp only [f, G]
  rw [ha, hb, hc]
  simp only [southwestCount_reflectedTorus_anchor_difference]
  ring

/-- Both orientations of a corner three-cycle have the Alexander drop
needed in the first torus representative when all cyclic gaps are at most
`n+2`. -/
theorem alexander_reflectedTorus_three_cycle_bounds (n : ℕ)
    (a b c : Fin (consecutiveTorusGridSize n))
    (hab : a.val < b.val) (hbc : b.val < c.val)
    (hgap1 : b.val - a.val ≤ n + 2) (hgap2 : c.val - b.val ≤ n + 2)
    (hgap3 : consecutiveTorusGridSize n - c.val + a.val ≤ n + 2) :
    (reflectedTorusGrid n).alexander
        (((reflectedTorusAnchor n).swapColumns a b).swapColumns a c) ≤
      (reflectedTorusGrid n).alexander (reflectedTorusAnchor n) - (n + 1 : ℚ) ∧
    (reflectedTorusGrid n).alexander
        (((reflectedTorusAnchor n).swapColumns a c).swapColumns a b) ≤
      (reflectedTorusGrid n).alexander (reflectedTorusAnchor n) - (n + 1 : ℚ) := by
  have hab' : a ≠ b := by intro h; subst b; omega
  have hbc' : b ≠ c := by intro h; subst c; omega
  have hac' : a ≠ c := by intro h; subst c; omega
  have hc := c.isLt
  have hN : consecutiveTorusGridSize n = 2 * n + 3 := by
    unfold consecutiveTorusGridSize
    omega
  have hc' : c.val < 2 * n + 3 := by omega
  have hgap3' : 2 * n + 3 - c.val + a.val ≤ n + 2 := by omega
  have hpot := potential_three_cycle_bounds n a.val b.val c.val hab hbc hc' hgap1 hgap2 hgap3'
  have h₁ := alexanderTwo_sub_of_three_columns n
    (((reflectedTorusAnchor n).swapColumns a b).swapColumns a c)
    a b c c a b hab' hac' hbc'
    (by simp only [GridState.swapColumns_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hac'.symm hbc'.symm])
    (by simp only [GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hab'.symm hbc', Equiv.swap_apply_right])
    (by simp only [GridState.swapColumns_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right]) (by
      intro d hda hdb hdc
      simp [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne, hda, hdb, hdc])
  have h₂ := alexanderTwo_sub_of_three_columns n
    (((reflectedTorusAnchor n).swapColumns a c).swapColumns a b)
    a b c b c a hab' hac' hbc'
    (by simp only [GridState.swapColumns_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hab'.symm hbc'])
    (by simp only [GridState.swapColumns_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right])
    (by simp only [GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hac'.symm hbc'.symm, Equiv.swap_apply_right]) (by
      intro d hda hdb hdc
      simp [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne, hda, hdb, hdc])
  have hI₁ : (reflectedTorusGrid n).alexanderTwoℤ
      (((reflectedTorusAnchor n).swapColumns a b).swapColumns a c) ≤
      (reflectedTorusGrid n).alexanderTwoℤ (reflectedTorusAnchor n) - 2 * ((n : ℤ) + 1) := by
    omega
  have hI₂ : (reflectedTorusGrid n).alexanderTwoℤ
      (((reflectedTorusAnchor n).swapColumns a c).swapColumns a b) ≤
      (reflectedTorusGrid n).alexanderTwoℤ (reflectedTorusAnchor n) - 2 * ((n : ℤ) + 1) := by
    omega
  have hQ₁ := (Int.cast_le (R := ℚ)).mpr hI₁
  have hQ₂ := (Int.cast_le (R := ℚ)).mpr hI₂
  push_cast at hQ₁ hQ₂
  rw [← GridDiagram.two_mul_alexander_eq_intCast,
    ← GridDiagram.two_mul_alexander_eq_intCast] at hQ₁ hQ₂
  constructor <;> linarith

end OnLeConjecture.KnotFloer.GridFull

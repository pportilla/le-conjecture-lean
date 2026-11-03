/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamContraction
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Grading.Southwest
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Southwest pair counts for the shared-corner seam

These counts compare the actual seam state with the pair of factor states.
The shared row and column are retained explicitly.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
open scoped BigOperators
variable {n m : ℕ}

theorem seam_sum (f : Fin (n + m + 1) → ℤ) :
    ∑ c, f c = (∑ a : Fin n, f (seamLeft n m a.castSucc)) +
      ∑ b : Fin (m + 1), f (seamRight n m b) := by
  rw [← (seamRightIndexEquiv n m).sum_comp]
  simp only [Fintype.sum_sum_type, seamRightIndexEquiv_inl, seamRightIndexEquiv_inr]

theorem southwestCount_int_sum {k : ℕ} (x : GridState k) (c r : Fin k) :
    (x.southwestCount c r : ℤ) = ∑ d : Fin k, if d < c ∧ x d < r then 1 else 0 := by
  classical
  simp only [GridState.southwestCount_def, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem seam_southwest_left (f : GridState (n + 1)) (g : GridState (m + 1))
    (c : Fin n) (r : Fin (n + 1)) :
    (seamState f g).southwestCount (seamLeft n m c.castSucc) (seamLeft n m r) =
      f.southwestCount c.castSucc r := by
  apply Nat.cast_injective (R := ℤ)
  rw [southwestCount_int_sum, southwestCount_int_sum, seam_sum]
  have hright : (∑ b : Fin (m + 1),
      if seamRight n m b < seamLeft n m c.castSucc ∧
        seamState f g (seamRight n m b) < seamLeft n m r then (1 : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    have hn : ¬seamRight n m b < seamLeft n m c.castSucc := by
      simp only [Fin.lt_def, seamRight_val, seamLeft_val, Fin.val_castSucc]
      omega
    simp [hn]
  rw [hright, add_zero]
  have hfactor := Fin.sum_univ_castSucc
    (fun d : Fin (n + 1) => if d < c.castSucc ∧ f d < r then (1 : ℤ) else 0)
  rw [hfactor]
  have hn : ¬Fin.last n < c.castSucc := by
    simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc]
    omega
  simp only [hn, false_and, ite_false, add_zero]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [seamState_left_castSucc, Fin.lt_def, seamLeft_val, Fin.val_castSucc]

theorem seam_southwest_right_high (f : GridState (n + 1)) (g : GridState (m + 1))
    (c r : Fin (m + 1)) (hr : r ≠ 0) :
    (seamState f g).southwestCount (seamRight n m c) (seamRight n m r) =
      n + g.southwestCount c r := by
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_add, southwestCount_int_sum, southwestCount_int_sum, seam_sum]
  have hleft : (∑ a : Fin n,
      if seamLeft n m a.castSucc < seamRight n m c ∧
        seamState f g (seamLeft n m a.castSucc) < seamRight n m r
      then (1 : ℤ) else 0) = n := by
    have hterm (a : Fin n) : seamLeft n m a.castSucc < seamRight n m c ∧
        seamState f g (seamLeft n m a.castSucc) < seamRight n m r := by
      rw [seamState_left_castSucc]
      simp only [Fin.lt_def, seamLeft_val, seamRight_val, Fin.val_castSucc]
      have hn : r.val ≠ 0 := fun h => hr (Fin.ext h)
      constructor <;> omega
    simp only [hterm, and_self, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  rw [hleft]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hcol : seamRight n m d < seamRight n m c ↔ d < c := by
    simp only [Fin.lt_def, seamRight_val]
    omega
  by_cases hgd : g d = 0
  · rw [seamState_right_of_zero _ _ _ hgd]
    have hlow : seamLeft n m (f (Fin.last n)) < seamRight n m r := by
      simp only [Fin.lt_def, seamLeft_val, seamRight_val]
      have hn : r.val ≠ 0 := fun h => hr (Fin.ext h)
      omega
    have hpos : (0 : Fin (m + 1)) < r := Fin.pos_iff_ne_zero.mpr hr
    simp only [hcol, hlow, hgd, hpos, and_true]
  · rw [seamState_right_of_ne_zero _ _ _ hgd]
    have hrows : seamRight n m (g d) < seamRight n m r ↔ g d < r := by
      simp only [Fin.lt_def, seamRight_val]
      omega
    simp only [hcol, hrows]

theorem seam_right_row_lt_left_iff (f : GridState (n + 1)) (g : GridState (m + 1))
    (c : Fin (m + 1)) (r : Fin (n + 1)) :
    seamState f g (seamRight n m c) < seamLeft n m r ↔
      g c = 0 ∧ f (Fin.last n) < r := by
  by_cases hc : g c = 0
  · rw [seamState_right_of_zero _ _ _ hc]
    simp only [hc, true_and, Fin.lt_def, seamLeft_val]
  · rw [seamState_right_of_ne_zero _ _ _ hc]
    simp only [hc, false_and, iff_false, Fin.lt_def, seamRight_val, seamLeft_val]
    have hn : (g c).val ≠ 0 := fun h => hc (Fin.ext h)
    omega

theorem seam_southwest_right_low (f : GridState (n + 1)) (g : GridState (m + 1))
    (c : Fin (m + 1)) (r : Fin (n + 1)) :
    (seamState f g).southwestCount (seamRight n m c) (seamLeft n m r) =
      f.southwestCount (Fin.last n) r +
        if g.toPerm.symm 0 < c ∧ f (Fin.last n) < r then 1 else 0 := by
  classical
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_add, southwestCount_int_sum, southwestCount_int_sum, seam_sum]
  have hleft : (∑ a : Fin n,
      if seamLeft n m a.castSucc < seamRight n m c ∧
        seamState f g (seamLeft n m a.castSucc) < seamLeft n m r
      then (1 : ℤ) else 0) =
        ∑ a : Fin (n + 1), if a < Fin.last n ∧ f a < r then 1 else 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [lt_self_iff_false, false_and, ite_false, add_zero]
    apply Finset.sum_congr rfl
    intro a ha
    have hac : seamLeft n m a.castSucc < seamRight n m c := by
      simp only [Fin.lt_def, seamLeft_val, seamRight_val, Fin.val_castSucc]
      omega
    simp only [seamState_left_castSucc, hac, true_and,
      Fin.lt_def, seamLeft_val, Fin.val_castSucc, Fin.val_last]
    simp only [a.isLt, true_and]
  rw [hleft]
  congr 1
  have hzero (d : Fin (m + 1)) : g d = 0 ↔ d = g.toPerm.symm 0 := by
    constructor
    · intro h
      exact g.toPerm.injective (h.trans (g.toPerm.apply_symm_apply 0).symm)
    · rintro rfl
      exact g.toPerm.apply_symm_apply 0
  have hterm (d : Fin (m + 1)) :
      (if seamRight n m d < seamRight n m c ∧
          seamState f g (seamRight n m d) < seamLeft n m r
        then (1 : ℤ) else 0) =
      if d = g.toPerm.symm 0 then
        (if g.toPerm.symm 0 < c ∧ f (Fin.last n) < r then 1 else 0) else 0 := by
    simp only [seam_right_row_lt_left_iff, hzero]
    by_cases hd : d = g.toPerm.symm 0
    · subst d
      simp only [Fin.lt_def, seamRight_val, true_and, ite_true]
      simp only [Nat.add_lt_add_iff_left]
    · simp [hd]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem I_int_sum_southwest {k : ℕ} (f x : GridState k) :
    (GridPoint.I f.pointSet x.pointSet : ℤ) =
      ∑ c : Fin k, (f.southwestCount c (x c) : ℤ) := by
  classical
  rw [GridState.I_pointSet_eq_card, Finset.card_filter, Fintype.sum_prod_type,
    Finset.sum_comm, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    southwestCount_int_sum]

/-- The sole extra pair in the strict southwest count across the seam. -/
def seamPairCountDefect (f x : GridState (n + 1)) (g z : GridState (m + 1)) : ℕ :=
  if f (Fin.last n) < x (Fin.last n) ∧ g.toPerm.symm 0 < z.toPerm.symm 0 then 1 else 0

theorem seamPairCountDefect_le_one (f x : GridState (n + 1))
    (g z : GridState (m + 1)) : seamPairCountDefect f x g z ≤ 1 := by
  unfold seamPairCountDefect
  split_ifs <;> omega

theorem seam_I (f x : GridState (n + 1)) (g z : GridState (m + 1)) :
    (GridPoint.I (seamState f g).pointSet (seamState x z).pointSet : ℤ) =
      (GridPoint.I f.pointSet x.pointSet : ℤ) + GridPoint.I g.pointSet z.pointSet +
        (n : ℤ) * m + seamPairCountDefect f x g z := by
  classical
  let d : Fin (m + 1) := z.toPerm.symm 0
  let a : Fin (n + 1) := x (Fin.last n)
  let e : ℤ := seamPairCountDefect f x g z
  have hzero (j : Fin (m + 1)) : z j = 0 ↔ j = d := by
    constructor
    · intro h
      exact z.toPerm.injective (h.trans (z.toPerm.apply_symm_apply 0).symm)
    · rintro rfl
      exact z.toPerm.apply_symm_apply 0
  have hswzero (j : Fin (m + 1)) : g.southwestCount j 0 = 0 := by
    simp [GridState.southwestCount_def]
  have hright (j : Fin (m + 1)) :
      ((seamState f g).southwestCount (seamRight n m j)
        (seamState x z (seamRight n m j)) : ℤ) =
      (n + (g.southwestCount j (z j) : ℤ)) +
        if j = d then (f.southwestCount (Fin.last n) a : ℤ) - n + e else 0 := by
    by_cases hz : z j = 0
    · have hj := (hzero j).mp hz
      rw [seamState_right_of_zero _ _ _ hz, seam_southwest_right_low, hz, hswzero]
      have he : (if g.toPerm.symm 0 < j ∧ f (Fin.last n) < x (Fin.last n)
          then (1 : ℕ) else 0) = seamPairCountDefect f x g z := by
        simp only [seamPairCountDefect, hj, d, and_comm]
      rw [he, Nat.cast_add, if_pos hj]
      dsimp only [a, e]
      ring
    · rw [seamState_right_of_ne_zero _ _ _ hz, seam_southwest_right_high _ _ _ _ hz,
        Nat.cast_add, if_neg (fun h => hz ((hzero j).mpr h)), add_zero]
  have hleft : (∑ c : Fin n,
      ((seamState f g).southwestCount (seamLeft n m c.castSucc)
        (seamState x z (seamLeft n m c.castSucc)) : ℤ)) =
      ∑ c : Fin n, (f.southwestCount c.castSucc (x c.castSucc) : ℤ) := by
    simp only [seamState_left_castSucc, seam_southwest_left]
  have hfx := I_int_sum_southwest f x
  rw [Fin.sum_univ_castSucc] at hfx
  have hgz := I_int_sum_southwest g z
  rw [I_int_sum_southwest, seam_sum, hleft]
  simp only [hright, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hfx, hgz]
  dsimp only [a, e]
  push_cast
  ring

theorem seam_I_self (x : GridState (n + 1)) (z : GridState (m + 1)) :
    (GridPoint.I (seamState x z).pointSet (seamState x z).pointSet : ℤ) =
      (GridPoint.I x.pointSet x.pointSet : ℤ) + GridPoint.I z.pointSet z.pointSet +
        (n : ℤ) * m := by
  simp only [seam_I, seamPairCountDefect, lt_self_iff_false, false_and, ite_false,
    Nat.cast_zero, add_zero]

private theorem two_sum_fin (k : ℕ) :
    2 * (∑ c : Fin k, (c.val : ℤ)) = (k : ℤ) * ((k : ℤ) - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The centered marking pairing reduces to one directed southwest count. -/
theorem JNumCenter_int_eq (x f : GridState n) :
    (GridPoint.JNumCenter x.pointSet f.pointSet : ℤ) =
      n + 2 * (GridPoint.I f.pointSet x.pointSet : ℤ) := by
  have hrow : (∑ c : Fin n, ((x c).val : ℤ)) = ∑ c : Fin n, (c.val : ℤ) :=
    Equiv.sum_comp x.toPerm (fun c : Fin n => (c.val : ℤ))
  rw [GridState.JNumCenter_pointSet_eq_sum_southwestCount, I_int_sum_southwest]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hrow]
  have hs := two_sum_fin n
  nlinarith

end OnLeConjecture.KnotFloer.GridFull

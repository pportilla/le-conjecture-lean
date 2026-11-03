/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.ExteriorSignedBraid

/-!
# Layered braid words

This module provides the word combinatorics behind the finite event relations of Section 3 of
the written proof of Statement E (`statement-E-complete-proof.tex`, subsection "Why the
configuration homotopies give finite word relations").

Consider `n + 1` strands at pairwise distinct heights, listed by position from left to right by
a height sequence `c : Fin (n + 1) → α`. When the strands move horizontally at fixed heights,
the configuration space is contractible, so the braid of such a motion depends only on its
initial and final orders. The *layered word* `layeredWord (n + 1) c` is an explicit signed word
for the motion from the reference order (heights decreasing from left to right) to the order
`c`: the lowest strand is moved last, from the right end to its position, passing below all the
other strands (`descRun`). The main results are:

* `layeredWord_swap`: exchanging the strands at positions `i` and `i + 1` appends the single
  letter `σ_i^{ε}` up to `SignedBraidEquiv`, where `ε = +1` when the strand that moves to the
  left is the higher one (`exchangeSign`).
* `layeredTransition_congr`: the transition word `layeredWord(c ∘ π)⁻¹ layeredWord(c ∘ ρ)`
  between two orders depends, up to `SignedBraidEquiv`, only on the relative heights of the
  pairs of strands whose order differs between `π` and `ρ`.
* `layeredWord_comp_permutation`: along a positive word `r`, the layered word changes by the
  letters of `r` with the signs determined by the heights (`signedTransition`).

The proof of `layeredWord_swap` is an induction on the number of strands. It uses only free
cancellation, far commutation, and the two braid relations `a⁻¹b⁻¹a⁻¹ = b⁻¹a⁻¹b⁻¹` and
`ab⁻¹a⁻¹ = b⁻¹a⁻¹b` (`braid_neg`, `braid_mixed`), which are derived from the positive braid
relation by free cancellation. No presentation of a fundamental group is used.

The module also contains the general congruence and cancellation lemmas for `SignedBraidEquiv`
and `SignedBraidConj` used later.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory

open SignedAdjacentWord Function

variable {m : ℕ}

/-! ### Congruence and cancellation -/

namespace SignedBraidStep

theorem append_left {u v : SignedAdjacentWord m} (h : SignedBraidStep u v)
    (p : SignedAdjacentWord m) : SignedBraidStep (p ++ u) (p ++ v) := by
  cases h with
  | cancel u v i e =>
    simpa only [List.append_assoc] using SignedBraidStep.cancel (p ++ u) v i e
  | far u v i j e f h =>
    simpa only [List.append_assoc] using SignedBraidStep.far (p ++ u) v i j e f h
  | braid u v i j h =>
    simpa only [List.append_assoc] using SignedBraidStep.braid (p ++ u) v i j h

theorem append_right {u v : SignedAdjacentWord m} (h : SignedBraidStep u v)
    (q : SignedAdjacentWord m) : SignedBraidStep (u ++ q) (v ++ q) := by
  cases h with
  | cancel u v i e =>
    simpa only [List.append_assoc, List.cons_append] using SignedBraidStep.cancel u (v ++ q) i e
  | far u v i j e f h =>
    simpa only [List.append_assoc, List.cons_append] using
      SignedBraidStep.far u (v ++ q) i j e f h
  | braid u v i j h =>
    simpa only [List.append_assoc, List.cons_append] using
      SignedBraidStep.braid u (v ++ q) i j h

end SignedBraidStep

namespace SignedBraidEquiv

theorem refl (u : SignedAdjacentWord m) : SignedBraidEquiv u u := Relation.EqvGen.refl u

theorem symm {u v : SignedAdjacentWord m} (h : SignedBraidEquiv u v) : SignedBraidEquiv v u :=
  Relation.EqvGen.symm _ _ h

theorem trans {u v w : SignedAdjacentWord m} (h₁ : SignedBraidEquiv u v)
    (h₂ : SignedBraidEquiv v w) : SignedBraidEquiv u w :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

theorem of_step {u v : SignedAdjacentWord m} (h : SignedBraidStep u v) : SignedBraidEquiv u v :=
  Relation.EqvGen.rel _ _ h

theorem of_eq {u v : SignedAdjacentWord m} (h : u = v) : SignedBraidEquiv u v := h ▸ refl u

theorem append_left {u v : SignedAdjacentWord m} (h : SignedBraidEquiv u v)
    (p : SignedAdjacentWord m) : SignedBraidEquiv (p ++ u) (p ++ v) := by
  induction h with
  | rel _ _ h => exact of_step (h.append_left p)
  | refl => exact refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem append_right {u v : SignedAdjacentWord m} (h : SignedBraidEquiv u v)
    (q : SignedAdjacentWord m) : SignedBraidEquiv (u ++ q) (v ++ q) := by
  induction h with
  | rel _ _ h => exact of_step (h.append_right q)
  | refl => exact refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem append {u u' v v' : SignedAdjacentWord m} (h₁ : SignedBraidEquiv u u')
    (h₂ : SignedBraidEquiv v v') : SignedBraidEquiv (u ++ v) (u' ++ v') :=
  (h₁.append_right v).trans (h₂.append_left u')

theorem cons {u v : SignedAdjacentWord m} (h : SignedBraidEquiv u v) (a : Fin (m - 1) × ℤˣ) :
    SignedBraidEquiv (a :: u) (a :: v) := by
  simpa using h.append_left [a]

/-- Free cancellation of `σ_i^e σ_i^{-e}` at the front of a word. -/
theorem cancel_front (i : Fin (m - 1)) (e : ℤˣ) (v : SignedAdjacentWord m) :
    SignedBraidEquiv ((i, e) :: (i, -e) :: v) v := by
  simpa using of_step (SignedBraidStep.cancel [] v i e)

/-- Free cancellation of `σ_i^{-e} σ_i^{e}` at the front of a word. -/
theorem cancel_front' (i : Fin (m - 1)) (e : ℤˣ) (v : SignedAdjacentWord m) :
    SignedBraidEquiv ((i, -e) :: (i, e) :: v) v := by
  simpa using cancel_front i (-e) v

/-- Free cancellation inside a word. -/
theorem cancel_mid (u v : SignedAdjacentWord m) (i : Fin (m - 1)) (e : ℤˣ) :
    SignedBraidEquiv (u ++ (i, e) :: (i, -e) :: v) (u ++ v) :=
  of_step (SignedBraidStep.cancel u v i e)

theorem cancel_mid' (u v : SignedAdjacentWord m) (i : Fin (m - 1)) (e : ℤˣ) :
    SignedBraidEquiv (u ++ (i, -e) :: (i, e) :: v) (u ++ v) := by
  simpa using cancel_mid u v i (-e)

end SignedBraidEquiv

namespace SignedAdjacentWord

@[simp] theorem inv_inv (w : SignedAdjacentWord m) : inv (inv w) = w := by
  simp [inv, List.map_reverse, Function.comp_def]

theorem inv_append (u v : SignedAdjacentWord m) : inv (u ++ v) = inv v ++ inv u := by
  simp [inv]

@[simp] theorem inv_singleton (a : Fin (m - 1) × ℤˣ) : inv [a] = [(a.1, -a.2)] := by
  simp [inv]

end SignedAdjacentWord

namespace SignedBraidEquiv

/-- A word followed by its inverse is trivial. -/
theorem append_inv_self (w : SignedAdjacentWord m) : SignedBraidEquiv (w ++ inv w) [] := by
  induction w with
  | nil => exact refl _
  | cons a w ih =>
    rw [inv_cons]
    have h1 : SignedBraidEquiv (a :: w ++ (inv w ++ [(a.1, -a.2)])) ([a] ++ [(a.1, -a.2)]) := by
      have := (ih.append_left [a]).append_right [(a.1, -a.2)]
      simpa only [List.singleton_append, List.cons_append, List.append_assoc,
        List.nil_append] using this
    refine h1.trans ?_
    simpa using cancel_front a.1 a.2 []

/-- The inverse of a word followed by the word is trivial. -/
theorem inv_append_self (w : SignedAdjacentWord m) : SignedBraidEquiv (inv w ++ w) [] := by
  simpa using append_inv_self (inv w)

/-- Cancellation of `w w⁻¹` inside a word. -/
theorem cancel_inv_mid (u w v : SignedAdjacentWord m) :
    SignedBraidEquiv (u ++ (w ++ inv w) ++ v) (u ++ v) := by
  simpa using ((append_inv_self w).append_left u).append_right v

theorem cancel_inv_mid' (u w v : SignedAdjacentWord m) :
    SignedBraidEquiv (u ++ (inv w ++ w) ++ v) (u ++ v) := by
  simpa using ((inv_append_self w).append_left u).append_right v

/-- Two transition words with a common middle compose. -/
theorem transition_comp (a b c : SignedAdjacentWord m) :
    SignedBraidEquiv ((inv a ++ b) ++ (inv b ++ c)) (inv a ++ c) := by
  simpa [List.append_assoc] using cancel_inv_mid (inv a) b c

/-- A letter commutes past a word whose letters are all far from it. -/
theorem far_past (a : Fin (m - 1) × ℤˣ) (w : SignedAdjacentWord m)
    (hw : ∀ b ∈ w, a.1.val + 2 ≤ b.1.val ∨ b.1.val + 2 ≤ a.1.val) :
    SignedBraidEquiv (a :: w) (w ++ [a]) := by
  induction w with
  | nil => exact refl _
  | cons b w ih =>
    have hb := hw b (List.mem_cons_self ..)
    have hstep : SignedBraidEquiv (a :: b :: w) (b :: a :: w) := by
      simpa using of_step (SignedBraidStep.far [] w a.1 b.1 a.2 b.2 hb)
    refine hstep.trans ?_
    simpa using (ih fun c hc => hw c (List.mem_cons_of_mem _ hc)).cons b

/-- The positive braid relation as an equivalence of three-letter words. -/
theorem braid_pos (i j : Fin (m - 1)) (h : j.val = i.val + 1) :
    SignedBraidEquiv [(i, 1), (j, 1), (i, 1)] [(j, 1), (i, 1), (j, 1)] := by
  simpa using of_step (SignedBraidStep.braid [] [] i j h)

/-- The negative braid relation `a⁻¹b⁻¹a⁻¹ = b⁻¹a⁻¹b⁻¹`, derived from `aba = bab` by free
cancellation. -/
theorem braid_neg (i j : Fin (m - 1)) (h : j.val = i.val + 1) :
    SignedBraidEquiv [(i, -1), (j, -1), (i, -1)] [(j, -1), (i, -1), (j, -1)] := by
  -- `b⁻¹a⁻¹b⁻¹ (b a b) a⁻¹b⁻¹a⁻¹` is equivalent to both sides.
  have hleft : SignedBraidEquiv
      ([(j, -1), (i, -1), (j, -1)] ++ [(j, 1), (i, 1), (j, 1)] ++ [(i, -1), (j, -1), (i, -1)])
      [(i, -1), (j, -1), (i, -1)] := by
    have h1 := cancel_mid [(j, -1), (i, -1)] ([(i, 1), (j, 1)] ++ [(i, -1), (j, -1), (i, -1)])
      j (-1)
    have h2 := cancel_mid [(j, -1)] ([(j, 1)] ++ [(i, -1), (j, -1), (i, -1)]) i (-1)
    have h3 := cancel_mid [] [(i, -1), (j, -1), (i, -1)] j (-1)
    simp only [neg_neg] at h1 h2 h3
    exact h1.trans (h2.trans h3)
  have hright : SignedBraidEquiv
      ([(j, -1), (i, -1), (j, -1)] ++ [(i, 1), (j, 1), (i, 1)] ++ [(i, -1), (j, -1), (i, -1)])
      [(j, -1), (i, -1), (j, -1)] := by
    have h1 := cancel_mid [(j, -1), (i, -1), (j, -1), (i, 1), (j, 1)] [(j, -1), (i, -1)] i 1
    have h2 := cancel_mid [(j, -1), (i, -1), (j, -1), (i, 1)] [(i, -1)] j 1
    have h3 := cancel_mid [(j, -1), (i, -1), (j, -1)] [] i 1
    simp only [List.append_nil] at h1 h2 h3
    simpa using h1.trans (h2.trans h3)
  have hmid := ((braid_pos i j h).symm.append_left [(j, -1), (i, -1), (j, -1)]).append_right
    [(i, -1), (j, -1), (i, -1)]
  exact hleft.symm.trans (hmid.trans hright)

/-- The mixed braid relation `a b⁻¹ a⁻¹ = b⁻¹ a⁻¹ b`, derived from `aba = bab` by free
cancellation. -/
theorem braid_mixed (i j : Fin (m - 1)) (h : j.val = i.val + 1) :
    SignedBraidEquiv [(i, 1), (j, -1), (i, -1)] [(j, -1), (i, -1), (j, 1)] := by
  -- `b⁻¹a⁻¹ (a b a) b⁻¹ a⁻¹` is equivalent to both sides.
  have hleft : SignedBraidEquiv
      ([(j, -1), (i, -1)] ++ [(i, 1), (j, 1), (i, 1)] ++ [(j, -1), (i, -1)])
      [(i, 1), (j, -1), (i, -1)] := by
    have h1 := cancel_mid [(j, -1)] ([(j, 1), (i, 1)] ++ [(j, -1), (i, -1)]) i (-1)
    have h2 := cancel_mid [] ([(i, 1)] ++ [(j, -1), (i, -1)]) j (-1)
    simp only [neg_neg] at h1 h2
    simpa using h1.trans h2
  have hright : SignedBraidEquiv
      ([(j, -1), (i, -1)] ++ [(j, 1), (i, 1), (j, 1)] ++ [(j, -1), (i, -1)])
      [(j, -1), (i, -1), (j, 1)] := by
    have h1 := cancel_mid [(j, -1), (i, -1), (j, 1), (i, 1)] [(i, -1)] j 1
    have h2 := cancel_mid [(j, -1), (i, -1), (j, 1)] [] i 1
    simp only [List.append_nil] at h1 h2
    simpa using h1.trans h2
  have hmid := ((braid_pos i j h).append_left [(j, -1), (i, -1)]).append_right
    [(j, -1), (i, -1)]
  exact hleft.symm.trans (hmid.trans hright)

/-- The braid relation `a^ε b⁻¹ a⁻¹ = b⁻¹ a⁻¹ b^ε` for both signs `ε`. -/
theorem braid_slide (i j : Fin (m - 1)) (h : j.val = i.val + 1) (e : ℤˣ) :
    SignedBraidEquiv [(i, e), (j, -1), (i, -1)] [(j, -1), (i, -1), (j, e)] := by
  rcases Int.units_eq_one_or e with rfl | rfl
  · exact braid_mixed i j h
  · exact braid_neg i j h

end SignedBraidEquiv

namespace SignedBraidConj

theorem refl (u : SignedAdjacentWord m) : SignedBraidConj u u := Relation.EqvGen.refl u

theorem symm {u v : SignedAdjacentWord m} (h : SignedBraidConj u v) : SignedBraidConj v u :=
  Relation.EqvGen.symm _ _ h

theorem trans {u v w : SignedAdjacentWord m} (h₁ : SignedBraidConj u v)
    (h₂ : SignedBraidConj v w) : SignedBraidConj u w :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

/-- Cyclic rotation of a whole block of letters. -/
theorem rotate (u v : SignedAdjacentWord m) : SignedBraidConj (u ++ v) (v ++ u) := by
  induction v using List.reverseRecOn generalizing u with
  | nil => simpa using refl u
  | append_singleton v a ih =>
    have h1 : SignedBraidConj (u ++ (v ++ [a])) (a :: (u ++ v)) := by
      rw [← List.append_assoc]
      exact Relation.EqvGen.rel _ _ (SignedBraidConjStep.rotate (u ++ v) a)
    have h2 : SignedBraidConj ((a :: u) ++ v) (v ++ (a :: u)) := ih (a :: u)
    simpa using h1.trans h2

/-- A conjugate `c X c⁻¹` is conjugate to `X`. -/
theorem conjugate_left (c X : SignedAdjacentWord m) : SignedBraidConj (c ++ X ++ inv c) X := by
  have h1 : SignedBraidConj ((c ++ X) ++ inv c) (inv c ++ (c ++ X)) := rotate _ _
  have h2 : SignedBraidEquiv (inv c ++ (c ++ X)) X := by
    simpa [List.append_assoc] using SignedBraidEquiv.cancel_inv_mid' [] c X
  exact h1.trans h2.toConj

/-- If `A c ≡ c B` in the braid group, then `A` and `B` are conjugate. -/
theorem of_equiv_conjugate {A B c : SignedAdjacentWord m}
    (h : SignedBraidEquiv (A ++ c) (c ++ B)) : SignedBraidConj A B := by
  have h1 : SignedBraidEquiv A (c ++ B ++ inv c) := by
    have h2 := h.append_right (inv c)
    have h3 : SignedBraidEquiv (A ++ c ++ inv c) A := by
      simpa using SignedBraidEquiv.cancel_inv_mid A c []
    exact h3.symm.trans h2
  exact h1.toConj.trans (conjugate_left c B)

end SignedBraidConj

/-! ### Layered words -/

section Layered

variable {α : Type*} [LinearOrder α]

/-- The sign of the exchange of two adjacent strands with heights `x` (left) and `y` (right):
`+1` when the strand moving to the left, of height `y`, is the higher one. -/
def exchangeSign (x y : α) : ℤˣ := if x < y then 1 else -1

/-- A word on `n` strands, viewed on the first `n` of `n + 1` strands. -/
def liftWordSucc (n : ℕ) (w : SignedAdjacentWord n) : SignedAdjacentWord (n + 1) :=
  w.map fun a => ((Fin.castLE (Nat.sub_le n 1) a.1 : Fin n), a.2)

@[simp] theorem liftWordSucc_nil (n : ℕ) : liftWordSucc n [] = [] := rfl

@[simp] theorem liftWordSucc_append (n : ℕ) (u v : SignedAdjacentWord n) :
    liftWordSucc n (u ++ v) = liftWordSucc n u ++ liftWordSucc n v := by
  simp [liftWordSucc]

theorem liftWordSucc_inv (n : ℕ) (w : SignedAdjacentWord n) :
    liftWordSucc n (inv w) = inv (liftWordSucc n w) := by
  simp [liftWordSucc, inv, List.map_reverse]

theorem SignedBraidStep.liftWordSucc {n : ℕ} {u v : SignedAdjacentWord n}
    (h : SignedBraidStep u v) : SignedBraidStep (liftWordSucc n u) (liftWordSucc n v) := by
  cases h with
  | cancel u v i e =>
    simpa [OnLeConjecture.KnotTheory.liftWordSucc] using
      SignedBraidStep.cancel (OnLeConjecture.KnotTheory.liftWordSucc n u)
        (OnLeConjecture.KnotTheory.liftWordSucc n v) (Fin.castLE (Nat.sub_le n 1) i : Fin n) e
  | far u v i j e f h =>
    simpa [OnLeConjecture.KnotTheory.liftWordSucc] using
      SignedBraidStep.far (OnLeConjecture.KnotTheory.liftWordSucc n u)
        (OnLeConjecture.KnotTheory.liftWordSucc n v) (Fin.castLE (Nat.sub_le n 1) i : Fin n)
        (Fin.castLE (Nat.sub_le n 1) j : Fin n) e f (by simpa using h)
  | braid u v i j h =>
    simpa [OnLeConjecture.KnotTheory.liftWordSucc] using
      SignedBraidStep.braid (OnLeConjecture.KnotTheory.liftWordSucc n u)
        (OnLeConjecture.KnotTheory.liftWordSucc n v) (Fin.castLE (Nat.sub_le n 1) i : Fin n)
        (Fin.castLE (Nat.sub_le n 1) j : Fin n) (by simpa using h)

theorem SignedBraidEquiv.liftWordSucc {n : ℕ} {u v : SignedAdjacentWord n}
    (h : SignedBraidEquiv u v) :
    SignedBraidEquiv (liftWordSucc n u) (liftWordSucc n v) := by
  induction h with
  | rel _ _ h => exact SignedBraidEquiv.of_step h.liftWordSucc
  | refl => exact SignedBraidEquiv.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- The descending run `σ_{hi-1}⁻¹ σ_{hi-2}⁻¹ ⋯ σ_{lo}⁻¹` on `n + 1` strands (letters at
least `n` are omitted). -/
def descRun (n : ℕ) (hi lo : ℕ) : SignedAdjacentWord (n + 1) :=
  if h : lo < hi ∧ lo < n then
    descRun n hi (lo + 1) ++ ([(⟨lo, by omega⟩, -1)] : SignedAdjacentWord (n + 1))
  else []
termination_by hi - lo

theorem descRun_of_lt {n hi lo : ℕ} (h : lo < hi) (hn : lo < n) :
    descRun n hi lo =
      descRun n hi (lo + 1) ++ ([(⟨lo, by omega⟩, -1)] : SignedAdjacentWord (n + 1)) := by
  rw [descRun, dif_pos ⟨h, hn⟩]

theorem descRun_of_le {n hi lo : ℕ} (h : hi ≤ lo) : descRun n hi lo = [] := by
  rw [descRun, dif_neg (by omega)]

theorem descRun_split {n hi mid lo : ℕ} (hlm : lo ≤ mid) (hmh : mid ≤ hi) (hhn : hi ≤ n) :
    descRun n hi lo = descRun n hi mid ++ descRun n mid lo := by
  induction h : mid - lo generalizing lo with
  | zero =>
    have : lo = mid := by omega
    subst this
    rw [descRun_of_le (le_refl _), List.append_nil]
  | succ k ih =>
    have hlt : lo < mid := by omega
    rw [descRun_of_lt (by omega) (by omega), descRun_of_lt (hi := mid) hlt (by omega),
      ih (lo := lo + 1) (by omega) (by omega), List.append_assoc]

theorem mem_descRun {n hi lo : ℕ} {b : Fin (n + 1 - 1) × ℤˣ} (hb : b ∈ descRun n hi lo) :
    lo ≤ b.1.val ∧ b.1.val < hi ∧ b.2 = -1 := by
  induction h : hi - lo generalizing lo with
  | zero => rw [descRun_of_le (by omega)] at hb; simp at hb
  | succ k ih =>
    by_cases hn : lo < n
    · rw [descRun_of_lt (by omega) hn] at hb
      rcases List.mem_append.mp hb with hb | hb
      · have := ih (lo := lo + 1) hb (by omega); exact ⟨by omega, this.2.1, this.2.2⟩
      · simp only [List.mem_singleton] at hb; subst hb; simp; omega
    · rw [descRun, dif_neg (by omega)] at hb; simp at hb

/-- A letter far below a descending run commutes past it. -/
theorem descRun_far_below {n hi lo : ℕ} (i : Fin (n + 1 - 1)) (e : ℤˣ) (h : i.val + 2 ≤ lo) :
    SignedBraidEquiv (m := n + 1) ((i, e) :: descRun n hi lo)
      (descRun n hi lo ++ ([(i, e)] : SignedAdjacentWord (n + 1))) :=
  SignedBraidEquiv.far_past _ _ fun _ hb => Or.inl ((mem_descRun hb).1.trans' h)

/-- A letter far above a descending run commutes past it. -/
theorem descRun_far_above {n hi lo : ℕ} (i : Fin (n + 1 - 1)) (e : ℤˣ) (h : hi + 1 ≤ i.val) :
    SignedBraidEquiv (m := n + 1) ((i, e) :: descRun n hi lo)
      (descRun n hi lo ++ ([(i, e)] : SignedAdjacentWord (n + 1))) :=
  SignedBraidEquiv.far_past _ _ fun b hb => Or.inr (by
    have := (mem_descRun hb).2.1; change b.1.val + 2 ≤ i.val; omega)

/-- Sliding the letter `σ_{i-1}^e` through the run `σ_{n-1}⁻¹ ⋯ σ_p⁻¹` with `p < i` turns it
into `σ_i^e`. -/
theorem descRun_slide {n p : ℕ} (i i' : Fin (n + 1 - 1)) (hi' : i'.val + 1 = i.val)
    (hp : p ≤ i'.val) (e : ℤˣ) :
    SignedBraidEquiv (m := n + 1) ((i', e) :: descRun n n p)
      (descRun n n p ++ ([(i, e)] : SignedAdjacentWord (n + 1))) := by
  have hin : i.val < n := i.isLt
  have hsplit : descRun n n p = descRun n n (i.val + 1) ++
      (([(i, -1), (i', -1)] : SignedAdjacentWord (n + 1)) ++ descRun n i'.val p) := by
    rw [descRun_split (mid := i.val + 1) (by omega) (by omega) le_rfl,
      descRun_split (n := n) (hi := i.val + 1) (mid := i'.val) (lo := p) hp (by omega)
        (by omega)]
    rw [descRun_of_lt (n := n) (hi := i.val + 1) (lo := i'.val) (by omega) (by omega),
      descRun_of_lt (n := n) (hi := i.val + 1) (lo := i'.val + 1) (by omega) (by omega),
      descRun_of_le (n := n) (hi := i.val + 1) (lo := i'.val + 1 + 1) (by omega)]
    have h1 : ((⟨i'.val + 1, by omega⟩ : Fin (n + 1 - 1))) = i := Fin.ext hi'
    simp only [h1, List.nil_append, List.cons_append]
  rw [hsplit]
  set A := descRun n n (i.val + 1)
  set B := descRun n i'.val p
  have hA : SignedBraidEquiv (m := n + 1) ((i', e) :: A)
      (A ++ ([(i', e)] : SignedAdjacentWord (n + 1))) :=
    descRun_far_below i' e (by omega)
  have hB : SignedBraidEquiv (m := n + 1) ((i, e) :: B)
      (B ++ ([(i, e)] : SignedAdjacentWord (n + 1))) :=
    descRun_far_above i e (by omega)
  have hbraid := SignedBraidEquiv.braid_slide (m := n + 1) i' i hi'.symm e
  have s1 : SignedBraidEquiv (m := n + 1)
      ((i', e) :: (A ++ (([(i, -1), (i', -1)] : SignedAdjacentWord (n + 1)) ++ B)))
      (A ++ (i', e) :: (i, -1) :: (i', -1) :: B) := by
    simpa using hA.append_right (([(i, -1), (i', -1)] : SignedAdjacentWord (n + 1)) ++ B)
  have s2 : SignedBraidEquiv (m := n + 1) (A ++ (i', e) :: (i, -1) :: (i', -1) :: B)
      (A ++ (i, -1) :: (i', -1) :: (i, e) :: B) := by
    simpa using (hbraid.append_left A).append_right B
  have s3 : SignedBraidEquiv (m := n + 1) (A ++ (i, -1) :: (i', -1) :: (i, e) :: B)
      (A ++ (i, -1) :: (i', -1) :: (B ++ ([(i, e)] : SignedAdjacentWord (n + 1)))) := by
    simpa using hB.append_left (A ++ ([(i, -1), (i', -1)] : SignedAdjacentWord (n + 1)))
  simpa using s1.trans (s2.trans s3)

/-- The position of the lowest strand of a height sequence. -/
noncomputable def lowestPos {n : ℕ} (c : Fin (n + 1) → α) : Fin (n + 1) :=
  Classical.choose (Finite.exists_min c)

theorem lowestPos_le {n : ℕ} (c : Fin (n + 1) → α) (q : Fin (n + 1)) :
    c (lowestPos c) ≤ c q :=
  Classical.choose_spec (Finite.exists_min c) q

theorem lowestPos_eq {n : ℕ} {c : Fin (n + 1) → α} (hc : Injective c) {p : Fin (n + 1)}
    (hp : ∀ q, c p ≤ c q) : lowestPos c = p :=
  hc (le_antisymm (lowestPos_le c p) (hp _))

/-- **The layered word** of a height sequence: a word for the horizontal motion at fixed
heights from the order with decreasing heights to the order `c`. The lowest strand is moved
last, from the right end to its position. -/
noncomputable def layeredWord : (n : ℕ) → (Fin n → α) → SignedAdjacentWord n
  | 0, _ => []
  | n + 1, c => liftWordSucc n (layeredWord n (c ∘ (lowestPos c).succAbove)) ++
      descRun n n (lowestPos c).val

theorem layeredWord_succ (n : ℕ) (c : Fin (n + 1) → α) :
    layeredWord (n + 1) c = liftWordSucc n (layeredWord n (c ∘ (lowestPos c).succAbove)) ++
      descRun n n (lowestPos c).val := rfl

theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (q : Fin n) :
    (p.succAbove q).val = if q.val < p.val then q.val else q.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h₁ h₂ h₂ <;> simp_all [Fin.lt_def]

/-- **Exchange of two adjacent strands.** Exchanging the strands at positions `i` and `i + 1`
appends `σ_i^{ε}` to the layered word, with `ε = exchangeSign (c i) (c (i + 1))`. -/
theorem layeredWord_swap : ∀ (n : ℕ) (c : Fin (n + 1) → α), Injective c → ∀ i : Fin n,
    SignedBraidEquiv (layeredWord (n + 1) (c ∘ ⇑(adjacentSwap (m := n + 1) i)))
      (layeredWord (n + 1) c ++
        ([(i, exchangeSign (c (adjacentLower (m := n + 1) i))
          (c (adjacentUpper (m := n + 1) i)))] : SignedAdjacentWord (n + 1))) := by
  intro n
  induction n with
  | zero => intro c _ i; exact i.elim0
  | succ n ih =>
    intro c hc i
    set p := lowestPos c with hpdef
    have hcs : Injective (c ∘ ⇑(adjacentSwap (m := n + 2) i)) := hc.comp (Equiv.injective _)
    have hp' : lowestPos (c ∘ ⇑(adjacentSwap (m := n + 2) i)) =
        adjacentSwap (m := n + 2) i p := by
      apply lowestPos_eq hcs
      intro q
      simp only [Function.comp_apply]
      have hinv : adjacentSwap (m := n + 2) i (adjacentSwap (m := n + 2) i p) = p := by
        rw [← Equiv.Perm.mul_apply, SignedAdjacentWord.adjacentSwap_mul_self,
          Equiv.Perm.one_apply]
      rw [hinv]
      exact lowestPos_le c _
    have hpmin : ∀ q, c p ≤ c q := lowestPos_le c
    rw [layeredWord_succ, layeredWord_succ (c := c), hp', ← hpdef]
    have hsval : (adjacentSwap (m := n + 2) i p).val =
        if p.val = i.val then i.val + 1 else if p.val = i.val + 1 then i.val else p.val :=
      adjacentSwap_apply_val i p
    rcases lt_trichotomy p.val i.val with hlt | heq | hgt
    · -- The lowest strand lies to the left of the exchanged pair.
      have hsp : adjacentSwap (m := n + 2) i p = p := by
        apply Fin.ext; rw [hsval]; split_ifs <;> omega
      rw [hsp]
      have hi1 : 1 ≤ i.val := by omega
      let i' : Fin n := ⟨i.val - 1, by omega⟩
      have hfun : (c ∘ ⇑(adjacentSwap (m := n + 2) i)) ∘ p.succAbove =
          (c ∘ p.succAbove) ∘ ⇑(adjacentSwap (m := n + 1) i') := by
        funext q
        simp only [Function.comp_apply]
        congr 1
        apply Fin.ext
        rw [adjacentSwap_apply_val, val_succAbove, val_succAbove, adjacentSwap_apply_val]
        simp only [i']
        split_ifs <;> omega
      have hlo : p.succAbove (adjacentLower (m := n + 1) i') = adjacentLower (m := n + 2) i := by
        apply Fin.ext; rw [val_succAbove]; simp only [i']; split_ifs <;> omega
      have hup : p.succAbove (adjacentUpper (m := n + 1) i') = adjacentUpper (m := n + 2) i := by
        apply Fin.ext; rw [val_succAbove]; simp only [i']; split_ifs <;> omega
      have hIH := ih (c ∘ p.succAbove) (hc.comp (Fin.succAbove_right_injective)) i'
      simp only [Function.comp_apply, hlo, hup] at hIH
      rw [hfun]
      have hlift := hIH.liftWordSucc
      rw [liftWordSucc_append] at hlift
      have hslide := descRun_slide (n := n + 1) (p := p.val) i
        (Fin.castLE (Nat.sub_le (n + 1) 1) i' : Fin (n + 1))
        (by change i.val - 1 + 1 = i.val; omega)
        (by change p.val ≤ i.val - 1; omega)
        (exchangeSign (c (adjacentLower (m := n + 2) i)) (c (adjacentUpper (m := n + 2) i)))
      have h1 := hlift.append_right (descRun (n + 1) (n + 1) p.val)
      refine h1.trans ?_
      simp only [liftWordSucc, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append]
      simpa only [List.append_assoc] using hslide.append_left _
    · -- The lowest strand is the left strand of the pair.
      have hsp : (adjacentSwap (m := n + 2) i p).val = i.val + 1 := by
        rw [hsval, if_pos heq]
      have hfun : (c ∘ ⇑(adjacentSwap (m := n + 2) i)) ∘
          (adjacentSwap (m := n + 2) i p).succAbove = c ∘ p.succAbove := by
        funext q
        simp only [Function.comp_apply]
        congr 1
        apply Fin.ext
        rw [adjacentSwap_apply_val, val_succAbove, val_succAbove, hsp]
        split_ifs <;> omega
      have hplo : p = adjacentLower (m := n + 2) i := Fin.ext heq
      have hsign : exchangeSign (c (adjacentLower (m := n + 2) i))
          (c (adjacentUpper (m := n + 2) i)) = 1 := by
        rw [exchangeSign, if_pos]
        rw [← hplo]
        refine lt_of_le_of_ne (hpmin _) fun h => ?_
        have := hc h
        rw [hplo] at this
        simp [Fin.ext_iff, adjacentLower, adjacentUpper] at this
      rw [hfun, hsp, hsign, descRun_of_lt (n := n + 1) (lo := p.val) (by omega) (by omega)]
      have hfin : ((⟨p.val, by omega⟩ : Fin (n + 1))) = i := Fin.ext heq
      rw [hfin]
      have hc := (SignedBraidEquiv.cancel_mid'
          (liftWordSucc (n + 1) (layeredWord (n + 1) (c ∘ p.succAbove)) ++
            descRun (n + 1) (n + 1) (p.val + 1)) [] i 1).symm
      rw [heq] at hc ⊢
      simpa [List.append_assoc] using hc
    · rcases Nat.lt_or_ge (i.val + 1) p.val with hgt' | hle
      · -- The lowest strand lies to the right of the exchanged pair.
        have hsp : adjacentSwap (m := n + 2) i p = p := by
          apply Fin.ext; rw [hsval]; split_ifs <;> omega
        rw [hsp]
        let i' : Fin n := ⟨i.val, by omega⟩
        have hfun : (c ∘ ⇑(adjacentSwap (m := n + 2) i)) ∘ p.succAbove =
            (c ∘ p.succAbove) ∘ ⇑(adjacentSwap (m := n + 1) i') := by
          funext q
          simp only [Function.comp_apply]
          congr 1
          apply Fin.ext
          rw [adjacentSwap_apply_val, val_succAbove, val_succAbove, adjacentSwap_apply_val]
          simp only [i']
          split_ifs <;> omega
        have hlo : p.succAbove (adjacentLower (m := n + 1) i') =
            adjacentLower (m := n + 2) i := by
          apply Fin.ext; rw [val_succAbove]; simp only [i']; split_ifs <;> omega
        have hup : p.succAbove (adjacentUpper (m := n + 1) i') =
            adjacentUpper (m := n + 2) i := by
          apply Fin.ext; rw [val_succAbove]; simp only [i']; split_ifs; omega
        have hIH := ih (c ∘ p.succAbove) (hc.comp (Fin.succAbove_right_injective)) i'
        simp only [Function.comp_apply, hlo, hup] at hIH
        rw [hfun]
        have hlift := hIH.liftWordSucc
        rw [liftWordSucc_append] at hlift
        have hcast : (Fin.castLE (Nat.sub_le (n + 1) 1) i' : Fin (n + 1)) = i := Fin.ext rfl
        have hfar := descRun_far_below (n := n + 1) (hi := n + 1) (lo := p.val) i
          (exchangeSign (c (adjacentLower (m := n + 2) i)) (c (adjacentUpper (m := n + 2) i)))
          (by omega)
        have h1 := hlift.append_right (descRun (n + 1) (n + 1) p.val)
        refine h1.trans ?_
        simp only [liftWordSucc, List.map_cons, List.map_nil, List.append_assoc,
          List.singleton_append, hcast]
        simpa only [List.append_assoc, liftWordSucc] using hfar.append_left _
      · -- The lowest strand is the right strand of the pair.
        have heq' : p.val = i.val + 1 := by omega
        have hsp : (adjacentSwap (m := n + 2) i p).val = i.val := by
          rw [hsval, if_neg (by omega), if_pos heq']
        have hfun : (c ∘ ⇑(adjacentSwap (m := n + 2) i)) ∘
            (adjacentSwap (m := n + 2) i p).succAbove = c ∘ p.succAbove := by
          funext q
          simp only [Function.comp_apply]
          congr 1
          apply Fin.ext
          rw [adjacentSwap_apply_val, val_succAbove, val_succAbove, hsp]
          split_ifs <;> omega
        have hpup : p = adjacentUpper (m := n + 2) i := Fin.ext heq'
        have hsign : exchangeSign (c (adjacentLower (m := n + 2) i))
            (c (adjacentUpper (m := n + 2) i)) = -1 := by
          rw [exchangeSign, if_neg]
          rw [← hpup]
          exact not_lt.mpr (hpmin _)
        rw [hfun, hsp, hsign, descRun_of_lt (n := n + 1) (lo := i.val) (by omega) (by omega)]
        have hfin : ((⟨i.val, by omega⟩ : Fin (n + 1))) = i := rfl
        rw [hfin, heq']
        exact SignedBraidEquiv.of_eq (by simp [List.append_assoc])


/-- The signed letters of the exchanges along a positive word `r`, starting from the order
`c`: each letter `σ_i` of `r` receives the sign `exchangeSign` of the strands it exchanges. -/
noncomputable def signedTransition {n : ℕ} (c : Fin (n + 1) → α) :
    PositiveAdjacentWord (n + 1) → SignedAdjacentWord (n + 1)
  | [] => []
  | i :: r => (i, exchangeSign (c (adjacentLower i)) (c (adjacentUpper i))) ::
      signedTransition (c ∘ ⇑(adjacentSwap i)) r

/-- Along a positive word `r`, the layered word changes by the signed letters of `r`. -/
theorem layeredWord_comp_permutation {n : ℕ} (c : Fin (n + 1) → α) (hc : Injective c)
    (r : PositiveAdjacentWord (n + 1)) :
    SignedBraidEquiv (layeredWord (n + 1) (c ∘ ⇑r.permutation))
      (layeredWord (n + 1) c ++ signedTransition c r) := by
  induction r generalizing c with
  | nil =>
    rw [PositiveAdjacentWord.permutation_nil, Equiv.Perm.coe_one, Function.comp_id]
    simpa [signedTransition] using SignedBraidEquiv.refl (layeredWord (n + 1) c)
  | cons i r ih =>
    rw [PositiveAdjacentWord.permutation_cons, Equiv.Perm.coe_mul, ← Function.comp_assoc]
    have h1 := ih (c ∘ ⇑(adjacentSwap i)) (hc.comp (Equiv.injective _))
    have h2 := (layeredWord_swap n c hc i).append_right
      (signedTransition (c ∘ ⇑(adjacentSwap i)) r)
    refine h1.trans (h2.trans (SignedBraidEquiv.of_eq ?_))
    simp [signedTransition, List.append_assoc]

/-- The pairs of strands whose relative order differs between the orders `π` and `ρ`
(position-to-label enumerations). -/
def invertedPairs {n : ℕ} (π ρ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun kl => π.symm kl.1 < π.symm kl.2 ∧ ρ.symm kl.2 < ρ.symm kl.1

theorem adjacentSwap_self_apply {n : ℕ} (i : Fin n) (x : Fin (n + 1)) :
    adjacentSwap (m := n + 1) i (adjacentSwap (m := n + 1) i x) = x := by
  rw [← Equiv.Perm.mul_apply, SignedAdjacentWord.adjacentSwap_mul_self, Equiv.Perm.one_apply]

theorem adjacentSwap_symm {n : ℕ} (i : Fin n) :
    (adjacentSwap (m := n + 1) i).symm = adjacentSwap (m := n + 1) i := by
  rw [← Equiv.Perm.inv_def, SignedAdjacentWord.adjacentSwap_inv]

/-- An adjacent exchange reverses the order of two positions only when they are the two
exchanged positions. -/
theorem adjacentSwap_lt_of_lt {n : ℕ} (i : Fin n) {a b : Fin (n + 1)}
    (h : adjacentSwap (m := n + 1) i a < adjacentSwap (m := n + 1) i b) (hba : b < a) :
    a = adjacentUpper (m := n + 1) i ∧ b = adjacentLower (m := n + 1) i := by
  rw [Fin.lt_def, adjacentSwap_apply_val, adjacentSwap_apply_val] at h
  rw [Fin.lt_def] at hba
  simp only [Fin.ext_iff, adjacentUpper, adjacentLower]
  split_ifs at h <;> omega

theorem eq_of_invertedPairs_empty {n : ℕ} {π ρ : Equiv.Perm (Fin (n + 1))}
    (h : ∀ i : Fin n, ρ.symm (π (adjacentLower (m := n + 1) i)) <
      ρ.symm (π (adjacentUpper (m := n + 1) i))) : π = ρ := by
  have hmono : StrictMono fun j => ρ.symm (π j) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact h i
  have hid := hmono.eq_id
  refine Equiv.ext fun j => ?_
  have := congrFun hid j
  simp only [id] at this
  calc π j = ρ (ρ.symm (π j)) := (Equiv.apply_symm_apply ρ _).symm
    _ = ρ j := by rw [this]

/-- **Transition congruence.** The transition word between the orders `π` and `ρ` depends,
up to `SignedBraidEquiv`, only on the relative heights of the pairs of strands whose order
differs between `π` and `ρ`. -/
theorem layeredTransition_congr {n : ℕ} {c c' : Fin (n + 1) → α} (hc : Injective c)
    (hc' : Injective c') (π ρ : Equiv.Perm (Fin (n + 1)))
    (hagree : ∀ k l, π.symm k < π.symm l → ρ.symm l < ρ.symm k → (c k < c l ↔ c' k < c' l)) :
    SignedBraidEquiv (inv (layeredWord (n + 1) (c ∘ ⇑π)) ++ layeredWord (n + 1) (c ∘ ⇑ρ))
      (inv (layeredWord (n + 1) (c' ∘ ⇑π)) ++ layeredWord (n + 1) (c' ∘ ⇑ρ)) := by
  induction hD : (invertedPairs π ρ).card using Nat.strong_induction_on generalizing π with
  | _ D ih =>
    by_cases hπρ : π = ρ
    · subst hπρ
      exact (SignedBraidEquiv.inv_append_self _).trans
        (SignedBraidEquiv.inv_append_self _).symm
    obtain ⟨i, hi⟩ : ∃ i : Fin n, ρ.symm (π (adjacentUpper (m := n + 1) i)) <
        ρ.symm (π (adjacentLower (m := n + 1) i)) := by
      by_contra hno
      simp only [not_exists, not_lt] at hno
      apply hπρ
      apply eq_of_invertedPairs_empty
      intro i
      refine lt_of_le_of_ne (hno i) fun he => ?_
      have := π.injective (ρ.symm.injective he)
      simp [Fin.ext_iff, adjacentLower, adjacentUpper] at this
    set π' := π * adjacentSwap (m := n + 1) i with hπ'
    have hsymm : ∀ x, π'.symm x = adjacentSwap (m := n + 1) i (π.symm x) := by
      intro x
      rw [hπ', Equiv.Perm.mul_def, Equiv.symm_trans_apply, adjacentSwap_symm]
    -- The inverted pairs of `π'` form a proper subset of those of `π`.
    have hsub : ∀ x y, π'.symm x < π'.symm y → ρ.symm y < ρ.symm x →
        π.symm x < π.symm y := by
      intro x y hxy hρ
      rw [hsymm, hsymm] at hxy
      by_contra hn
      have hne : π.symm x ≠ π.symm y := fun he => by rw [he] at hxy; exact lt_irrefl _ hxy
      have hlt : π.symm y < π.symm x := lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hne)
      obtain ⟨hx, hy⟩ := adjacentSwap_lt_of_lt i hxy hlt
      have hx' : x = π (adjacentUpper (m := n + 1) i) := by rw [← hx, Equiv.apply_symm_apply]
      have hy' : y = π (adjacentLower (m := n + 1) i) := by rw [← hy, Equiv.apply_symm_apply]
      rw [hx', hy'] at hρ
      exact lt_asymm hi hρ
    have hcard : (invertedPairs π' ρ).card < D := by
      rw [← hD]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨(π (adjacentLower (m := n + 1) i), π (adjacentUpper (m := n + 1) i)), ?_, ?_⟩
        · simp only [invertedPairs, Finset.mem_filter, Finset.mem_univ, true_and,
            Equiv.symm_apply_apply]
          exact ⟨by simp [Fin.lt_def, adjacentLower, adjacentUpper], hi⟩
        · simp only [invertedPairs, Finset.mem_filter, Finset.mem_univ, true_and, hsymm,
            Equiv.symm_apply_apply, not_and]
          intro h
          rw [Fin.lt_def, adjacentSwap_apply_val, adjacentSwap_apply_val] at h
          simp at h
      · intro kl hkl
        simp only [invertedPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hkl ⊢
        exact ⟨hsub _ _ hkl.1 hkl.2, hkl.2⟩
    have hagree' : ∀ k l, π'.symm k < π'.symm l → ρ.symm l < ρ.symm k →
        (c k < c l ↔ c' k < c' l) :=
      fun k l h₁ h₂ => hagree k l (hsub k l h₁ h₂) h₂
    have hIH := ih _ hcard π' hagree' rfl
    -- One exchange step for each height function.
    have hstep : ∀ d : Fin (n + 1) → α, Injective d →
        SignedBraidEquiv (inv (layeredWord (n + 1) (d ∘ ⇑π)) ++ layeredWord (n + 1) (d ∘ ⇑π'))
          ([(i, exchangeSign (d (π (adjacentLower (m := n + 1) i)))
            (d (π (adjacentUpper (m := n + 1) i))))] : SignedAdjacentWord (n + 1)) := by
      intro d hd
      have h1 := layeredWord_swap n (d ∘ ⇑π) (hd.comp π.injective) i
      rw [hπ', Equiv.Perm.coe_mul, ← Function.comp_assoc]
      refine (h1.append_left _).trans ?_
      simpa [List.append_assoc] using SignedBraidEquiv.cancel_inv_mid' []
        (layeredWord (n + 1) (d ∘ ⇑π))
        ([(i, exchangeSign (d (π (adjacentLower (m := n + 1) i)))
            (d (π (adjacentUpper (m := n + 1) i))))] : SignedAdjacentWord (n + 1))
    have hsign : exchangeSign (c (π (adjacentLower (m := n + 1) i)))
        (c (π (adjacentUpper (m := n + 1) i))) =
        exchangeSign (c' (π (adjacentLower (m := n + 1) i)))
          (c' (π (adjacentUpper (m := n + 1) i))) := by
      have := hagree (π (adjacentLower (m := n + 1) i)) (π (adjacentUpper (m := n + 1) i))
        (by simp [Fin.lt_def, adjacentLower, adjacentUpper]) hi
      unfold exchangeSign
      simp only [this]
    have hL := (SignedBraidEquiv.transition_comp (layeredWord (n + 1) (c ∘ ⇑π))
      (layeredWord (n + 1) (c ∘ ⇑π')) (layeredWord (n + 1) (c ∘ ⇑ρ))).symm
    have hR := SignedBraidEquiv.transition_comp (layeredWord (n + 1) (c' ∘ ⇑π))
      (layeredWord (n + 1) (c' ∘ ⇑π')) (layeredWord (n + 1) (c' ∘ ⇑ρ))
    refine hL.trans (((hstep c hc).append hIH).trans ?_)
    refine (SignedBraidEquiv.of_eq ?_).trans (((hstep c' hc').append
      (SignedBraidEquiv.refl _)).symm.trans hR)
    rw [hsign]

/-- The transition word between two orders that differ by one adjacent exchange is the signed
letter of that exchange. -/
theorem layeredTransition_swap {n : ℕ} {c : Fin (n + 1) → α} (hc : Injective c)
    (π : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    SignedBraidEquiv (inv (layeredWord (n + 1) (c ∘ ⇑π)) ++
        layeredWord (n + 1) (c ∘ ⇑(π * adjacentSwap (m := n + 1) i)))
      ([(i, exchangeSign (c (π (adjacentLower (m := n + 1) i)))
        (c (π (adjacentUpper (m := n + 1) i))))] : SignedAdjacentWord (n + 1)) := by
  have h1 := layeredWord_swap n (c ∘ ⇑π) (hc.comp π.injective) i
  rw [Equiv.Perm.coe_mul, ← Function.comp_assoc]
  refine (h1.append_left _).trans ?_
  simpa [List.append_assoc] using SignedBraidEquiv.cancel_inv_mid' []
    (layeredWord (n + 1) (c ∘ ⇑π))
    ([(i, exchangeSign (c (π (adjacentLower (m := n + 1) i)))
        (c (π (adjacentUpper (m := n + 1) i))))] : SignedAdjacentWord (n + 1))

/-- The transition word between equal orders is trivial. -/
theorem layeredTransition_self {n : ℕ} (c : Fin n → α) :
    SignedBraidEquiv (inv (layeredWord n c) ++ layeredWord n c) [] :=
  SignedBraidEquiv.inv_append_self _

end Layered

end OnLeConjecture.KnotTheory

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyPathWord

/-!
# Reversal of path words

The cut-system argument of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`, subsection "Global factorization, exponent count, and
transitivity") reads the boundary of a cell counterclockwise, so that two of its four sides are
traversed backwards. This module proves that traversing a strand family backwards inverts its
path word.

* `SignedBraidEquiv.inv`: the inverse word `SignedAdjacentWord.inv` respects `SignedBraidEquiv`.
  The inverse of a free cancellation or of a far commutation is a relation of the same kind, and
  the inverse of the positive braid relation is the negative braid relation `braid_neg`.
* `localWord_swap`: exchanging the two configurations of a local word inverts it.
* `chainWord_reverse`: the chain word of a reversed chain is the inverse of the chain word, when
  every two consecutive configurations may serve as centers of each other.
* `IsPathWord.reverse`: if `W` is a path word of `K` on `[u, v]`, then `W⁻¹` is a path word of the
  reversed family `t ↦ K (u + v - t)` on `[u, v]`.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.KnotTheory

open SignedAdjacentWord

variable {m : ℕ}

/-- The inverse of an elementary relation is a relation of the braid group. -/
theorem SignedBraidStep.inv_equiv {u v : SignedAdjacentWord m} (h : SignedBraidStep u v) :
    SignedBraidEquiv (inv u) (inv v) := by
  cases h with
  | cancel u v i e =>
    have h1 : inv (u ++ (i, e) :: (i, -e) :: v) = inv v ++ (i, e) :: (i, -e) :: inv u := by
      simp [inv]
    rw [h1, inv_append]
    exact SignedBraidEquiv.of_step (SignedBraidStep.cancel (inv v) (inv u) i e)
  | far u v i j e f h =>
    have h1 : inv (u ++ (i, e) :: (j, f) :: v) = inv v ++ (j, -f) :: (i, -e) :: inv u := by
      simp [inv]
    have h2 : inv (u ++ (j, f) :: (i, e) :: v) = inv v ++ (i, -e) :: (j, -f) :: inv u := by
      simp [inv]
    rw [h1, h2]
    exact SignedBraidEquiv.of_step (SignedBraidStep.far _ _ j i (-f) (-e) h.symm)
  | braid u v i j h =>
    have h1 : inv (u ++ (i, 1) :: (j, 1) :: (i, 1) :: v) =
        inv v ++ ([(i, -1), (j, -1), (i, -1)] ++ inv u) := by
      simp [inv]
    have h2 : inv (u ++ (j, 1) :: (i, 1) :: (j, 1) :: v) =
        inv v ++ ([(j, -1), (i, -1), (j, -1)] ++ inv u) := by
      simp [inv]
    rw [h1, h2]
    exact ((SignedBraidEquiv.braid_neg i j h).append_right (inv u)).append_left (inv v)

/-- **The inverse word respects equality in the braid group.** -/
theorem SignedBraidEquiv.inv {u v : SignedAdjacentWord m} (h : SignedBraidEquiv u v) :
    SignedBraidEquiv (SignedAdjacentWord.inv u) (SignedAdjacentWord.inv v) := by
  induction h with
  | rel _ _ h => exact h.inv_equiv
  | refl => exact SignedBraidEquiv.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem inv_flatten (L : List (SignedAdjacentWord m)) :
    inv L.flatten = (L.reverse.map inv).flatten := by
  induction L with
  | nil => rfl
  | cons w L ih => simp [List.flatten_cons, inv_append, ih]

end OnLeConjecture.KnotTheory

namespace OnLeConjecture.Analytic

open KnotTheory SignedAdjacentWord

variable {S : ℕ}

/-- Exchanging the two configurations of a local word inverts it. -/
theorem localWord_swap (z x y : Fin S → ℂ) : localWord z y x = inv (localWord z x y) := by
  simp [localWord, inv_append]

/-- **Reversed chains.** If every two consecutive configurations of the chain `Y` may serve as
centers of each other, the chain word of the reversed chain `a ↦ Y (N - a)` is the inverse of
the chain word of `Y`. -/
theorem chainWord_reverse : ∀ (N : ℕ) (Y : ℕ → Fin S → ℂ),
    (∀ b < N, SignedBraidEquiv (localWord (Y (b + 1)) (Y (b + 1)) (Y b))
      (localWord (Y b) (Y (b + 1)) (Y b))) →
    SignedBraidEquiv (chainWord (fun a => Y (N - a)) N) (inv (chainWord Y N))
  | 0, Y, _ => by simpa using SignedBraidEquiv.refl ([] : SignedAdjacentWord S)
  | N + 1, Y, hY => by
    have ih := chainWord_reverse N (fun b => Y (b + 1)) fun b hb => hY (b + 1) (by omega)
    have hX : chainWord (fun a => Y (N + 1 - a)) N = chainWord (fun a => Y (N - a + 1)) N :=
      chainWord_congr fun a ha => by rw [show N + 1 - a = N - a + 1 by omega]
    have hsplit : chainWord Y (N + 1) = localWord (Y 0) (Y 0) (Y 1) ++
        chainWord (fun b => Y (b + 1)) N := by
      rw [show N + 1 = 1 + N by omega, chainWord_add]
      simp only [chainWord_succ, chainWord_zero, List.nil_append, zero_add]
      congr 1
      exact chainWord_congr fun a _ => by rw [add_comm]
    rw [chainWord_succ, hX, hsplit, inv_append, ← localWord_swap]
    have e1 : N + 1 - N = 1 := by omega
    have e2 : N + 1 - (N + 1) = 0 := by omega
    rw [e1, e2]
    exact ih.append (hY 0 (by omega))

namespace IsPathWord

variable {K : Fin S → ℝ → ℂ} {u v : ℝ} {W : SignedAdjacentWord S}

/-- The reversed partition of a strict partition. -/
theorem _root_.OnLeConjecture.Analytic.IsStrictPartition.reverse {t : ℕ → ℝ} {N : ℕ} {δ : ℝ}
    (P : IsStrictPartition t N u v δ) :
    IsStrictPartition (fun a => u + v - t (N - a)) N u v δ := by
  refine ⟨by simp [P.last], by simp [P.zero], fun a ha => ?_, fun a ha => ?_⟩
  · have := P.step (N - (a + 1)) (by omega)
    rw [show N - (a + 1) + 1 = N - a by omega] at this
    linarith
  · have := P.gap (N - (a + 1)) (by omega)
    rw [show N - (a + 1) + 1 = N - a by omega] at this
    linarith

/-- **Reversal of path words.** If `W` is a path word of the strand family `K` on `[u, v]`, then
`W⁻¹` is a path word of the reversed family `t ↦ K (u + v - t)` on `[u, v]`. -/
theorem reverse (hcont : ∀ k, ContinuousOn (K k) (Icc u v))
    (hinj : ∀ t ∈ Icc u v, Injective fun k => K k t) (h : IsPathWord K u v W) :
    IsPathWord (fun k t => K k (u + v - t)) u v (inv W) := by
  obtain ⟨m, δ, hK⟩ := exists_pathModulus hcont hinj
  obtain ⟨δW, hδW, hW⟩ := h
  refine ⟨min δW δ, lt_min hδW hK.delta_pos, fun t' N P' => ?_⟩
  have P := P'.reverse
  have hP : IsStrictPartition (fun a => u + v - t' (N - a)) N u v δW :=
    P.mono (min_le_left _ _)
  have hWt := hW _ N hP
  set Y : ℕ → Fin S → ℂ := fun b k => K k (u + v - t' (N - b)) with hYdef
  have hrev : chainWord (fun a k => K k (u + v - t' a)) N = chainWord (fun a => Y (N - a)) N := by
    refine chainWord_congr fun a ha => funext fun k => ?_
    simp only [hYdef, show N - (N - a) = a by omega]
  rw [hrev]
  refine (chainWord_reverse N Y fun b hb => ?_).trans hWt.inv
  -- Consecutive configurations lie in a common cell.
  have hb1 := P.mem_Icc (a := b) (by omega)
  have hb2 := P.mem_Icc (a := b + 1) (by omega)
  have hgap := P.gap b hb
  have hstep := P.step b hb
  have hC : IsConfigCell {Y b, Y (b + 1)} m := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with rfl | rfl
      · exact hK.sep _ hb1
      · exact hK.sep _ hb2
    · have hnear : ∀ s ∈ ({b, b + 1} : Set ℕ), ∀ s' ∈ ({b, b + 1} : Set ℕ),
          ConfigNear (Y s) (Y s') (m / 8) := by
        intro s hs s' hs'
        have hs1 : u + v - t' (N - s) ∈ Icc u v := by
          rcases hs with rfl | rfl
          · exact hb1
          · exact hb2
        have hs2 : u + v - t' (N - s') ∈ Icc u v := by
          rcases hs' with rfl | rfl
          · exact hb1
          · exact hb2
        apply hK.near _ hs1 _ hs2
        rw [abs_lt]
        have hδ : min δW δ ≤ δ := min_le_right _ _
        rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> constructor <;> linarith
      intro x hx y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hnear b (by simp) b (by simp)
      · exact hnear b (by simp) (b + 1) (by simp)
      · exact hnear (b + 1) (by simp) b (by simp)
      · exact hnear (b + 1) (by simp) (b + 1) (by simp)
  exact hC.localWord_center hK.pos (by simp) (by simp) (by simp) (by simp)

end IsPathWord

end OnLeConjecture.Analytic

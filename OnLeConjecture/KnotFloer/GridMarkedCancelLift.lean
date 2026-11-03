/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridMarkedCancelCompare
public import OnLeConjecture.KnotTheory.SignedWordGridMoves
public import OnLeConjecture.KnotFloer.GridConnectedSumIterated
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-!
# Signed words on the first strands

A signed word on `a` strands is placed on the first `a` of `S ≥ a` strands by `liftWord`. The
lift commutes with concatenation, inverses and ladders, and sends `β.toSigned` to
`liftPositiveWord β`. A signed word grid of a word is a signed word grid of its lift, up to the
identification of the sizes (`isSignedWordGrid_liftWord`), since the heights of the corners and
the cyclic gaps only depend on the values of the letters.

Hence the word grid of a positive word `β` on `a` strands using every generator is related by grid
moves to every signed word grid of the lift of a conjugate of `β` (`wordGrid_movesTo_lift`), by
the signed word-grid relations (`signedWordGridRelations`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid OnLeConjecture.KnotFloer.GridFull
  SignedAdjacentWord

variable {a S : ℕ}

/-- A signed word on `a` strands placed on the first `a` of `S` strands. -/
def liftWord (h : a ≤ S) (w : SignedAdjacentWord a) : SignedAdjacentWord S :=
  w.map fun x => (Fin.castLE (by omega) x.1, x.2)

section Lift

variable (h : a ≤ S)

theorem liftWord_length (w : SignedAdjacentWord a) : (liftWord h w).length = w.length := by
  simp [liftWord]

theorem liftWord_append (u w : SignedAdjacentWord a) :
    liftWord h (u ++ w) = liftWord h u ++ liftWord h w := List.map_append

theorem liftWord_inv (w : SignedAdjacentWord a) : liftWord h (inv w) = inv (liftWord h w) := by
  simp [liftWord, inv, List.map_reverse, List.map_map, Function.comp_def]

theorem liftWord_toSigned (β : PositiveAdjacentWord a) :
    liftWord h β.toSigned = liftPositiveWord h β := by
  simp [liftWord, PositiveAdjacentWord.toSigned, liftPositiveWord, List.map_map,
    Function.comp_def]

theorem liftWord_ladder (s : ℕ) : ∀ (j : ℕ) (hj : s + j ≤ a - 1) (hj' : s + j ≤ S - 1),
    liftWord h (ladder s j hj) = ladder s j hj'
  | 0, _, _ => rfl
  | j + 1, hj, hj' => by
    rw [ladder, ladder, liftWord_append, liftWord_ladder s j (by omega) (by omega)]
    rfl

theorem getElem_liftWord (w : SignedAdjacentWord a) (i : ℕ) (hi : i < (liftWord h w).length) :
    (liftWord h w)[i] = (Fin.castLE (by omega) (w[i]'(by rw [liftWord_length] at hi; exact hi)).1,
      (w[i]'(by rw [liftWord_length] at hi; exact hi)).2) := by
  simp [liftWord]

end Lift

/-! ### Transport of signed word grids -/

theorem gridCast_O {n n' : ℕ} (e : n = n') (G : GridDiagram n) (c : Fin n') :
    (gridCast e G).O c = Fin.cast e (G.O (Fin.cast e.symm c)) := by
  subst e; rfl

theorem gridCast_X {n n' : ℕ} (e : n = n') (G : GridDiagram n) (c : Fin n') :
    (gridCast e G).X c = Fin.cast e (G.X (Fin.cast e.symm c)) := by
  subst e; rfl

section Transport

variable (h : a ≤ S) (w : SignedAdjacentWord a)

/-- The corner of the lift over a corner of the word. -/
def liftCorner (p : Fin w.length × Fin 3) : Fin (liftWord h w).length × Fin 3 :=
  (Fin.cast (liftWord_length h w).symm p.1, p.2)

theorem liftCorner_surj (q : Fin (liftWord h w).length × Fin 3) :
    ∃ p, liftCorner h w p = q :=
  ⟨(Fin.cast (liftWord_length h w) q.1, q.2), by simp [liftCorner]⟩

theorem oHeight2_liftCorner (p : Fin w.length × Fin 3) :
    (liftWord h w).oHeight2 (liftCorner h w p) = w.oHeight2 p := by
  simp only [SignedAdjacentWord.oHeight2, liftCorner, Fin.val_cast]
  rw [getElem_liftWord]
  simp [signedOHeight2]

theorem xHeight2_liftCorner (p : Fin w.length × Fin 3) :
    (liftWord h w).xHeight2 (liftCorner h w p) = w.xHeight2 p := by
  simp only [SignedAdjacentWord.xHeight2, liftCorner, Fin.val_cast]
  rw [getElem_liftWord]
  simp [signedXHeight2]

theorem fpe_liftCorner (p : Fin w.length × Fin 3) :
    (finProdFinEquiv (liftCorner h w p)).val = (finProdFinEquiv p).val := by
  simp [liftCorner]

theorem cornerGap_liftCorner (p q : Fin w.length × Fin 3) :
    (liftWord h w).cornerGap (liftCorner h w p) (liftCorner h w q) = w.cornerGap p q := by
  simp only [SignedAdjacentWord.cornerGap, fpe_liftCorner, liftWord_length]

theorem lift_size : w.length * 3 = (liftWord h w).length * 3 := by rw [liftWord_length]

theorem gridCast_O_liftCorner (G : GridDiagram (w.length * 3)) (p : Fin w.length × Fin 3) :
    ((gridCast (lift_size h w) G).O (finProdFinEquiv (liftCorner h w p))).val =
      (G.O (finProdFinEquiv p)).val := by
  rw [gridCast_O, Fin.val_cast]
  congr 2

theorem gridCast_X_liftCorner (G : GridDiagram (w.length * 3)) (p : Fin w.length × Fin 3) :
    ((gridCast (lift_size h w) G).X (finProdFinEquiv (liftCorner h w p))).val =
      (G.X (finProdFinEquiv p)).val := by
  rw [gridCast_X, Fin.val_cast]
  congr 2

/-- **Signed word grids of a lift.** -/
theorem isSignedWordGrid_liftWord {G : GridDiagram (w.length * 3)} (hG : IsSignedWordGrid w G) :
    IsSignedWordGrid (liftWord h w) (gridCast (lift_size h w) G) := by
  constructor
  · intro a' b' hab
    obtain ⟨p, rfl⟩ := liftCorner_surj h w a'
    obtain ⟨q, rfl⟩ := liftCorner_surj h w b'
    rw [oHeight2_liftCorner, oHeight2_liftCorner] at hab
    rw [Fin.lt_def, gridCast_O_liftCorner, gridCast_O_liftCorner]
    exact hG.O_lt p q hab
  · intro b'
    obtain ⟨q, rfl⟩ := liftCorner_surj h w b'
    obtain ⟨p, hp1, hp2, hp3⟩ := hG.X_eq q
    refine ⟨liftCorner h w p, ?_, fun a' ha => ?_, ?_⟩
    · rw [oHeight2_liftCorner, xHeight2_liftCorner, hp1]
    · obtain ⟨p', rfl⟩ := liftCorner_surj h w a'
      rw [oHeight2_liftCorner, xHeight2_liftCorner] at ha
      rw [cornerGap_liftCorner, cornerGap_liftCorner]
      exact hp2 p' ha
    · apply Fin.ext
      rw [gridCast_X_liftCorner, gridCast_O_liftCorner, hp3]

end Transport

/-! ### Word grids of a positive word and signed word grids of a lifted conjugate -/

theorem generatorIndices_univ_of_sub {m : ℕ} {u w : SignedAdjacentWord m}
    (hu : u.generatorIndices = Finset.univ) (hsub : ∀ x ∈ u, x ∈ w) :
    w.generatorIndices = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro i
  have hi : i ∈ u.generatorIndices := by rw [hu]; exact Finset.mem_univ i
  simp only [generatorIndices, List.mem_toFinset, List.mem_map] at hi ⊢
  obtain ⟨x, hx, rfl⟩ := hi
  exact ⟨x, hsub x hx, rfl⟩

/-- **The word grid of `β` and the lifted conjugates of `β`.** -/
theorem wordGrid_movesTo_lift (h : a ≤ S) (ha : 2 ≤ a) (β : PositiveAdjacentWord a)
    (hβ : β.toSigned.generatorIndices = Finset.univ) (A : SignedAdjacentWord a)
    {G : GridDiagram ((liftWord h (conjugateWord A β.toSigned)).length * 3)}
    (hG : IsSignedWordGrid (liftWord h (conjugateWord A β.toSigned)) G) :
    (wordGrid β).MovesTo G := by
  have hgen : (conjugateWord A β.toSigned).generatorIndices = Finset.univ :=
    generatorIndices_univ_of_sub hβ (fun x hx => by simp [conjugateWord, hx])
  obtain ⟨H₀, hH₀, hm⟩ := signedWordGridRelations ha β (conjugateWord A β.toSigned) hβ hgen
    (SignedBraidConj.conjugate_left A β.toSigned).symm
  exact hm.trans ((movesTo_gridCast _ H₀).trans
    (signed_movesTo (isSignedWordGrid_liftWord h _ hH₀) hG))

end OnLeConjecture.KnotTheory.MarkedCancel

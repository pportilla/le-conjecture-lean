/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.MarkedCancelFront
public import OnLeConjecture.KnotTheory.SignedWordGridMovesCancelStep

/-!
# Grid moves between marked word grids

`MFwd v p v' p'` says that, for every protected grid `H`, every marked word grid of `v` with the
marked arc leaving `p` is related by grid moves to a marked word grid of `v'` with the marked arc
leaving `p'`. It is reflexive and transitive.

The marked cancellation of an inverse pair at the front of a word, with the marked arc leaving a
corner of the remaining word, gives `MFwd` (`mfwd_cancel_front`). This instantiates
`marked_cancel_front` with the window data `SignedGrid.cancP` and `SignedGrid.cancM` of the
unmarked cancellation.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow

variable {m : ℕ}

/-- Every marked word grid of `v` at `p` is related by grid moves to a marked word grid of `v'` at
`p'`, for every protected grid. -/
def MFwd (v : SignedAdjacentWord m) (hv : 0 < v.length) (p : Fin v.length × Fin 3)
    (v' : SignedAdjacentWord m) (hv' : 0 < v'.length) (p' : Fin v'.length × Fin 3) : Prop :=
  ∀ {k : ℕ} (H : GridDiagram (k + 1)) (hX : H.X 0 = 0) (hO : H.O (Fin.last k) = 0)
    (M : GridDiagram (v.length * 3 + k + 1)), IsMarkedGrid v hv p H hX hO M →
      ∃ M' : GridDiagram (v'.length * 3 + k + 1), IsMarkedGrid v' hv' p' H hX hO M' ∧ M.MovesTo M'

theorem MFwd.refl (v : SignedAdjacentWord m) (hv : 0 < v.length) (p : Fin v.length × Fin 3) :
    MFwd v hv p v hv p :=
  fun _ _ _ M hM => ⟨M, hM, GridDiagram.MovesTo.refl _⟩

theorem MFwd.trans {v v' v'' : SignedAdjacentWord m} {hv : 0 < v.length} {hv' : 0 < v'.length}
    {hv'' : 0 < v''.length} {p : Fin v.length × Fin 3} {p' : Fin v'.length × Fin 3}
    {p'' : Fin v''.length × Fin 3} (h₁ : MFwd v hv p v' hv' p') (h₂ : MFwd v' hv' p' v'' hv'' p'') :
    MFwd v hv p v'' hv'' p'' := by
  intro k H hX hO M hM
  obtain ⟨M', hM', hm⟩ := h₁ H hX hO M hM
  obtain ⟨M'', hM'', hm'⟩ := h₂ H hX hO M' hM'
  exact ⟨M'', hM'', hm.trans hm'⟩

/-- Any key refining the outgoing heights gives the same marked word grids up to grid moves. -/
theorem MFwd.of_key {v : SignedAdjacentWord m} {hv : 0 < v.length} {p : Fin v.length × Fin 3}
    {k : ℕ} {H : GridDiagram (k + 1)} {hX : H.X 0 = 0} {hO : H.O (Fin.last k) = 0}
    {M : GridDiagram (v.length * 3 + k + 1)} (hM : IsMarkedGrid v hv p H hX hO M)
    {κ : Fin v.length × Fin 3 → ℕ} (hκ : ∀ a b, v.oHeight2 a < v.oHeight2 b → κ a < κ b) :
    M.MovesTo (markedGrid v κ hv p H hX hO).toGrid := by
  obtain ⟨κ₀, hκ₀, rfl⟩ := hM
  exact markedGrid_movesTo_of_keys v hv p H hX hO hκ₀ hκ

/-- The corner of `u ++ t` over a corner of `t`. -/
def shiftCorner (u t : SignedAdjacentWord m) (q : Fin t.length × Fin 3) :
    Fin (u ++ t).length × Fin 3 :=
  (⟨q.1.val + u.length, by simp only [List.length_append]; omega⟩, q.2)

theorem cancP_ol : 30 ∈ Ol cancP ∧ 31 ∈ Ol cancP := by decide

theorem cancM_ol : 30 ∈ Ol cancM ∧ 31 ∈ Ol cancM := by decide

theorem cancP_xl : ∀ x ∈ Xl cancP, x ∉ Ol cancP → isConn x = true := by decide

theorem cancM_xl : ∀ x ∈ Xl cancM, x ∉ Ol cancM → isConn x = true := by decide

/-- **Marked cancellation at the front of a word.** If both ranks of the inverse pair occur in
`t`, a marked word grid of the pair followed by `t`, with the marked arc leaving a corner of `t`,
is related by grid moves to a marked word grid of `t` with the marked arc leaving that corner. -/
theorem mfwd_cancel_front (r : Fin (m - 1)) (e : ℤˣ) (t : SignedAdjacentWord m)
    (h0 : RankIn t r.val) (h1 : RankIn t (r.val + 1)) (p' : Fin t.length × Fin 3) :
    MFwd ([(r, e), (r, -e)] ++ t) (by simp) (shiftCorner [(r, e), (r, -e)] t p') t
      (Fin.pos p'.1) p' := by
  intro k H hX hO M hM
  rcases Int.units_eq_one_or e with rfl | rfl
  · have hB := block_cancel_S r 1 [true, false] t (fun k hk => by
      interval_cases k <;> simp [posB]) h0 h1
    have hm1 := MFwd.of_key hM (skappa_mono (K := 2) cancP _ cancP_init.2.2.2.2.1)
    have hm2 := markedGrid_movesTo_winGrid cancP hB cancP_init
      (shiftCorner [(r, 1), (r, -1)] t p') H hX hO
    obtain ⟨M', hM', hm3⟩ := marked_cancel_front hB cancP cancP_init cancP_run cancP_ok cancP_ol
      cancP_xl p' H hX hO
    exact ⟨M', hM', hm1.trans (hm2.trans hm3)⟩
  · have hB := block_cancel_S r (-1) [false, true] t (fun k hk => by
      interval_cases k <;> simp [posB]) h0 h1
    have hm1 := MFwd.of_key hM (skappa_mono (K := 2) cancM _ cancM_init.2.2.2.2.1)
    have hm2 := markedGrid_movesTo_winGrid cancM hB cancM_init
      (shiftCorner [(r, -1), (r, - -1)] t p') H hX hO
    obtain ⟨M', hM', hm3⟩ := marked_cancel_front hB cancM cancM_init cancM_run cancM_ok cancM_ol
      cancM_xl p' H hX hO
    exact ⟨M', hM', hm1.trans (hm2.trans hm3)⟩

end OnLeConjecture.KnotTheory.MarkedCancel

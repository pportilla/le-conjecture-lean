/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridEndpointCleanupBlocks
public import OnLeConjecture.KnotTheory.ScissorSequenceCount

/-!
# The marked factor cleanup as a statement

This file states `MarkedFactorCleanupStatement`, the marked inverse cancellation with a protected
seam summand of the written proof of Statement E (`statement_E_complete_proof.tex`, Section 8,
Lemma `markedInverseCancellation`), applied to one factor of a normalized factorization, together
with the reframing of Section 10 ("The invariant under marked inverse-pair cancellation"). The
statement is not proved here. It is the only input of the cleanup of the scissor endpoint that is
not proved by the files `GridEndpointCleanup*`.

**The frame preparation.** A grid diagram `G` of size `n` has its *closing row at the bottom*
(`ClosingRowBottom`) if the `O` marking of its last column and the `X` marking of its first column
lie in row `0`. Its frame preparation `framePrep G` is the grid `D(G, b)` of Section 10
("Preparation at a specified arc") for the arc `b` of row `0`: rotate the rows so that row `0`
becomes the top row, and `X`-stabilize at the `X` marking of column `0` with the new last column
and the new bottom row. It is triply prepared (`framePrep_triplyPrepared`).

**The statement.** Let `F` be a normalized factorization on `S ≥ 2` strands in which strand `0`
lies in every factor cycle, and let `l` be a factor, with the padded factor word
`q_l = (p γ_l) η_l (p γ_l)⁻¹`. There are a triply prepared grid `P` and a frame tower `E` over `P`
with `S - a_l` four-mark blocks (`FrameTower`, one block for every strand fixed by the factor) such
that

* if `l` is a singular factor, `P` is related by grid moves to the word grid of the local
  positive word `β_l`;
* if `l` is a simple factor, `P` is an unknotted seam summand: the seam of any grid `G` (with its
  last `X` marking in its last row) with `P` is related to `G` by grid moves;
* for every signed word grid `G` of `q_l` whose closing rank-`0` arc lies in the bottom row and
  every triply prepared *protected* grid `H`, the binary seam `Σ(H, framePrep G)` is related by
  grid moves to `Σ(H, E)`.

In the binary seam `Σ(H, D)` the protected grid `H` is inserted into the frame arc of `D`, which
is the closing rank-`0` arc of `G`; this is the framed insertion of Section 8 with the protected
seam summand `H`. In the application `H` is the seam of all other factors of the scissor endpoint,
so the conclusion replaces the exposed factor by its cleaned form and leaves every other factor
unchanged.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory

variable {n : ℕ}

/-- The closing arc of a grid diagram lies in its bottom row: the `O` marking of the last column
and the `X` marking of the first column lie in row `0`. -/
def ClosingRowBottom (G : GridDiagram n) : Prop :=
  ∃ h : 0 < n, G.O ⟨n - 1, by omega⟩ = ⟨0, h⟩ ∧ G.X ⟨0, h⟩ = ⟨0, h⟩

/-- **The frame preparation** `D(G, b)` at the arc `b` of the bottom row (Section 10, "Preparation
at a specified arc"): the rows are rotated so that row `0` becomes the top row, and the `X`
marking of column `0` is split by an `X` stabilization with the new last column and the new bottom
row. -/
def framePrep (G : GridDiagram n) (hG : ClosingRowBottom G) : GridDiagram (n + 1) :=
  (G.relabelRows (finRotate n).symm).stabilizeX (Fin.last n) 0 ⟨0, hG.1⟩

/-- The frame preparation is triply prepared. -/
theorem framePrep_triplyPrepared (G : GridDiagram n) (hG : ClosingRowBottom G) :
    TriplyPrepared (framePrep G hG) := by
  obtain ⟨hn, hO, hX⟩ := hG
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  have hrot : ((finRotate (d + 1)).symm (G.X 0)) = Fin.last d := by
    have hX' : G.X 0 = 0 := hX
    rw [hX', Equiv.symm_apply_eq, finRotate_last]
  refine ⟨?_, ?_, ?_⟩
  · simp only [framePrep, GridDiagram.stabilizeX_X]
    have h := GridState.splitPoint_apply_splitColumn
      (G.relabelRows (finRotate (d + 1)).symm).X (Fin.last (d + 1)) 0 0
    rw [Fin.succAbove_last] at h
    exact h
  · simp only [framePrep, GridDiagram.stabilizeX_O]
    exact GridState.insertPoint_apply_newColumn _ _ _
  · simp only [framePrep, GridDiagram.stabilizeX_X]
    rw [GridState.splitPoint_apply_newColumn]
    apply Fin.ext
    simp only [GridDiagram.relabelRows_X, GridState.relabelRows_apply]
    rw [show (⟨0, hn⟩ : Fin (d + 1)) = 0 from rfl, hrot]
    simp

/-- **The marked factor cleanup** (Section 8, Lemma `markedInverseCancellation`, for one factor,
with the reframing of Section 10). For every factor `l` of a normalized factorization in which
strand `0` lies in every factor cycle, there are a triply prepared grid `P` and a frame tower `E`
over `P` with `S - a_l` four-mark blocks such that `P` is related to the word grid of the local
word if `l` is singular, `P` is an unknotted seam summand if `l` is simple, and for every signed
word grid `G` of the padded factor with its closing rank-`0` arc in the bottom row and every
triply prepared protected grid `H`, the seam `Σ(H, framePrep G)` is related by grid moves to
`Σ(H, E)`. -/
def MarkedFactorCleanupStatement : Prop :=
  ∀ (S N B : ℕ) (hS : 2 ≤ S) (F : NormalizedFactorization S N B),
    F.StrandZeroInEveryFactor (by omega) → ∀ l : Fin (N + B),
      ∃ (a : ℕ) (P : GridDiagram (a + 1)) (b : ℕ) (E : GridDiagram (b + 1))
        (hP : TriplyPrepared P) (hPE : FrameTower P (S - F.cycleLength l) E),
        (∀ h : l.val < N, (wordGrid (F.word ⟨l.val, h⟩)).MovesTo P) ∧
        (N ≤ l.val → ∀ (m : ℕ) (G : GridDiagram (m + 1)) (hG : G.X (Fin.last m) = Fin.last m),
          (connectedSumSeamGrid G P hG hP.1).MovesTo G) ∧
        ∀ (G : GridDiagram ((F.factor l).length * 3)), IsSignedWordGrid (F.factor l) G →
          ∀ (hG : ClosingRowBottom G) (m : ℕ) (H : GridDiagram (m + 1)) (hH : TriplyPrepared H),
            (connectedSumSeamGrid H (framePrep G hG) hH.2.2
                (framePrep_triplyPrepared G hG).1).MovesTo
              (connectedSumSeamGrid H E hH.2.2 (hPE.triplyPrepared hP).1)

end OnLeConjecture.KnotFloer.GridFull

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.TorusWordGridBase
public import OnLeConjecture.KnotTheory.TorusWordGridTorus

/-! # The selected grid of a torus word and the reflected torus grid

Record M404 (combinatorial form) and M807 of the dependency audit:
`docs/route-n/J11-torus-word-grid.tex`, Theorem *main*, for `q ≥ 2`.

* `wordGrid_betaPow_movesTo`: the selected grid of `β^{J+1}`, for the descending Coxeter word
  `β` on `A + 1` strands and `J ≥ 1`, is related by grid moves to
  `reflectedDiagram (torusLink A J)`. Proof: the base case (`exists_base`), `J` absorptions
  (`IsHybrid.exists_absorb`), and the identification of the hybrid grid without blocks
  (`IsHybrid.movesTo_reflectedTorusLink`).
* `wordGrid_torusWord_movesTo`: the same for the torus word `δ^q`, `δ` the Coxeter word, with
  `a ≥ 2` strands and `q ≥ 2`, through far commutations and rotations
  (`wordGrid_torusWord_movesTo_pow`).
* `reflectedTorusGrid_movesTo_coxeterPower`: the case `a = S`, `q = S + 1`.

All results are unconditional. The case `q = 1` is not formalized here.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti OnLeConjecture.KnotFloer.GridFull

theorem IsHybrid.length_eq {n A k J : ℕ} {G : LabeledGrid n TorusCol TorusRow}
    (hG : IsHybrid A k J G) : n = A + 1 + k + 3 * A * J := by
  have := G.cols_length
  rw [hG.cols, hybCols, List.length_append, rCols_length, wordCols_length] at this
  omega

/-- `J` absorptions starting from `H_{A+1,1}(β^J)`. -/
theorem IsHybrid.exists_absorb_all {A : ℕ} (hA : 1 ≤ A) :
    ∀ (J k n : ℕ) (G : LabeledGrid n TorusCol TorusRow), 1 ≤ k → IsHybrid A k J G →
      ∃ (n' : ℕ) (G' : LabeledGrid n' TorusCol TorusRow), IsHybrid A (k + J) 0 G' ∧
        G.toGrid.MovesTo G'.toGrid := by
  intro J
  induction J with
  | zero => intro k n G _ hG; exact ⟨n, G, hG, GridDiagram.MovesTo.refl _⟩
  | succ J ih =>
    intro k n G hk hG
    obtain ⟨n₁, G₁, h₁, hmv₁⟩ := hG.exists_absorb hA hk
    obtain ⟨n₂, G₂, h₂, hmv₂⟩ := ih (k + 1) n₁ G₁ (by omega) h₁
    refine ⟨n₂, G₂, by rwa [show k + (J + 1) = k + 1 + J by omega], hmv₁.trans hmv₂⟩

/-- **The selected grid of `β^{J+1}`.** -/
theorem wordGrid_betaPow_movesTo {A J : ℕ} (hA : 1 ≤ A) (hJ : 1 ≤ J) :
    (wordGrid (wordPow (betaWord A) (J + 1))).MovesTo
      (reflectedDiagram (GridDiagram.torusLink A J)) := by
  obtain ⟨n, G, hG, hmv⟩ := exists_base hA hJ
  obtain ⟨n', G', hG', hmv'⟩ := IsHybrid.exists_absorb_all hA J 1 n G le_rfl hG
  rw [show 1 + J = J + 1 by omega] at hG'
  have hn := hG'.length_eq
  simp only [Nat.mul_zero, Nat.add_zero] at hn
  subst hn
  exact (hmv.trans hmv').trans hG'.movesTo_reflectedTorusLink.symm

theorem betaWord_perm (A : ℕ) : (betaWord A).Perm (List.finRange (A + 1 - 1)) :=
  List.reverse_perm _

/-- **Theorem main of J11, for `q ≥ 2`.** The selected grid of the torus word `δ^q` on `a`
strands is related by grid moves to the reflected standard grid of the `(a, q)` torus link. -/
theorem wordGrid_torusWord_movesTo (a q : ℕ) (ha : 2 ≤ a) (hq : 2 ≤ q) :
    (wordGrid (torusWord a q)).MovesTo
      (reflectedDiagram (GridDiagram.torusLink (a - 1) (q - 1))) := by
  obtain ⟨A, rfl⟩ : ∃ A, a = A + 1 := ⟨a - 1, by omega⟩
  obtain ⟨J, rfl⟩ : ∃ J, q = J + 1 := ⟨q - 1, by omega⟩
  change (wordGrid (torusWord (A + 1) (J + 1))).MovesTo
    (reflectedDiagram (GridDiagram.torusLink A J))
  exact (wordGrid_torusWord_movesTo_pow (betaWord A) (betaWord_perm A) (J + 1)).trans
    (wordGrid_betaPow_movesTo (by omega) (by omega))

/-- **The case `a = S`, `q = S + 1` needed by J12.** -/
theorem reflectedTorusGrid_movesTo_coxeterPower (S : ℕ) (hS : 2 ≤ S) :
    (reflectedTorusGrid (S - 1)).MovesTo (wordGrid (fullTwistWord S ++ coxeterWord S)) := by
  obtain ⟨A, rfl⟩ : ∃ A, S = A + 1 := ⟨S - 1, by omega⟩
  change (reflectedTorusGrid A).MovesTo _
  rw [fullTwistWord, ← torusWord_succ]
  have h : (wordGrid (torusWord (A + 1) (A + 1 + 1))).MovesTo
      (reflectedDiagram (GridDiagram.torusLink A (A + 1))) :=
    wordGrid_torusWord_movesTo (A + 1) (A + 1 + 1) (by omega) (by omega)
  exact h.symm

end OnLeConjecture.KnotTheory

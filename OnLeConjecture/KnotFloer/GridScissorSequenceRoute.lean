/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridScissorSequenceTree

/-!
# Reduction of the combinatorial route to the cleanup of the scissor endpoint

This file reduces `ScissorRouteStatement` (`GridExteriorScissorSteps`) to the cleanup part of the
construction, Sections 10 and 11 of the written proof of Statement E
(`statement_E_complete_proof.tex`) together with the marked inverse cancellations of Section 8.

The scissor phase, its count of `X` switches and its spanning tree are proved in
`GridScissorSequenceTree` (`exists_scissorPhase`). Its endpoint is a *scissor endpoint grid*
(`IsScissorEndpointGrid`): its rows are ordered by height, and its component permutation sends
the last column of every rank `x ≥ 1` of a factor to the first column of that rank in the same
factor and follows the matching of the product elsewhere. What remains is
`ScissorEndpointCleanupStatement`: prepared factor grids `D_j` related by grid moves to the word
grids of the local words, such that every scissor endpoint grid is related by grid moves to a
four-mark tower over the iterated seam of the `D_j` with `F.auxCount` blocks, one for every pair
of a factor and a strand it fixes. This statement is not proved here.

The main result is `scissorRouteStatement_of_cleanup`. All other results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory OnLeConjecture.KnotTheory.SignedGrid
  OnLeConjecture.KnotTheory.NormalizedFactorization

/-- A scissor endpoint grid: rows ordered by height, and the component permutation of the
scissor endpoint. -/
def IsScissorEndpointGrid {S N B : ℕ} (F : NormalizedFactorization S N B) (hS : 2 ≤ S)
    (K : GridDiagram (prodSize F)) : Prop :=
  ∃ (ℓ : List (Fin (prodSize F))) (hnd : ℓ.Nodup) (hl : ℓ.length = prodSize F)
    (μ : Equiv.Perm (Fin (prodSize F))) (hμ : ∀ d, μ d ≠ d),
    K = phaseGrid (listPerm ℓ hnd hl) μ hμ ∧
      ℓ.Pairwise (fun a b => colHeight F a ≤ colHeight F b) ∧ IsScissorEndpointPerm F hS μ

/-- **The cleanup of the scissor endpoint** (Sections 8, 10 and 11 of the written proof): seam
preparation, cyclic exposure, marked inverse cancellations, removal of the trailing simple
factors and positioning of the auxiliary blocks, stated as grid moves. -/
def ScissorEndpointCleanupStatement : Prop :=
  ∀ (S N B : ℕ) (hS : 2 ≤ S) (hN : 0 < N) (F : NormalizedFactorization S N B),
    F.StrandZeroInEveryFactor (by omega) → F.Transitive →
    ∃ (sizes : Fin N → ℕ) (D : ∀ j, GridDiagram (sizes j)) (hprep : SeamPrepared D)
      (_ : ∀ j, 2 ≤ sizes j),
      (∀ j, (wordGrid (F.word j)).MovesTo (D j)) ∧
      ∀ K : GridDiagram (prodSize F), IsScissorEndpointGrid F hS K →
        ∃ (m : ℕ) (K' : GridDiagram m) (e : Fin (iteratedSeamSize sizes) → Fin m),
          K.MovesTo K' ∧ FourMarkTower (iteratedSeamGrid D hprep) F.auxCount K' e

/-- **Reduction of the combinatorial route.** The scissor phase of Section 9 is proved; the
cleanup of its endpoint gives `ScissorRouteStatement`. -/
theorem scissorRouteStatement_of_cleanup (h : ScissorEndpointCleanupStatement) :
    ScissorRouteStatement := by
  intro S N B hS hN F hzero htrans
  obtain ⟨sizes, D, hprep, hD, hw, hK⟩ := h S N B hS hN F hzero htrans
  refine ⟨sizes, D, hprep, hD, hw, fun H hH => ?_⟩
  obtain ⟨K, E, k, hk, hph, htree, ℓ, hnd, hl, μ, hμ, hKeq, hsort, hend⟩ :=
    exists_scissorPhase (hS := hS) hN hzero htrans hH
  obtain ⟨m, K', e, hmv, htower⟩ := hK K ⟨ℓ, hnd, hl, μ, hμ, hKeq, hsort, hend⟩
  have hU : E.length = F.auxCount := by
    have := htree.2
    rw [hKeq, gridComponentPerm_phaseGrid, ← orbitCount_def,
      orbitCount_endpoint (hS := hS) hN hzero hend] at this
    omega
  have htower' : FourMarkTower (iteratedSeamGrid D hprep) E.length K' e := hU ▸ htower
  exact ⟨K, E, k, m, K', e, hk, hph, htree, hmv, htower'⟩

end OnLeConjecture.KnotFloer.GridFull

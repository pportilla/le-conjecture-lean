/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridEndpointCleanupBlockGrid

/-!
# The cleanup of the scissor endpoint

This file proves `ScissorEndpointCleanupStatement` (`GridScissorSequenceRoute`) from the marked
factor cleanup `MarkedFactorCleanupStatement` (`GridEndpointCleanupMarkedStatement`), following
Sections 10 and 11 of the written proof of Statement E (`statement_E_complete_proof.tex`):

1. the rows of a scissor endpoint grid are sorted into blocks, and the sorted grid is the cyclic
   block grid of the frame preparations of the local grids of the factors; a global
   `X` stabilization gives their seam chain (`endpoint_movesTo_seamChain`; for one factor,
   `endpoint_movesTo_framePrep`);
2. every factor is exposed by the cyclic block rule and cleaned by the marked factor cleanup,
   with the seam of the other factors protected (`chainOf_movesTo_cleanAll`);
3. the seam chain of the cleaned factors is a frame tower over the seam chain of the cleaned
   factor grids (`FrameTower.seamChain`), and its auxiliary blocks are moved to the canonical
   stack at the origin (`FrameTower.exists_canonStack`);
4. the trailing simple factors are removed (`canonStack_removeSimple`), and the canonical stack is a
   four-mark tower over the iterated seam of the singular factors (`CanonStack.fourMarkTower`).

The main result is `scissorEndpointCleanupStatement_of_markedFactorCleanup`, and with
`scissorRouteStatement_of_cleanup` it gives `scissorRouteStatement_of_markedFactorCleanup`. The
only hypothesis is `MarkedFactorCleanupStatement`.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory OnLeConjecture.KnotTheory.SignedGrid
  OnLeConjecture.KnotTheory.NormalizedFactorization

/-! ### Transport along equalities in `Σ k, GridDiagram k` -/

theorem FourMarkTower.of_sigma_eq {n₀ n₀' : ℕ} {G₀ : GridDiagram n₀} {G₀' : GridDiagram n₀'}
    (h : (⟨n₀, G₀⟩ : Σ k, GridDiagram k) = ⟨n₀', G₀'⟩) {k m : ℕ} {G : GridDiagram m}
    {e : Fin n₀ → Fin m} (hG : FourMarkTower G₀ k G e) :
    ∃ e' : Fin n₀' → Fin m, FourMarkTower G₀' k G e' := by
  obtain ⟨hn, hG₀⟩ := Sigma.mk.inj_iff.mp h
  subst hn
  obtain rfl := eq_of_heq hG₀
  exact ⟨e, hG⟩

theorem CanonStack.of_sigma_eq {a a' : ℕ} {T : GridDiagram (a + 1)} {T' : GridDiagram (a' + 1)}
    (h : (⟨a + 1, T⟩ : Σ k, GridDiagram k) = ⟨a' + 1, T'⟩) {k b : ℕ} {G : GridDiagram (b + 1)}
    (hG : CanonStack T k G) : CanonStack T' k G := by
  obtain ⟨hn, hT⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : a = a' := by omega
  obtain rfl := eq_of_heq hT
  exact hG

/-- Seam chains of families that agree after a transport of the index agree. -/
theorem chainOf_sigma_cast {M M' : ℕ} (hM : M = M') {F : Fin (M + 1) → Σ e, GridDiagram (e + 1)}
    {F' : Fin (M' + 1) → Σ e, GridDiagram (e + 1)} (ht : ∀ j, TriplyPrepared (F j).2)
    (ht' : ∀ j, TriplyPrepared (F' j).2) (h : ∀ j, F j = F' (Fin.cast (by omega) j)) :
    (⟨_, chainOf M F ht⟩ : Σ k, GridDiagram k) = ⟨_, chainOf M' F' ht'⟩ := by
  subst hM
  exact chainOf_sigma_congr ht ht' fun j => (h j).trans (congrArg F' (Fin.ext rfl))

/-! ### Removal of trailing simple factors under a canonical stack -/

/-- `A` is an unknotted seam summand: its seam with every grid whose last `X` marking lies in the
last row is related to that grid by grid moves. -/
def SimpleSummand (A : Σ e, GridDiagram (e + 1)) : Prop :=
  ∀ (m : ℕ) (G : GridDiagram (m + 1)) (hG : G.X (Fin.last m) = Fin.last m)
    (hA : A.2.X 0 = 0), (connectedSumSeamGrid G A.2 hG hA).MovesTo G

/-- **Removal of trailing simple factors under a canonical stack.** -/
theorem canonStack_removeSimple (m U : ℕ) :
    (k : ℕ) → (G : Fin (m + k + 1) → Σ e, GridDiagram (e + 1)) →
      (ht : ∀ j, TriplyPrepared (G j).2) →
      (∀ i : Fin (m + k + 1), m < i.val → SimpleSummand (G i)) →
      ∀ {b : ℕ} {Y : GridDiagram (b + 1)}, CanonStack (chainOf (m + k) G ht) U Y →
        ∃ (b' : ℕ) (Q : GridDiagram (b' + 1)),
          CanonStack (chainOf m (fun j => G (Fin.castLE (by omega) j)) fun j => ht _) U Q ∧
            Y.MovesTo Q
  | 0, G, ht, _, b, Y, hY => ⟨b, Y, hY.of_sigma_eq (chainOf_sigma_congr _ _ fun j =>
      congrArg G (Fin.ext rfl)), GridDiagram.MovesTo.refl _⟩
  | k + 1, G, ht, hs, b, Y, hY => by
    have hdec := seamChainGrid_succ_of_triplyPrepared (m + k) (fun j => (G j).2)
      (fun j => (ht j.succ).1) ht
    have hT := seamChainGrid_triplyPrepared (m + k) (fun j => (G j.castSucc).2)
      (fun j => (ht j.castSucc.succ).1) fun j => ht j.castSucc
    obtain ⟨b₁, Q₁, hQ₁⟩ := CanonStack.exists_canonStack
      (seamChainGrid (m + k) (fun j => (G j.castSucc).2) fun j => (ht j.castSucc.succ).1) U
    have hseam := hQ₁.seam_left hT.2.2 (G (Fin.last (m + k + 1))).2 (ht _).1
    have hY' : CanonStack (chainOf (m + k + 1) G ht) U
        (connectedSumSeamGrid Q₁ (G (Fin.last (m + k + 1))).2 (hQ₁.X_last hT.2.2) (ht _).1) := by
      rw [chainOf, hdec]
      exact hseam
    have e1 := hY.unique hY'
    have hrem : (connectedSumSeamGrid Q₁ (G (Fin.last (m + k + 1))).2 (hQ₁.X_last hT.2.2)
        (ht _).1).MovesTo Q₁ := hs (Fin.last _) (by simp) _ Q₁ _ _
    obtain ⟨b', Q, hQ, hm⟩ := canonStack_removeSimple m U k (fun j => G j.castSucc)
      (fun j => ht _) (fun i hi => hs i.castSucc hi) hQ₁
    refine ⟨b', Q, ?_, (movesTo_of_sigma_eq e1).trans (hrem.trans hm)⟩
    exact hQ.of_sigma_eq (chainOf_sigma_congr _ _ fun j => congrArg G (Fin.ext rfl))

/-! ### The cleanup -/

/-- **The cleanup of the scissor endpoint from the marked factor cleanup.** -/
theorem scissorEndpointCleanupStatement_of_markedFactorCleanup
    (hmarked : MarkedFactorCleanupStatement) : ScissorEndpointCleanupStatement := by
  intro S N B hS hN F hzero _htrans
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  choose a P b E hP hPE hword hsimple hclean using hmarked S (m + 1) B hS F hzero
  -- the prepared factors
  let sizes : Fin (m + 1) → ℕ := fun j => a (Fin.castAdd B j) + 1
  let D : ∀ j, GridDiagram (sizes j) := fun j => P (Fin.castAdd B j)
  have hprep : SeamPrepared D :=
    { pos := fun j => by simp [sizes]
      first := fun _ => (hP _).2.2
      rest := fun j _ => ⟨(hP (Fin.castAdd B j)).1, (hP (Fin.castAdd B j)).2.1⟩ }
  refine ⟨sizes, D, hprep, fun j => by
    have := one_le_of_gridDiagram (P (Fin.castAdd B j)); simp [sizes]; omega,
    fun j => hword (Fin.castAdd B j) j.isLt, ?_⟩
  rintro K ⟨ℓ, hnd, hl, μ, hμ', rfl, hsort, hμ⟩
  -- notation
  let Pfam : Fin (m + 1 + B) → Σ e, GridDiagram (e + 1) := fun l => ⟨a l, P l⟩
  let k : Fin (m + 1 + B) → ℕ := fun l => S - F.cycleLength l
  have htE : ∀ l, TriplyPrepared (E l) := fun l => (hPE l).triplyPrepared (hP l)
  have hU : F.auxCount = ∑ l, k l := auxCount_eq F hS
  -- the singular part and the final target
  have htarget : ∀ {b' : ℕ} {Q : GridDiagram (b' + 1)},
      CanonStack (chainOf m (fun j => Pfam (Fin.castAdd B j)) fun j => hP _) (∑ l, k l) Q →
      ∃ (e : Fin (iteratedSeamSize sizes) → Fin (b' + 1)),
        FourMarkTower (iteratedSeamGrid D hprep) F.auxCount Q e := by
    intro b' Q hQ
    have hX0 := seamChainGrid_X_zero m (fun j => (Pfam (Fin.castAdd B j)).2)
      (fun j => (hP _).1) fun j => hP _
    obtain ⟨e, he, -, -⟩ := hQ.fourMarkTower hX0
    rw [hU]
    refine FourMarkTower.of_sigma_eq ?_ he
    rw [iteratedSeamGrid_succ]
    refine (seamChainGrid_sigma_congr _ _ fun j => ?_).trans (gridCast_sigma _ _).symm
    exact (gridCast_sigma _ _).symm
  by_cases hr : m + B = 0
  · -- a single factor
    obtain ⟨rfl, rfl⟩ : m = 0 ∧ B = 0 := ⟨by omega, by omega⟩
    set l₀ : Fin (0 + 1 + 0) := ⟨0, by omega⟩
    have h1 := endpoint_movesTo_framePrep F hS hnd hl hμ hμ' rfl
    have hG := isSignedWordGrid_localGrid F hS hnd hl hsort l₀
    have hc := hclean l₀ _ hG (closingRowBottom_localGrid F hS hnd hl l₀) 1 unknotTwo
      unknotTwo_triplyPrepared
    have h2 := (connectedSumSeamGrid_unknotTwo_movesTo (localFrame F hS hnd hl l₀)
      (framePrep_triplyPrepared _ _).1).symm
    have h3 := connectedSumSeamGrid_unknotTwo_movesTo (E l₀) (htE l₀).1
    obtain ⟨b', Y, hY, h4⟩ := (hPE l₀).exists_canonStack
    have hY' : CanonStack (chainOf 0 (fun j => Pfam (Fin.castAdd 0 j)) fun j => hP _)
        (∑ l, k l) Y := by
      have : (∑ l, k l) = k l₀ := by simp [l₀]
      rw [this]
      exact hY
    obtain ⟨e, he⟩ := htarget hY'
    exact ⟨_, Y, e, h1.trans (h2.trans (hc.trans (h3.trans h4))), he⟩
  · -- at least two factors
    obtain ⟨M, hM⟩ : ∃ M, m + 1 + B = M + 1 + 1 := ⟨m + B - 1, by omega⟩
    have h1 := endpoint_movesTo_seamChain F hS hnd hl hμ hμ' hsort M hM
    let Fam' : Fin (M + 1 + 1) → Σ e, GridDiagram (e + 1) :=
      fun i => ⟨b (Fin.cast hM.symm i), E (Fin.cast hM.symm i)⟩
    have htFam' : ∀ i, TriplyPrepared (Fam' i).2 := fun i => htE _
    let Fam : Fin (M + 1 + 1) → Σ e, GridDiagram (e + 1) :=
      fun i => ⟨factorSize F (Fin.cast hM.symm i), localFrame F hS hnd hl (Fin.cast hM.symm i)⟩
    have htFam : ∀ i, TriplyPrepared (Fam i).2 := fun i => framePrep_triplyPrepared
      (localGrid F hS hnd hl (Fin.cast hM.symm i)).toGrid (closingRowBottom_localGrid F hS hnd hl _)
    have hcl : ∀ i, CleansTo (Fam i) (Fam' i) := fun i =>
      ⟨htFam i, htFam' i, fun m' H hH _ _ =>
        hclean (Fin.cast hM.symm i) _ (isSignedWordGrid_localGrid F hS hnd hl hsort _)
          (closingRowBottom_localGrid F hS hnd hl _) m' H hH⟩
    have h2 := chainOf_movesTo_cleanAll M Fam Fam' htFam htFam' hcl
    have h3 := FrameTower.seamChain (M + 1) (fun i => P (Fin.cast hM.symm i))
      (fun i => E (Fin.cast hM.symm i)) (fun i => hP _) (fun i => htE _)
      (fun i => k (Fin.cast hM.symm i))
      fun i => hPE _
    obtain ⟨b₁, Y, hY, h4⟩ := h3.exists_canonStack
    have hsum : (∑ i : Fin (M + 1 + 1), k (Fin.cast hM.symm i)) = ∑ l, k l :=
      Fintype.sum_equiv (finCongr hM.symm) _ _ fun _ => rfl
    rw [hsum] at hY
    let Pfam' : Fin (m + B + 1) → Σ e, GridDiagram (e + 1) :=
      fun i => Pfam (Fin.cast (by omega) i)
    have hbase : (⟨_, seamChainGrid (M + 1) (fun i => P (Fin.cast hM.symm i))
        (fun j => (hP _).1)⟩ : Σ k, GridDiagram k) = ⟨_, chainOf (m + B) Pfam' fun l => hP _⟩ :=
      chainOf_sigma_cast (F := fun i => Pfam (Fin.cast hM.symm i)) (by omega) (fun i => hP _)
        (fun l => hP _) (fun j => congrArg Pfam (Fin.ext rfl))
    have hY' : CanonStack (chainOf (m + B) Pfam' fun l => hP _) (∑ l, k l) Y :=
      hY.of_sigma_eq hbase
    obtain ⟨b₂, Q, hQ, h5⟩ := canonStack_removeSimple m (∑ l, k l) B Pfam' (fun l => hP _)
      (fun i hi A G hG hA => hsimple (Fin.cast (by omega) i) (by simp; omega) A G hG) hY'
    obtain ⟨e, he⟩ := htarget (hQ.of_sigma_eq (chainOf_sigma_congr _ _ fun j =>
      congrArg Pfam (Fin.ext rfl)))
    exact ⟨_, Q, e, h1.trans (h2.trans (h4.trans h5)), he⟩

/-- **The combinatorial route from the marked factor cleanup.** -/
theorem scissorRouteStatement_of_markedFactorCleanup (hmarked : MarkedFactorCleanupStatement) :
    ScissorRouteStatement :=
  scissorRouteStatement_of_cleanup (scissorEndpointCleanupStatement_of_markedFactorCleanup hmarked)

end OnLeConjecture.KnotFloer.GridFull

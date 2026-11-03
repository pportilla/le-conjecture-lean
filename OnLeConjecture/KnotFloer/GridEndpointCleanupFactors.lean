/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridEndpointCleanupRelocate
public import OnLeConjecture.KnotFloer.GridEndpointCleanupMarkedStatement

/-!
# Successive factor cleanup in a seam chain

This file performs the successive cleanup of the factors of a seam chain of triply prepared grids,
as in the written proof of Statement E (`statement_E_complete_proof.tex`, Section 10, "The
invariant under marked inverse-pair cancellation"): the cyclic block rule exposes any factor as
the last factor of the chain, the exposed factor is replaced by its cleaned form while the seam of
the other factors is protected, and the chain is rotated back.

A triply prepared grid `A` *cleans to* a triply prepared grid `B` (`CleansTo`) if for every
triply prepared protected grid `H` the seam `Σ(H, A)` is related by grid moves to `Σ(H, B)`.

* `seamChainGrid_movesTo_cleanAt`: a factor that cleans to `B` can be replaced by `B` in a seam
  chain of at least two triply prepared factors.
* `seamChainGrid_movesTo_cleanAll`: if every factor cleans to a grid, then the seam chain is related
  by grid moves to the seam chain of the cleaned factors.
* `connectedSumSeamGrid_unknotTwo_movesTo`: the seam of the triply prepared `2 × 2` grid
  `unknotTwo` with any grid whose first `X` marking lies in row `0` is an `X` stabilization of
  it. This handles a chain with a single factor.

All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory

/-- `A` cleans to `B`: both are triply prepared, and the seam of any triply prepared grid `H`
with `A` is related by grid moves to its seam with `B`. -/
def CleansTo (A B : Σ e, GridDiagram (e + 1)) : Prop :=
  TriplyPrepared A.2 ∧ TriplyPrepared B.2 ∧
    ∀ (m : ℕ) (H : GridDiagram (m + 1)) (hH : TriplyPrepared H) (hA : TriplyPrepared A.2)
      (hB : TriplyPrepared B.2),
      (connectedSumSeamGrid H A.2 hH.2.2 hA.1).MovesTo (connectedSumSeamGrid H B.2 hH.2.2 hB.1)

/-- The seam chain of a triply prepared family given as a function to `Σ e, GridDiagram (e + 1)`. -/
abbrev chainOf (M : ℕ) (F : Fin (M + 1) → Σ e, GridDiagram (e + 1))
    (ht : ∀ j, TriplyPrepared (F j).2) : GridDiagram (seamChainSize M (fun j => (F j).1) + 1) :=
  seamChainGrid M (fun j => (F j).2) fun j => (ht j.succ).1

/-- Seam chains of pointwise equal families agree in `Σ k, GridDiagram k`. -/
theorem chainOf_sigma_congr {M : ℕ} {F F' : Fin (M + 1) → Σ e, GridDiagram (e + 1)}
    (ht : ∀ j, TriplyPrepared (F j).2) (ht' : ∀ j, TriplyPrepared (F' j).2)
    (h : ∀ j, F j = F' j) :
    (⟨_, chainOf M F ht⟩ : Σ k, GridDiagram k) = ⟨_, chainOf M F' ht'⟩ := by
  obtain rfl : F = F' := funext h
  rfl

/-- **Cleaning the last factor.** -/
theorem chainOf_movesTo_cleanLast (M : ℕ) (F : Fin (M + 1 + 1) → Σ e, GridDiagram (e + 1))
    (ht : ∀ j, TriplyPrepared (F j).2) (B : Σ e, GridDiagram (e + 1))
    (hc : CleansTo (F (Fin.last (M + 1))) B)
    (ht' : ∀ j, TriplyPrepared (Function.update F (Fin.last (M + 1)) B j).2) :
    (chainOf (M + 1) F ht).MovesTo
      (chainOf (M + 1) (Function.update F (Fin.last (M + 1)) B) ht') := by
  have hinit : ∀ j : Fin (M + 1),
      Function.update F (Fin.last (M + 1)) B j.castSucc = F j.castSucc :=
    fun j => Function.update_of_ne (Fin.castSucc_ne_last j) _ _
  have hlast : Function.update F (Fin.last (M + 1)) B (Fin.last (M + 1)) = B :=
    Function.update_self _ _ _
  rw [chainOf, chainOf, seamChainGrid_succ_of_triplyPrepared M _ _ ht,
    seamChainGrid_succ_of_triplyPrepared M _ _ ht']
  have hS := seamChainGrid_triplyPrepared M (fun j => (F j.castSucc).2)
    (fun j => (ht j.castSucc.succ).1) fun j => ht j.castSucc
  refine (hc.2.2 _ _ hS hc.1 hc.2.1).trans (movesTo_of_sigma_eq ?_)
  refine connectedSumSeamGrid_sigma_congr _ _ _ _ ?_ ?_
  · exact chainOf_sigma_congr (M := M) (fun j => ht j.castSucc) (fun j => ht' j.castSucc)
      fun j => (hinit j).symm
  · exact congrArg (fun A : Σ e, GridDiagram (e + 1) => (⟨A.1 + 1, A.2⟩ : Σ k, GridDiagram k))
      hlast.symm

/-- The rotation `finRotate n ^ (i + 1)` sends the last index to `i`. -/
theorem finRotate_pow_last {N : ℕ} (i : Fin (N + 1)) :
    (finRotate (N + 1) ^ (i.val + 1)) (Fin.last N) = i := by
  apply Fin.ext
  rw [val_finRotate_pow _ (by omega)]
  simp only [natRot, Fin.val_last]
  split_ifs <;> omega

/-- **Cleaning one factor of a seam chain.** -/
theorem chainOf_movesTo_cleanAt (M : ℕ) (F : Fin (M + 1 + 1) → Σ e, GridDiagram (e + 1))
    (ht : ∀ j, TriplyPrepared (F j).2) (i : Fin (M + 1 + 1)) (B : Σ e, GridDiagram (e + 1))
    (hc : CleansTo (F i) B) (ht' : ∀ j, TriplyPrepared (Function.update F i B j).2) :
    (chainOf (M + 1) F ht).MovesTo (chainOf (M + 1) (Function.update F i B) ht') := by
  set ρ := finRotate (M + 1 + 1) ^ (i.val + 1) with hρ
  have hρl : ρ (Fin.last (M + 1)) = i := finRotate_pow_last i
  -- rotate so that `i` is last
  have h1 := seamChainGrid_movesTo_rotate_pow M (fun j => (F j).2) (fun j => (ht j.succ).1) ht
    (i.val + 1)
  -- clean the last factor of the rotated family
  set F₁ : Fin (M + 1 + 1) → Σ e, GridDiagram (e + 1) := fun j => F (ρ j) with hF₁
  have ht₁ : ∀ j, TriplyPrepared (F₁ j).2 := fun j => ht _
  have hc₁ : CleansTo (F₁ (Fin.last (M + 1))) B := by
    simp only [hF₁, hρl]; exact hc
  have ht₂ : ∀ j, TriplyPrepared (Function.update F₁ (Fin.last (M + 1)) B j).2 := by
    intro j
    by_cases hj : j = Fin.last (M + 1)
    · subst hj; rw [Function.update_self]; exact hc.2.1
    · rw [Function.update_of_ne hj]; exact ht _
  have h2 := chainOf_movesTo_cleanLast M F₁ ht₁ B hc₁ ht₂
  -- rotate back
  set k := (M + 1 + 1) - (i.val + 1) with hk
  have h3 := seamChainGrid_movesTo_rotate_pow M
    (fun j => (Function.update F₁ (Fin.last (M + 1)) B j).2) (fun j => (ht₂ j.succ).1) ht₂ k
  have hpow : finRotate (M + 1 + 1) ^ (M + 1 + 1) = 1 :=
    finRotate_pow_eq_one_of_apply_eq _ 0
      (Fin.ext (by rw [val_finRotate_pow _ le_rfl]; simp [natRot]))
  have hρk : ∀ j, ρ ((finRotate (M + 1 + 1) ^ k) j) = j := fun j => by
    rw [hρ, ← Equiv.Perm.mul_apply, ← pow_add, show i.val + 1 + k = M + 1 + 1 by omega, hpow]
    rfl
  have hkρ : ∀ j, (finRotate (M + 1 + 1) ^ k) (ρ j) = j := fun j => by
    rw [hρ, ← Equiv.Perm.mul_apply, ← pow_add, show k + (i.val + 1) = M + 1 + 1 by omega, hpow]
    rfl
  have hfam : ∀ j, Function.update F₁ (Fin.last (M + 1)) B ((finRotate (M + 1 + 1) ^ k) j) =
      Function.update F i B j := by
    intro j
    by_cases hj : j = i
    · have hl : (finRotate (M + 1 + 1) ^ k) j = Fin.last (M + 1) := by
        rw [hj, ← hρl]; exact hkρ _
      rw [hl, Function.update_self, hj, Function.update_self]
    · have hne : (finRotate (M + 1 + 1) ^ k) j ≠ Fin.last (M + 1) := fun h =>
        hj (by rw [← hρk j, h, hρl])
      rw [Function.update_of_ne hne, Function.update_of_ne hj]
      simp only [hF₁, hρk]
  exact h1.trans (h2.trans (h3.trans (movesTo_of_sigma_eq
    (chainOf_sigma_congr (M := M + 1) (fun j => ht₂ _) ht' hfam))))

/-- The family whose first `t` factors are cleaned. -/
def partClean {N : ℕ} (F G : Fin N → Σ e, GridDiagram (e + 1)) (t : ℕ) :
    Fin N → Σ e, GridDiagram (e + 1) :=
  fun j => if j.val < t then G j else F j

/-- **Cleaning all factors of a seam chain.** If every factor of a triply prepared family of at
least two grids cleans to the corresponding factor of a second family, then the seam chains are
related by grid moves. -/
theorem chainOf_movesTo_cleanAll (M : ℕ) (F G : Fin (M + 1 + 1) → Σ e, GridDiagram (e + 1))
    (htF : ∀ j, TriplyPrepared (F j).2) (htG : ∀ j, TriplyPrepared (G j).2)
    (hc : ∀ j, CleansTo (F j) (G j)) :
    (chainOf (M + 1) F htF).MovesTo (chainOf (M + 1) G htG) := by
  have htP : ∀ t j, TriplyPrepared (partClean F G t j).2 := by
    intro t j
    by_cases h : j.val < t
    · have e : partClean F G t j = G j := if_pos h
      rw [e]; exact htG j
    · have e : partClean F G t j = F j := if_neg h
      rw [e]; exact htF j
  have key : ∀ t, t ≤ M + 1 + 1 →
      (chainOf (M + 1) F htF).MovesTo (chainOf (M + 1) (partClean F G t) (htP t)) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine movesTo_of_sigma_eq (chainOf_sigma_congr _ _ fun j => ?_)
      simp [partClean]
    | succ t ih =>
      intro ht
      have hupd : ∀ j, Function.update (partClean F G t) ⟨t, by omega⟩ (G ⟨t, by omega⟩) j =
          partClean F G (t + 1) j := by
        intro j
        by_cases hj : j = ⟨t, by omega⟩
        · subst hj
          simp [partClean]
        · rw [Function.update_of_ne hj]
          have hj' : j.val ≠ t := fun h => hj (Fin.ext h)
          simp only [partClean]
          split_ifs <;> first | rfl | omega
      have hct : CleansTo (partClean F G t ⟨t, by omega⟩) (G ⟨t, by omega⟩) := by
        simp only [partClean, lt_irrefl, if_false]
        exact hc _
      have ht' : ∀ j, TriplyPrepared
          (Function.update (partClean F G t) ⟨t, by omega⟩ (G ⟨t, by omega⟩) j).2 := by
        intro j; rw [hupd]; exact htP _ _
      exact (ih (by omega)).trans ((chainOf_movesTo_cleanAt M _ (htP t) _ _ hct ht').trans
        (movesTo_of_sigma_eq (chainOf_sigma_congr _ _ hupd)))
  refine (key _ le_rfl).trans (movesTo_of_sigma_eq (chainOf_sigma_congr _ _ fun j => ?_))
  simp [partClean, j.isLt]

/-! ### The single factor -/

/-- The permutation of `Fin 2` with values `(1, 0)`. -/
def unknotTwoO : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- The triply prepared grid of size two: `O = (1, 0)` and `X = (0, 1)`. -/
def unknotTwo : GridDiagram 2 where
  O := ⟨unknotTwoO⟩
  X := ⟨1⟩
  disjoint := by decide

theorem unknotTwo_triplyPrepared : TriplyPrepared unknotTwo := ⟨by decide, by decide, by decide⟩

/-- The seam of `unknotTwo` with a grid `G` whose first `X` marking lies in row `0` is the `X`
stabilization of `G` that splits this marking, with the new column `0` and the new row `1`. -/
theorem connectedSumSeamGrid_unknotTwo_eq {m : ℕ} (G : GridDiagram (m + 1)) (hG : G.X 0 = 0) :
    connectedSumSeamGrid unknotTwo G unknotTwo_triplyPrepared.2.2 hG =
      gridCast (by omega) (G.stabilizeX 0 1 0) := by
  have hG0 : gridRowVal G.X 0 = 0 := by
    have := gridRowVal_val G.X 0; rw [hG] at this; simpa using this
  have hGX : ∀ j, 0 < j → j < m + 1 → gridRowVal G.X j ≠ 0 := by
    intro j hj0 hj h
    rw [gridRowVal_mk _ _ hj] at h
    have : G.X ⟨j, hj⟩ = G.X 0 := by rw [hG]; exact Fin.ext h
    have := congrArg Fin.val (G.X.toPerm.injective this)
    simp at this
    omega
  have hU0 : gridRowVal unknotTwo.O 0 = 1 := rfl
  have hU1 : gridRowVal unknotTwo.O 1 = 0 := rfl
  have hV0 : gridRowVal unknotTwo.X 0 = 0 := rfl
  have hV1 : gridRowVal unknotTwo.X 1 = 1 := rfl
  apply gridDiagram_ext_gridRowVal
  · intro k hk
    rw [gridRowVal_gridCast_O, gridRowVal_seam_O, GridDiagram.stabilizeX_O,
      gridRowVal_insertPoint]
    unfold seamFun natSuccAbove natPredAbove
    by_cases hk0 : k = 0
    · subst hk0; simpa using hU0
    · simp only [Fin.val_zero, Fin.val_one, hU1, show ¬ k < 1 by omega,
        show k < 1 + m + 1 by omega, hk0, show k < m + 1 + 1 by omega, show ¬ k < 0 by omega,
        ↓reduceIte]
      split_ifs <;> omega
  · intro k hk
    rw [gridRowVal_gridCast_X, gridRowVal_seam_X, GridDiagram.stabilizeX_X,
      gridRowVal_splitPoint]
    unfold seamFun natSuccAbove natPredAbove
    by_cases hk0 : k = 0
    · subst hk0; simpa [hG0] using hV0
    · by_cases hk1 : k = 1
      · subst hk1; simpa [hG0] using hV1
      · have hv := hGX (k - 1) (by omega) (by omega)
        simp only [Fin.val_zero, Fin.val_one, show ¬ k < 1 by omega,
          show k < 1 + m + 1 by omega, hk0, hk1, show k < m + 1 + 1 by omega,
          show ¬ k < 0 by omega, show ¬ (0 : ℕ) < 0 by omega,
          show (0 : ℕ) + 1 = 1 by omega, hv, ↓reduceIte]
        split_ifs <;> omega

/-- The seam of `unknotTwo` with a grid `G` whose first `X` marking lies in row `0` is related to
`G` by grid moves. -/
theorem connectedSumSeamGrid_unknotTwo_movesTo {m : ℕ} (G : GridDiagram (m + 1))
    (hG : G.X 0 = 0) :
    (connectedSumSeamGrid unknotTwo G unknotTwo_triplyPrepared.2.2 hG).MovesTo G := by
  rw [connectedSumSeamGrid_unknotTwo_eq G hG]
  refine (movesTo_gridCast _ _).symm.trans ?_
  have hs : GridDiagram.IsXStabilization G (G.stabilizeX 0 1 0) := by
    apply GridDiagram.isXStabilization_stabilizeX
    · left
      exact Fin.ext (by
        rw [val_finRotate_of_lt _ (by simp), val_succAbove_eq_natSuccAbove]
        simp [natSuccAbove])
    · right
      have h1 : (1 : Fin (m + 1 + 1)).succAbove (G.X 0) = 0 := by
        rw [hG]; exact Fin.ext (by rw [val_succAbove_eq_natSuccAbove]; simp [natSuccAbove])
      rw [h1]
      exact Fin.ext (by rw [val_finRotate_of_lt _ (by simp)]; simp)
  exact (GridDiagram.IsStabilization.movesTo ((GridDiagram.isStabilization_iff _ _).mpr
    (Or.inr hs))).symm

end OnLeConjecture.KnotFloer.GridFull

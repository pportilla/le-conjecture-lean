/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridCanonicalMoves
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Choosing factor grids with a unit-coefficient seam

One supported X stabilization and cyclic row and column moves place the
second factor's shared X in column zero and its O in the last column of
that row. The move sequence preserves the proved canonical threshold.
This is a combinatorial grid statement, without a geometric realization claim.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
variable {n : ℕ}

theorem cyclicRows_pow_movesTo (G : GridDiagram n) (k : ℕ) :
    G.MovesTo (G.relabelRows ((finRotate n) ^ k)) := by
  induction k with
  | zero =>
    rw [pow_zero]
    change G.MovesTo (G.relabelRows (Equiv.refl _))
    rw [GridDiagram.relabelRows_refl]
  | succ k ih =>
    have hs := (G.relabelRows ((finRotate n) ^ k)).cyclicRows_movesTo
    rw [GridDiagram.relabelRows_relabelRows] at hs
    have hp : ((finRotate n) ^ k).trans (finRotate n) = (finRotate n) ^ (k + 1) := by
      ext c
      simp only [Equiv.trans_apply, pow_succ', Equiv.Perm.mul_apply]
    rw [hp] at hs
    exact ih.trans hs

theorem exists_cyclicRows_send (hn : 2 ≤ n) (a b : Fin n) :
    ∃ k : ℕ, ((finRotate n) ^ k) a = b := by
  have hne (c : Fin n) : finRotate n c ≠ c := by
    apply Equiv.Perm.mem_support.mp
    rw [support_finRotate_of_le hn]
    exact Finset.mem_univ _
  exact ((isCycle_finRotate_of_le hn).sameCycle (hne a) (hne b)).exists_nat_pow_eq

/-- A first-factor shared X can be placed at the final corner using only cyclic rows. -/
theorem exists_seamLeftGrid (G : GridDiagram (n + 1)) (hn : 2 ≤ n + 1) :
    ∃ H : GridDiagram (n + 1), G.MovesTo H ∧ H.X (Fin.last n) = Fin.last n ∧
      ∀ t : ℝ, gridCanonicalSpectralValue H t = gridCanonicalSpectralValue G t := by
  obtain ⟨k, hk⟩ := exists_cyclicRows_send hn (G.X (Fin.last n)) (Fin.last n)
  let H := G.relabelRows ((finRotate (n + 1)) ^ k)
  have hm : G.MovesTo H := cyclicRows_pow_movesTo G k
  exact ⟨H, hm, hk, fun t => (gridCanonicalSpectralValue_movesTo hm t).symm⟩

/-- The prepared second factor is obtained by actual allowed moves, with no extra
normalization hypothesis on the original factor. -/
theorem exists_seamPreparedGrid (G : GridDiagram (n + 1)) :
    ∃ H : GridDiagram (n + 2), G.MovesTo H ∧ H.X 0 = 0 ∧
      H.O (Fin.last (n + 1)) = 0 ∧
      ∀ t : ℝ, gridCanonicalSpectralValue H t = gridCanonicalSpectralValue G t := by
  let s : Fin (n + 1) := Fin.last n
  let q : Fin (n + 2) := (G.X s).castSucc
  let A := G.stabilizeX s.castSucc q s
  let B := A.relabelColumns (finRotate (n + 2))
  have hs : s.succ = Fin.last (n + 1) := rfl
  have hInvZero : (finRotate (n + 2)).symm 0 = Fin.last (n + 1) :=
    (finRotate (n + 2)).symm_apply_eq.mpr finRotate_last.symm
  have hInvLast : (finRotate (n + 2)).symm (Fin.last (n + 1)) = s.castSucc := by
    apply (finRotate (n + 2)).symm_apply_eq.mpr
    apply Fin.ext
    rw [coe_finRotate_of_ne_last]
    · simp [s]
    · intro h
      have := congrArg Fin.val h
      simp [s] at this
  have hX : B.X 0 = q := by
    change A.X ((finRotate (n + 2)).symm 0) = q
    rw [hInvZero, ← hs]
    change (G.stabilizeX s.castSucc q s).X s.succ = q
    rw [GridDiagram.stabilizeX_castSucc_X]
    exact GridState.insertPoint_apply_newColumn _ _ _
  have hO : B.O (Fin.last (n + 1)) = q := by
    change A.O ((finRotate (n + 2)).symm (Fin.last (n + 1))) = q
    rw [hInvLast]
    dsimp only [A]
    rw [GridDiagram.stabilizeX_O]
    exact GridState.insertPoint_apply_newColumn _ _ _
  have hGA : G.MovesTo A :=
    ((GridDiagram.isStabilization_iff G A).mpr
      (Or.inr (G.isXStabilization_stabilizeX_castSucc s))).movesTo
  have hGB : G.MovesTo B := hGA.trans A.cyclicColumns_movesTo
  obtain ⟨k, hk⟩ := exists_cyclicRows_send (by omega : 2 ≤ n + 2) q 0
  let H := B.relabelRows ((finRotate (n + 2)) ^ k)
  have hm : G.MovesTo H := hGB.trans (cyclicRows_pow_movesTo B k)
  refine ⟨H, hm, ?_, ?_, fun t => (gridCanonicalSpectralValue_movesTo hm t).symm⟩
  · change ((finRotate (n + 2)) ^ k) (B.X 0) = 0
    rw [hX, hk]
  · change ((finRotate (n + 2)) ^ k) (B.O (Fin.last (n + 1))) = 0
    rw [hO, hk]

/-- Preparation preserves the actual normalized canonical-class thresholds at every parameter. -/
theorem exists_seamPreparedGrid_canonical_threshold (G : GridDiagram (n + 1))
    (hn : 2 ≤ n + 1) :
    ∃ H : GridDiagram (n + 2), G.MovesTo H ∧ H.X 0 = 0 ∧
      H.O (Fin.last (n + 1)) = 0 ∧
      ∀ t : ℝ,
        ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
          (gridCanonicalClass G hn) =
        ((laurentMaslovBifiltration H (ZMod 2)).weighted t).spectralThreshold 0
          (gridCanonicalClass H (by omega)) := by
  obtain ⟨H, hm, hX, hO, _⟩ := exists_seamPreparedGrid G
  exact ⟨H, hm, hX, hO, fun t =>
    gridCanonicalClass_spectralThreshold_movesTo G H hn (by omega) hm t⟩

end OnLeConjecture.KnotFloer.GridFull

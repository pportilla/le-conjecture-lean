/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridHorizontalArcSets
public import OnLeConjecture.KnotTheory.PositiveBraidGridRowInterpolation

/-! # Native grid markings realized by one smooth row-offset function

The offset is constant on each entire original horizontal arc, including its
corners and cyclic seam. The same separated arc rows define both native marking
permutations. Its proved Lipschitz bound supplies the embedded shear deformation.
-/

@[expose] public noncomputable section
open Set
open scoped Topology ContDiff

namespace OnLeConjecture.KnotTheory

/-- Arbitrarily small separated rows and their native grid are realized by a smooth
offset on the literal base-row cylinder. No geometric realization certificate is an input. -/
theorem exists_positiveRectilinearWordGrid_smooth_row_offset {m : ℕ}
    (w : PositiveAdjacentWord m) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : Fin w.length × Fin 3 → ℝ)
      (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
      (q : ℂ × ℝ → ℝ),
      Function.Injective g ∧
      (∀ p, |g p - positiveRectilinearWordArcRow w p| < ε) ∧
      (∀ p p', positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w p' →
        g p < g p') ∧
      StrictMono row ∧
      (∀ p, row (G.O (finProdFinEquiv p)) = g p) ∧
      (∀ p, row (G.X (finProdFinEquiv p)) =
        g ((positiveRectilinearWordMatching w).symm p)) ∧
      ContDiff ℝ ∞ q ∧ LipschitzWith (1 / 2) q ∧
      (∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
        q p = g ((positiveRectilinearOutgoingArc w).symm a) -
          positiveRectilinearHorizontalArcRow w a) := by
  classical
  let K := fun p : Fin w.length × Fin 3 =>
    positiveRectilinearHorizontalArcSet w (positiveRectilinearOutgoingArc w p)
  have hK : ∀ p, IsCompact (K p) := fun _ => positiveRectilinearHorizontalArcSet_isCompact w _
  have hd : ∀ p r, p ≠ r → Disjoint (K p) (K r) := fun _ _ h =>
    positiveRectilinearHorizontalArcSet_disjoint w
      (fun he => h ((positiveRectilinearOutgoingArc w).injective he))
  obtain ⟨η, hη, hinterp⟩ := exists_positiveGridRowInterpolation_tolerance K hK hd
    (positiveRectilinearWordArcRow w)
  obtain ⟨g, hg, hclose, horder⟩ := exists_injective_row_perturbation
    (positiveRectilinearWordArcRow w) (lt_min hε hη)
  obtain ⟨G, row, hrow, hO, hX⟩ := exists_positiveRectilinearWordGrid_of_injective w g hg
  obtain ⟨q, hqs, hq, heq⟩ := hinterp g (fun p => (hclose p).trans_le (min_le_right _ _))
  refine ⟨g, G, row, q, hg, (fun p => (hclose p).trans_le (min_le_left _ _)),
    horder, hrow, hO, hX, hqs, hq, ?_⟩
  intro a p hp
  simpa only [K, Equiv.apply_symm_apply, positiveRectilinearWordArcRow_outgoing] using
    heq ((positiveRectilinearOutgoingArc w).symm a) p
      (by simpa only [K, Equiv.apply_symm_apply] using hp)

/-- On any point of an original horizontal arc, the constructed shear realizes its
unique new grid row and leaves the base phase and crossing depth unchanged. -/
theorem positiveRectilinearHorizontalArc_shear_row {m : ℕ} (w : PositiveAdjacentWord m)
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (a : PositiveRectilinearHorizontalArc w) (p : Circle × ℂ)
    (hp : ((p.1 : ℂ), p.2.re) ∈ positiveRectilinearHorizontalArcSet w a) :
    (positiveGridRowShearCylinder q 1 p).1 = p.1 ∧
      (positiveGridRowShearCylinder q 1 p).2.re = g ((positiveRectilinearOutgoingArc w).symm a) ∧
      (positiveGridRowShearCylinder q 1 p).2.im = p.2.im := by
  have hr : p.2.re = positiveRectilinearHorizontalArcRow w a := by
    obtain ⟨x, _, he⟩ := hp
    exact (congrArg Prod.snd he).symm
  apply positiveGridRowShearCylinder_row
  rw [hq a _ hp, hr]

end OnLeConjecture.KnotTheory

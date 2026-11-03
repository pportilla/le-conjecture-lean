/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridCanonicalSymmetry
public import OnLeConjecture.KnotFloer.GridCanonicalHalfTurn
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Move.Stabilization

/-!
# The normalized spectral threshold under all grid moves

The pinned combinatorial reduction connects every X or O stabilization to one
of two opposite X corners by cyclic translations and commutations. The proved
first-summand map covers one corner, and the native half-turn covers the other.
Consequently the canonical F₂ threshold is invariant under the complete grid
move relation.

The value assigned to the empty grid is zero by convention. No normalized class
is claimed for that grid. All nonempty grid diagrams have size at least two.
The quotient used here is the combinatorial `TauCeti.GridLink`. Identifying that
quotient with embedded links is a separate theorem.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti

variable {n k : ℕ}

/-- A grid admitting a column has size at least two, since a size-one grid cannot exist. -/
theorem grid_size_two_le_of_column (G : GridDiagram n) (s : Fin n) : 2 ≤ n := by
  by_contra hn
  have h : n = 1 := by have := s.isLt; omega
  subst n
  exact isEmptyElim G

/-- The canonical threshold, with value zero on the empty grid by convention. -/
def gridCanonicalSpectralValue (G : GridDiagram n) (t : ℝ) : EReal :=
  if hn : 2 ≤ n then
    ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
      (gridCanonicalClass G hn)
  else 0

/-- On grids of size at least two the value is the threshold of the proved canonical class. -/
theorem gridCanonicalSpectralValue_eq (G : GridDiagram n) (hn : 2 ≤ n) (t : ℝ) :
    gridCanonicalSpectralValue G t =
      ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
        (gridCanonicalClass G hn) := by
  simp only [gridCanonicalSpectralValue, dif_pos hn]

/-- The convention on the empty grid does not select a homology class. -/
@[simp] theorem gridCanonicalSpectralValue_empty (G : GridDiagram 0) (t : ℝ) :
    gridCanonicalSpectralValue G t = 0 := by simp [gridCanonicalSpectralValue]

/-- Cyclic row translations preserve the value. -/
theorem gridCanonicalSpectralValue_cyclicRows (G : GridDiagram n) (t : ℝ) :
    gridCanonicalSpectralValue G t =
      gridCanonicalSpectralValue (G.relabelRows (finRotate n)) t := by
  by_cases hn : 2 ≤ n
  · simp only [gridCanonicalSpectralValue_eq _ hn]
    exact (gridCanonicalClass_spectralThreshold_cyclicRows G hn t).symm
  · simp [gridCanonicalSpectralValue, hn]

/-- Cyclic column translations preserve the value. -/
theorem gridCanonicalSpectralValue_cyclicColumns (G : GridDiagram n) (t : ℝ) :
    gridCanonicalSpectralValue G t =
      gridCanonicalSpectralValue (G.relabelColumns (finRotate n)) t := by
  by_cases hn : 2 ≤ n
  · simp only [gridCanonicalSpectralValue_eq _ hn]
    exact (gridCanonicalClass_spectralThreshold_cyclicColumns G hn t).symm
  · simp [gridCanonicalSpectralValue, hn]

/-- Every validated row or column commutation preserves the value. -/
theorem gridCanonicalSpectralValue_commutation {G H : GridDiagram n}
    (h : GridDiagram.IsCommutation G H) (t : ℝ) :
    gridCanonicalSpectralValue G t = gridCanonicalSpectralValue H t := by
  by_cases hn : 2 ≤ n
  · simp only [gridCanonicalSpectralValue_eq _ hn]
    exact (gridCanonicalClass_spectralThreshold_of_isCommutation G H hn h t).symm
  · simp [gridCanonicalSpectralValue, hn]

/-- The original supported stabilization corner preserves the value. -/
theorem gridCanonicalSpectralValue_stabilization_castSucc (G : GridDiagram n)
    (s : Fin n) (t : ℝ) :
    gridCanonicalSpectralValue G t =
      gridCanonicalSpectralValue (G.stabilizeX s.castSucc (G.X s).castSucc s) t := by
  have hn := grid_size_two_le_of_column G s
  rw [gridCanonicalSpectralValue_eq G hn,
    gridCanonicalSpectralValue_eq _ (show 2 ≤ n + 1 by omega)]
  exact (gridCanonicalClass_spectralThreshold_stabilization G hn s t).symm

/-- The opposite stabilization corner preserves the value by the native half-turn. -/
theorem gridCanonicalSpectralValue_stabilization_succ (G : GridDiagram n)
    (s : Fin n) (t : ℝ) :
    gridCanonicalSpectralValue G t =
      gridCanonicalSpectralValue (G.stabilizeX s.succ (G.X s).succ s) t := by
  have hn := grid_size_two_le_of_column G s
  rw [gridCanonicalSpectralValue_eq G hn,
    gridCanonicalSpectralValue_eq _ (show 2 ≤ n + 1 by omega)]
  exact (gridCanonicalClass_spectralThreshold_stabilization_succ G hn s t).symm

/-- All eight X/O stabilization corners, including wrapped insertions, preserve the value. -/
theorem gridCanonicalSpectralValue_stabilization {G : GridDiagram n}
    {H : GridDiagram (n + 1)} (h : GridDiagram.IsStabilization G H) (t : ℝ) :
    gridCanonicalSpectralValue G t = gridCanonicalSpectralValue H t :=
  GridDiagram.IsStabilization.apply_eq_apply (fun _ G => gridCanonicalSpectralValue G t)
    (fun G => gridCanonicalSpectralValue_cyclicRows G t)
    (fun G => gridCanonicalSpectralValue_cyclicColumns G t)
    (fun h => gridCanonicalSpectralValue_commutation h t)
    (fun G s => gridCanonicalSpectralValue_stabilization_castSucc G s t)
    (fun G s => gridCanonicalSpectralValue_stabilization_succ G s t) h

/-- A spectral function on the combinatorial quotient by all grid moves. -/
def gridLinkSpectralThreshold (L : GridLink) (t : ℝ) : EReal :=
  GridLink.lift (fun _ G => gridCanonicalSpectralValue G t)
    (fun G => gridCanonicalSpectralValue_cyclicRows G t)
    (fun G => gridCanonicalSpectralValue_cyclicColumns G t)
    (fun h => gridCanonicalSpectralValue_commutation h t)
    (fun h => gridCanonicalSpectralValue_stabilization h t) L

/-- On a presenting diagram the quotient function is its canonical spectral value. -/
@[simp] theorem gridLinkSpectralThreshold_toGridLink (G : GridDiagram n) (t : ℝ) :
    gridLinkSpectralThreshold G.toGridLink t = gridCanonicalSpectralValue G t := rfl

/-- Every sequence of the exact elementary grid moves preserves the value. -/
theorem gridCanonicalSpectralValue_movesTo {G : GridDiagram n} {H : GridDiagram k}
    (h : GridDiagram.MovesTo G H) (t : ℝ) :
    gridCanonicalSpectralValue G t = gridCanonicalSpectralValue H t :=
  congrArg (fun L => gridLinkSpectralThreshold L t)
    ((GridDiagram.toGridLink_eq_iff_movesTo G).mpr h)

/-- The actual canonical-class thresholds agree for any two nonempty move-equivalent grids. -/
theorem gridCanonicalClass_spectralThreshold_movesTo (G : GridDiagram n) (H : GridDiagram k)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (h : GridDiagram.MovesTo G H) (t : ℝ) :
    ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
      (gridCanonicalClass G hn) =
        ((laurentMaslovBifiltration H (ZMod 2)).weighted t).spectralThreshold 0
          (gridCanonicalClass H hk) := by
  rw [← gridCanonicalSpectralValue_eq G hn, ← gridCanonicalSpectralValue_eq H hk]
  exact gridCanonicalSpectralValue_movesTo h t

end OnLeConjecture.KnotFloer.GridFull

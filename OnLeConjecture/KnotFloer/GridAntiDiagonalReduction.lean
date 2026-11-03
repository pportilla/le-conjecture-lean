/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCyclicFiltration
public import OnLeConjecture.KnotFloer.GridStabilizationCriticalGenerators
public import OnLeConjecture.KnotFloer.GridPolynomialLatticeRestrictionHomology
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Stabilization.Basic
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Unknot.Basic

/-!
# An explicit stabilization sequence with anti-diagonal O markings

Starting from a cyclic row translation of the two-by-two grid, stabilize the
last column at every step. The resulting O permutation is reversal in every
size. Thus changing only X markings connects any anti-diagonal O grid to this
explicit sequence at the level of the full Laurent complex and its polynomial
lattice. This does not identify the transferred stabilization differential.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

/-- The auxiliary grids are obtained by a specified local X stabilization at each step. -/
def antiDiagonalAuxiliaryGrid : (n : ℕ) → GridDiagram (n + 2)
  | 0 => GridDiagram.twoByTwo.relabelRows (finRotate 2)
  | n + 1 =>
    (antiDiagonalAuxiliaryGrid n).stabilizeX (Fin.last (n + 1)).castSucc
      ((antiDiagonalAuxiliaryGrid n).X (Fin.last (n + 1))).castSucc (Fin.last (n + 1))

/-- The base auxiliary grid is the actual cyclic row translation of the two-by-two grid. -/
theorem antiDiagonalAuxiliaryGrid_zero :
    antiDiagonalAuxiliaryGrid 0 = GridDiagram.twoByTwo.relabelRows (finRotate 2) := rfl

/-- The exact stabilization used by the already constructed local comparison maps. -/
theorem antiDiagonalAuxiliaryGrid_succ (n : ℕ) :
    antiDiagonalAuxiliaryGrid (n + 1) =
      (antiDiagonalAuxiliaryGrid n).stabilizeX (Fin.last (n + 1)).castSucc
        ((antiDiagonalAuxiliaryGrid n).X (Fin.last (n + 1))).castSucc (Fin.last (n + 1)) := rfl

/-- The split X marking is always in row one. -/
theorem antiDiagonalAuxiliaryGrid_X_last (n : ℕ) :
    (antiDiagonalAuxiliaryGrid n).X (Fin.last (n + 1)) = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [antiDiagonalAuxiliaryGrid_succ, GridDiagram.stabilizeX_castSucc_X]
    change ((antiDiagonalAuxiliaryGrid n).X.insertPoint (Fin.last (n + 2))
      ((antiDiagonalAuxiliaryGrid n).X (Fin.last (n + 1))).castSucc) (Fin.last (n + 2)) = 1
    rw [GridState.insertPoint_apply_newColumn, ih]
    apply Fin.ext
    simp

/-- The new O square is precisely on the anti-diagonal. -/
theorem antiDiagonalAuxiliaryGrid_newRow (n : ℕ) :
    ((antiDiagonalAuxiliaryGrid n).X (Fin.last (n + 1))).castSucc =
      (Fin.last (n + 1)).castSucc.rev := by
  rw [antiDiagonalAuxiliaryGrid_X_last]
  apply Fin.ext
  simp [Fin.rev]

/-- Every auxiliary grid has the required anti-diagonal O permutation. -/
theorem antiDiagonalAuxiliaryGrid_O_apply (n : ℕ) (c : Fin (n + 2)) :
    (antiDiagonalAuxiliaryGrid n).O c = c.rev := by
  induction n with
  | zero => fin_cases c <;> decide
  | succ n ih =>
    rw [antiDiagonalAuxiliaryGrid_succ, GridDiagram.stabilizeX_O,
      antiDiagonalAuxiliaryGrid_newRow]
    induction c using Fin.succAboveCases (Fin.last (n + 1)).castSucc with
    | x => exact GridState.insertPoint_apply_newColumn _ _ _
    | p c => rw [GridState.insertPoint_apply_succAbove, ih, Fin.rev_succAbove]

/-- Inserting row one commutes with the cyclic shift after embedding an old row by successor. -/
theorem finRotate_succAbove_one (n : ℕ) (i : Fin (n + 2)) :
    (1 : Fin (n + 3)).succAbove (finRotate (n + 2) i) =
      finRotate (n + 3) i.succ := by
  by_cases hi : i = Fin.last (n + 1)
  · subst i
    simp [Fin.succAbove]
  · have hi' : i.succ ≠ Fin.last (n + 2) := by
      intro h
      exact hi (Fin.succ_injective _ h)
    have h₁ := coe_finRotate_of_ne_last hi
    have h₂ := coe_finRotate_of_ne_last hi'
    have hle : (1 : Fin (n + 3)) ≤ (finRotate (n + 2) i).castSucc := by
      rw [Fin.le_def, Fin.val_one, Fin.val_castSucc, h₁]
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hle]
    apply Fin.ext
    rw [Fin.val_succ, h₁, h₂, Fin.val_succ]


/-- The auxiliary X markings are exactly the cyclic shift of reversal. -/
theorem antiDiagonalAuxiliaryGrid_X_apply (n : ℕ) (c : Fin (n + 2)) :
    (antiDiagonalAuxiliaryGrid n).X c = finRotate (n + 2) c.rev := by
  induction n with
  | zero => fin_cases c <;> decide
  | succ n ih =>
    rw [antiDiagonalAuxiliaryGrid_succ, GridDiagram.stabilizeX_castSucc_X,
      antiDiagonalAuxiliaryGrid_X_last]
    have hrow : (1 : Fin (n + 2)).castSucc = (1 : Fin (n + 3)) := by
      apply Fin.ext
      simp
    rw [hrow]
    induction c using Fin.lastCases with
    | last =>
      change ((antiDiagonalAuxiliaryGrid n).X.insertPoint (Fin.last (n + 2)) 1)
        (Fin.last (n + 2)) = _
      rw [GridState.insertPoint_apply_newColumn, Fin.rev_last]
      simp
    | cast c =>
      change ((antiDiagonalAuxiliaryGrid n).X.insertPoint (Fin.last (n + 2)) 1) c.castSucc = _
      conv_lhs => rw [← Fin.succAbove_last_apply]
      rw [GridState.insertPoint_apply_succAbove, ih, Fin.rev_castSucc]
      exact finRotate_succAbove_one n c.rev

/-- The auxiliary O state equals any given anti-diagonal O state. -/
theorem antiDiagonalAuxiliaryGrid_O_eq {n : ℕ} (G : GridDiagram (n + 2))
    (hO : ∀ c, G.O c = c.rev) : (antiDiagonalAuxiliaryGrid n).O = G.O :=
  GridState.ext fun c => (antiDiagonalAuxiliaryGrid_O_apply n c).trans (hO c).symm

/-- Every consecutive pair in the sequence is a permitted local X stabilization. -/
theorem antiDiagonalAuxiliaryGrid_isXStabilization (n : ℕ) :
    GridDiagram.IsXStabilization (antiDiagonalAuxiliaryGrid n)
      (antiDiagonalAuxiliaryGrid (n + 1)) := by
  rw [antiDiagonalAuxiliaryGrid_succ]
  exact (antiDiagonalAuxiliaryGrid n).isXStabilization_stabilizeX_castSucc (Fin.last (n + 1))

/-- The new X state is the explicit matching partner of the old X state. -/
theorem stabilizationPartnerState_X {n : ℕ} (G : GridDiagram n) (s : Fin n) :
    (stabilizationPartnerState G s G.X).val =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).X := by
  change (G.X.insertPoint s.succ (G.X s).succ).swapRows (G.X s).castSucc (G.X s).succ = _
  rw [← GridState.insertPoint_swapRows, GridState.swapRows_swapRows,
    GridDiagram.stabilizeX_castSucc_X]

variable (R : Type*) [CommRing R] [CharP R 2]

/-- The constructed full stabilization projection takes the new auxiliary X generator
exactly to the old X generator in the first copy. -/
theorem antiDiagonalAuxiliaryGrid_proj_X (n : ℕ) :
    (fullStabilizationTransferredRetraction (antiDiagonalAuxiliaryGrid n)
      (Fin.last (n + 1)) R).proj
        (Finsupp.single (antiDiagonalAuxiliaryGrid (n + 1)).X 1) =
          (Finsupp.single (antiDiagonalAuxiliaryGrid n).X 1, 0) := by
  rw [antiDiagonalAuxiliaryGrid_succ, ← stabilizationPartnerState_X]
  exact fullStabilizationTransferredRetraction_proj_partner_single
    (antiDiagonalAuxiliaryGrid n) (Fin.last (n + 1)) R (antiDiagonalAuxiliaryGrid n).X

/-- The initial auxiliary Laurent complex is obtained by the native cyclic row isomorphism. -/
def antiDiagonalAuxiliaryBaseIso :
    laurentMaslovComplex GridDiagram.twoByTwo R ≅
      laurentMaslovComplex (antiDiagonalAuxiliaryGrid 0) R :=
  laurentMaslovCyclicRowsIso GridDiagram.twoByTwo R

/-- The initial cyclic row map transports the entire polynomial homology image in every degree. -/
theorem antiDiagonalAuxiliaryBaseIso_polynomialImage (a b : Fin 2) (m : ℤ) :
    (polynomialHomologyImage R GridDiagram.twoByTwo a m).map
        (homologyMap (antiDiagonalAuxiliaryBaseIso R).hom m).hom =
      polynomialHomologyImage R (antiDiagonalAuxiliaryGrid 0) b m := by
  apply polynomialHomologyImage_map_eq_of_shifted_homotopyEquiv R
    GridDiagram.twoByTwo (antiDiagonalAuxiliaryGrid 0) a b
    (HomotopyEquiv.ofIso (antiDiagonalAuxiliaryBaseIso R)) 0 0
  · intro u v i x hx
    change (laurentMaslovCyclicRowsIso GridDiagram.twoByTwo R).hom.f i x ∈
      (laurentMaslovBifiltration (GridDiagram.twoByTwo.relabelRows (finRotate 2)) R).level
        (u + 0) (v + 0) i
    simpa only [add_zero] using
      laurentMaslovCyclicRows_preserves GridDiagram.twoByTwo R u v i x hx
  · intro u v i x hx
    change (laurentMaslovCyclicRowsIso GridDiagram.twoByTwo R).inv.f i x ∈
      (laurentMaslovBifiltration GridDiagram.twoByTwo R).level (u + 0) (v + 0) i
    simpa only [add_zero] using
      laurentMaslovCyclicRows_inv_preserves GridDiagram.twoByTwo R u v i x hx

/-- The base identification restricts to a linear equivalence of polynomial homology images. -/
def antiDiagonalAuxiliaryBasePolynomialImageEquiv (a b : Fin 2) (m : ℤ) :
    polynomialHomologyImage R GridDiagram.twoByTwo a m ≃ₗ[R]
      polynomialHomologyImage R (antiDiagonalAuxiliaryGrid 0) b m :=
  (homologyMapIso (antiDiagonalAuxiliaryBaseIso R) m).toLinearEquiv.ofSubmodules _ _
    (antiDiagonalAuxiliaryBaseIso_polynomialImage R a b m)

/-- The full native complexes agree after changing only the auxiliary X markings. -/
def antiDiagonalAuxiliaryMarkingIso {n : ℕ} (G : GridDiagram (n + 2))
    (hO : ∀ c, G.O c = c.rev) :
    laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R ≅ laurentMaslovComplex G R :=
  laurentMaslovMarkingIso R (antiDiagonalAuxiliaryGrid_O_eq G hO)

/-- The same marking change transports exactly the polynomial homology image. -/
theorem antiDiagonalAuxiliaryMarkingIso_polynomialImage {n : ℕ} (G : GridDiagram (n + 2))
    (hO : ∀ c, G.O c = c.rev) (a b : Fin (n + 2)) (m : ℤ) :
    (polynomialHomologyImage R (antiDiagonalAuxiliaryGrid n) a m).map
        (homologyMap (antiDiagonalAuxiliaryMarkingIso R G hO).hom m).hom =
      polynomialHomologyImage R G b m :=
  polynomialHomologyImage_map_markingIso R (antiDiagonalAuxiliaryGrid_O_eq G hO) a b m

end OnLeConjecture.KnotFloer.GridFull

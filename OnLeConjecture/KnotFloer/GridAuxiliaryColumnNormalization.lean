/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationFilteredEquivalence
public import OnLeConjecture.KnotFloer.GridReflectedTorusNormalization
public import OnLeConjecture.KnotFloer.GridPolynomialLatticeRestrictionHomology
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Polynomial homology normalization for arbitrary nonempty grids

Keeping the O markings and placing each X in the next row makes every pair
of columns noninterleaving. Adjacent column commutations can therefore sort
these O markings into anti-diagonal order. The constructed commutation maps
and marking isomorphisms transport the polynomial homology image to the
already computed anti-diagonal image.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ}

/-- Keep the O markings and place every X in the cyclically next row. -/
def adjacentRowAuxiliaryGrid (G : GridDiagram n) (hn : 2 ≤ n) : GridDiagram n where
  O := G.O
  X := G.O.relabelRows (finRotate n)
  disjoint c := (Grid.finRotate_ne_self hn (G.O c)).symm

@[simp] theorem adjacentRowAuxiliaryGrid_O (G : GridDiagram n) (hn : 2 ≤ n) :
    (adjacentRowAuxiliaryGrid G hn).O = G.O := rfl

@[simp] theorem adjacentRowAuxiliaryGrid_X (G : GridDiagram n) (hn : 2 ≤ n) (c : Fin n) :
    (adjacentRowAuxiliaryGrid G hn).X c = finRotate n (G.O c) := rfl

/-- All column pairs of the auxiliary grid satisfy the exact commutation condition. -/
theorem adjacentRowAuxiliaryGrid_noninterleaving (G : GridDiagram n) (hn : 2 ≤ n)
    (a b : Fin n) : (adjacentRowAuxiliaryGrid G hn).ColumnsNoninterleaving a b :=
  (adjacentRowAuxiliaryGrid G hn).columnsNoninterleaving_of_X_eq_finRotate_O rfl b

/-- Arbitrary column relabeling retains the adjacent-row marking condition. -/
theorem adjacentRowCondition_relabelColumns (G : GridDiagram n)
    (hG : ∀ c, G.X c = finRotate n (G.O c)) (κ : Equiv.Perm (Fin n)) :
    ∀ c, (G.relabelColumns κ).X c = finRotate n ((G.relabelColumns κ).O c) :=
  fun c => hG (κ.symm c)

variable (R : Type*) [CommRing R] [CharP R 2]

/-- Each validated commutation transports the polynomial image by its actual native maps. -/
def columnCommutationPolynomialImageEquiv (G : GridDiagram n)
    (C : GridDiagram.ColumnCommutationData G) (a : Fin n) (m : ℤ) :
    polynomialHomologyImage R G a m ≃ₗ[R]
      polynomialHomologyImage R (G.swapColumns C.column (finRotate n C.column)) a m :=
  polynomialHomologyImageEquivOfShiftedHomotopyEquiv R G _ a a
    (laurentMaslovCommutationHomotopyEquiv G R C) 0 0
    (Bifiltration.shifts_zero_zero_iff.mpr (laurentMaslovCommutationHom_preserves G R C))
    (Bifiltration.shifts_zero_zero_iff.mpr
      (laurentMaslovReverseCommutationHom_preserves G R C)) m

/-- Every adjacent swap is available on a grid with adjacent-row markings. -/
theorem adjacentRow_polynomialImage_equiv_swap {k : ℕ} (G : GridDiagram (k + 1))
    (hG : ∀ c, G.X c = finRotate (k + 1) (G.O c))
    (i : Fin k) (a : Fin (k + 1)) (m : ℤ) :
    Nonempty (polynomialHomologyImage R G a m ≃ₗ[R]
      polynomialHomologyImage R (G.relabelColumns (Equiv.swap i.castSucc i.succ)) a m) := by
  have hrot : finRotate (k + 1) i.castSucc = i.succ := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last (by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at this
      omega)]
    rfl
  have hne : i.castSucc ≠ finRotate (k + 1) i.castSucc := by
    rw [hrot]
    exact fun h => by have := congrArg Fin.val h; simp at this
  let C := GridDiagram.ColumnCommutationData.ofNoninterleaving i.castSucc hne
    (G.columnsNoninterleaving_of_X_eq_finRotate_O (hG i.castSucc) _)
  have hc : C.column = i.castSucc := GridDiagram.ColumnCommutationData.ofNoninterleaving_column ..
  have e := columnCommutationPolynomialImageEquiv R G C a m
  rw [hc, hrot] at e
  exact ⟨e⟩

/-- Adjacent-swap generation constructs image equivalences for every column permutation.
The induction composes the actual commutation-induced equivalences. -/
theorem adjacentRow_polynomialImage_equiv_relabel (G : GridDiagram n)
    (hG : ∀ c, G.X c = finRotate n (G.O c))
    (κ : Equiv.Perm (Fin n)) (a : Fin n) (m : ℤ) :
    Nonempty (polynomialHomologyImage R G a m ≃ₗ[R]
      polynomialHomologyImage R (G.relabelColumns κ) a m) := by
  cases n with
  | zero => exact Fin.elim0 a
  | succ k =>
    have hκ : κ ∈ Submonoid.closure
        (Set.range fun i : Fin k => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    have key : ∀ (τ : Equiv.Perm (Fin (k + 1))), τ ∈ Submonoid.closure
        (Set.range fun i : Fin k => Equiv.swap i.castSucc i.succ) →
        ∀ H : GridDiagram (k + 1), (∀ c, H.X c = finRotate (k + 1) (H.O c)) →
          Nonempty (polynomialHomologyImage R H a m ≃ₗ[R]
            polynomialHomologyImage R (H.relabelColumns τ) a m) := by
      intro τ hτ
      induction hτ using Submonoid.closure_induction with
      | mem τ hτ =>
        obtain ⟨i, rfl⟩ := hτ
        exact fun H hH => adjacentRow_polynomialImage_equiv_swap R H hH i a m
      | one =>
        intro H _
        exact ⟨LinearEquiv.refl R _⟩
      | mul τ υ _ _ hτ hυ =>
        intro H hH
        obtain ⟨eυ⟩ := hυ H hH
        obtain ⟨eτ⟩ := hτ (H.relabelColumns υ) (adjacentRowCondition_relabelColumns H hH υ)
        exact ⟨eυ.trans eτ⟩
    exact key κ hκ G hG

/-- Sorting the O columns of the auxiliary grid into anti-diagonal order. -/
def adjacentRowSortedGrid (G : GridDiagram n) (hn : 2 ≤ n) : GridDiagram n :=
  (adjacentRowAuxiliaryGrid G hn).relabelColumns (G.O.toPerm.trans Fin.revPerm)

/-- The sorted grid has exactly the anti-diagonal O marking. -/
theorem adjacentRowSortedGrid_O (G : GridDiagram n) (hn : 2 ≤ n) (c : Fin n) :
    (adjacentRowSortedGrid G hn).O c = c.rev := by
  change G.O.toPerm (G.O.toPerm.symm c.rev) = c.rev
  exact G.O.toPerm.apply_symm_apply c.rev

/-- Marking transport followed by admissible column commutations sorts the polynomial image. -/
def gridPolynomialImageSortEquiv (G : GridDiagram n) (hn : 2 ≤ n) (a : Fin n) (m : ℤ) :
    polynomialHomologyImage R G a m ≃ₗ[R]
      polynomialHomologyImage R (adjacentRowSortedGrid G hn) a m := by
  let A := adjacentRowAuxiliaryGrid G hn
  have hO : G.O = A.O := rfl
  let marking := (homologyMapIso (laurentMaslovMarkingIso R hO) m).toLinearEquiv
  let e := marking.ofSubmodules _ _ (polynomialHomologyImage_map_markingIso R hO a a m)
  exact e.trans (Classical.choice (adjacentRow_polynomialImage_equiv_relabel R A
    (fun _ => rfl) (G.O.toPerm.trans Fin.revPerm) a m))

/-- The degree-zero polynomial homology image of every grid of size at least two is R. -/
def gridPolynomialImageZeroEquiv (G : GridDiagram n) (hn : 2 ≤ n) (a : Fin n) :
    polynomialHomologyImage R G a 0 ≃ₗ[R] R :=
  (gridPolynomialImageSortEquiv R G hn a 0).trans
    (antiDiagonalPolynomialImageZeroEquiv R (adjacentRowSortedGrid G hn) hn
      (adjacentRowSortedGrid_O G hn) a)

/-- All positive-degree polynomial homology images vanish for grids of size at least two. -/
theorem grid_polynomialHomologyImage_eq_bot (G : GridDiagram n) (hn : 2 ≤ n)
    (a : Fin n) (m : ℤ) (hm : 0 < m) : polynomialHomologyImage R G a m = ⊥ := by
  apply le_antisymm _ bot_le
  intro ξ hξ
  let e := gridPolynomialImageSortEquiv R G hn a m
  have hz : e ⟨ξ, hξ⟩ = 0 := by
    apply Subtype.ext
    exact (antiDiagonal_polynomialHomologyImage_eq_bot R
      (adjacentRowSortedGrid G hn) hn (adjacentRowSortedGrid_O G hn) a m hm).le
        (e ⟨ξ, hξ⟩).property
  have hξ0 := e.injective (hz.trans e.map_zero.symm)
  exact congrArg Subtype.val hξ0

/-- Over F₂ every nonempty grid has exactly one nonzero degree-zero polynomial-image class. -/
theorem grid_existsUnique_polynomialHomologyImage_class
    (G : GridDiagram n) (hn : 2 ≤ n) (a : Fin n) :
    ∃! ξ : (laurentMaslovComplex G (ZMod 2)).homology 0,
      ξ ∈ polynomialHomologyImage (ZMod 2) G a 0 ∧ ξ ≠ 0 := by
  let H := adjacentRowSortedGrid G hn
  have hH : ∀ c, H.O c = c.rev := adjacentRowSortedGrid_O G hn
  let e := gridPolynomialImageSortEquiv (ZMod 2) G hn a 0
  let η : polynomialHomologyImage (ZMod 2) H a 0 :=
    ⟨antiDiagonalCornerNativeClass (ZMod 2) H hn hH,
      antiDiagonalCornerNativeClass_mem_polynomialHomologyImage (ZMod 2) H hn hH a⟩
  have hη : η ≠ 0 := fun h => antiDiagonalCornerNativeClass_ne_zero (ZMod 2) H hn hH
    (congrArg Subtype.val h)
  let ξ := e.symm η
  have hξ : ξ.val ≠ 0 := by
    intro h
    have hz : ξ = 0 := Subtype.ext h
    exact hη (by rw [← e.apply_symm_apply η]; change e ξ = 0; rw [hz, map_zero])
  refine ⟨ξ.val, ⟨ξ.property, hξ⟩, ?_⟩
  intro z hz
  have hez : (e ⟨z, hz.1⟩).val ≠ 0 := by
    intro h
    have he : e ⟨z, hz.1⟩ = 0 := Subtype.ext h
    have he' := e.injective (he.trans e.map_zero.symm)
    exact hz.2 (congrArg Subtype.val he')
  have heq : e ⟨z, hz.1⟩ = η := Subtype.ext
    (antiDiagonalCornerNativeClass_unique H hn hH a _ (e ⟨z, hz.1⟩).property hez)
  exact congrArg Subtype.val (e.injective (heq.trans (e.apply_symm_apply η).symm))

end OnLeConjecture.KnotFloer.GridFull

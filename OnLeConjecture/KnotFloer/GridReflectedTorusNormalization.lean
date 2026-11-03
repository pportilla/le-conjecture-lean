/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridAntiDiagonalNativeClass
public import OnLeConjecture.KnotFloer.GridAntiDiagonalPolynomialNormalization
public import OnLeConjecture.KnotFloer.GridReflectedTorusPolynomialClass

/-!
# The selected corner class in an anti-diagonal grid

The auxiliary stabilization sequence selects the constant corner cycle in every
anti-diagonal O grid. Its point formula agrees with the explicit reflected torus
anchor. These comparisons concern the constructed native grid complexes.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

/-- The corner permutation sends column c to minus c modulo the grid size. -/
def antiDiagonalCornerState (N : ℕ) : GridState N := ⟨reflectedPointRows N⟩

@[simp]
theorem antiDiagonalCornerState_apply (N : ℕ) (c : Fin N) :
    antiDiagonalCornerState N c = finRotate N c.rev := rfl

variable (R : Type*) [CommRing R] [CharP R 2]

/-- The auxiliary sequence's selected cycle, in any grid with anti-diagonal O markings. -/
def antiDiagonalCornerNativeCycle {N : ℕ} (G : GridDiagram N)
    (hN : 2 ≤ N) (hO : ∀ c, G.O c = c.rev) : (laurentMaslovComplex G R).cycles 0 := by
  cases N with
  | zero => omega
  | succ N =>
    cases N with
    | zero => omega
    | succ N => exact antiDiagonalAuxiliaryMarkingNativeCycle N R G hO

/-- Its underlying chain is precisely the constant corner generator. -/
theorem antiDiagonalCornerNativeCycle_apply {N : ℕ} (G : GridDiagram N)
    (hN : 2 ≤ N) (hO : ∀ c, G.O c = c.rev) :
    (laurentMaslovChainEquiv G R 0
      ((laurentMaslovComplex G R).iCycles 0 (antiDiagonalCornerNativeCycle R G hN hO)) :
        LaurentChain R N) = Finsupp.single (antiDiagonalCornerState N) 1 := by
  cases N with
  | zero => omega
  | succ N =>
    cases N with
    | zero => omega
    | succ N =>
      change (laurentMaslovChainEquiv G R 0
        ((laurentMaslovComplex G R).iCycles 0
          (antiDiagonalAuxiliaryMarkingNativeCycle N R G hO)) : LaurentChain R (N + 2)) = _
      rw [antiDiagonalAuxiliaryMarkingNativeCycle_apply]
      congr 1
      exact GridState.ext fun c => antiDiagonalAuxiliaryGrid_X_apply N c

/-- The selected corner class in native degree-zero homology. -/
def antiDiagonalCornerNativeClass {N : ℕ} (G : GridDiagram N)
    (hN : 2 ≤ N) (hO : ∀ c, G.O c = c.rev) : (laurentMaslovComplex G R).homology 0 :=
  (laurentMaslovComplex G R).homologyπ 0 (antiDiagonalCornerNativeCycle R G hN hO)

/-- The selected class is the actual same-O image of the tracked auxiliary class. -/
theorem antiDiagonalCornerNativeClass_eq_marking {N : ℕ} (G : GridDiagram (N + 2))
    (hO : ∀ c, G.O c = c.rev) :
    antiDiagonalCornerNativeClass R G (by omega) hO =
      homologyMap (antiDiagonalAuxiliaryMarkingIso R G hO).hom 0
        (antiDiagonalAuxiliaryNativeClass N R) := by
  have h := congrArg (fun f : (laurentMaslovComplex (antiDiagonalAuxiliaryGrid N) R).cycles 0 ⟶
      (laurentMaslovComplex G R).homology 0 => f (antiDiagonalAuxiliaryNativeCycle N R))
    (homologyπ_naturality (antiDiagonalAuxiliaryMarkingIso R G hO).hom 0)
  exact h.symm

/-- The constant corner cycle represents a nonzero Laurent homology class. -/
theorem antiDiagonalCornerNativeClass_ne_zero {N : ℕ} (G : GridDiagram N)
    (hN : 2 ≤ N) (hO : ∀ c, G.O c = c.rev) [Nontrivial R] :
    antiDiagonalCornerNativeClass R G hN hO ≠ 0 := by
  cases N with
  | zero => omega
  | succ N =>
    cases N with
    | zero => omega
    | succ N =>
      rw [antiDiagonalCornerNativeClass_eq_marking]
      exact (map_ne_zero_iff _
        (homologyMapIso (antiDiagonalAuxiliaryMarkingIso R G hO) 0).toLinearEquiv.injective).mpr
        (antiDiagonalAuxiliaryNativeClass_ne_zero R N)

/-- The selected nonzero class lies in every selected-variable polynomial homology image. -/
theorem antiDiagonalCornerNativeClass_mem_polynomialHomologyImage {N : ℕ}
    (G : GridDiagram N) (hN : 2 ≤ N) (hO : ∀ c, G.O c = c.rev) (a : Fin N) :
    antiDiagonalCornerNativeClass R G hN hO ∈ polynomialHomologyImage R G a 0 := by
  cases N with
  | zero => omega
  | succ N =>
    cases N with
    | zero => omega
    | succ N =>
      rw [antiDiagonalCornerNativeClass_eq_marking]
      exact antiDiagonalAuxiliaryMarkingNativeClass_mem_polynomialImage N R G hO 0 a

/-- The degree-zero polynomial image of an anti-diagonal O grid is the coefficient ring. -/
def antiDiagonalPolynomialImageZeroEquiv {N : ℕ}
    (G : GridDiagram N) (hN : 2 ≤ N) (hO : ∀ c, G.O c = c.rev) (a : Fin N) :
    polynomialHomologyImage R G a 0 ≃ₗ[R] R := by
  cases N with
  | zero => omega
  | succ N =>
    cases N with
    | zero => omega
    | succ N =>
      let e := (homologyMapIso (antiDiagonalAuxiliaryMarkingIso R G hO) 0).toLinearEquiv
      exact (e.ofSubmodules _ _
        (antiDiagonalAuxiliaryMarkingIso_polynomialImage R G hO 0 a 0)).symm.trans
          (antiDiagonalAuxiliaryPolynomialImageZeroEquiv R N 0)

/-- Positive-degree polynomial images vanish after changing only the auxiliary X markings. -/
theorem antiDiagonal_polynomialHomologyImage_eq_bot {N : ℕ}
    (G : GridDiagram N) (hN : 2 ≤ N) (hO : ∀ c, G.O c = c.rev) (a : Fin N)
    (m : ℤ) (hm : 0 < m) : polynomialHomologyImage R G a m = ⊥ := by
  cases N with
  | zero => omega
  | succ N =>
    cases N with
    | zero => omega
    | succ N =>
      rw [← antiDiagonalAuxiliaryMarkingIso_polynomialImage R G hO 0 a m,
        antiDiagonalAuxiliary_polynomialHomologyImage_eq_bot R N 0 m hm, Submodule.map_bot]

/-- Over F₂ the corner class is the unique nonzero degree-zero polynomial-image class. -/
theorem antiDiagonalCornerNativeClass_unique {N : ℕ}
    (G : GridDiagram N) (hN : 2 ≤ N) (hO : ∀ c, G.O c = c.rev) (a : Fin N)
    (ξ : (laurentMaslovComplex G (ZMod 2)).homology 0)
    (hmem : ξ ∈ polynomialHomologyImage (ZMod 2) G a 0) (hne : ξ ≠ 0) :
    ξ = antiDiagonalCornerNativeClass (ZMod 2) G hN hO := by
  cases N with
  | zero => omega
  | succ N =>
    cases N with
    | zero => omega
    | succ N =>
      rw [← antiDiagonalAuxiliaryMarkingIso_polynomialImage (ZMod 2) G hO 0 a 0] at hmem
      obtain ⟨z, hz, rfl⟩ := hmem
      rw [antiDiagonalCornerNativeClass_eq_marking]
      exact congrArg (homologyMap (antiDiagonalAuxiliaryMarkingIso (ZMod 2) G hO).hom 0)
        (antiDiagonalAuxiliaryNativeClass_unique N 0 z hz
          (fun h => hne (by rw [h, map_zero])))

/-- The torus anchor is the same corner permutation in the actual grid size. -/
theorem reflectedTorusAnchor_eq_antiDiagonalCornerState (n : ℕ) :
    reflectedTorusAnchor n = antiDiagonalCornerState (consecutiveTorusGridSize n) :=
  GridState.ext fun c => reflectedTorusAnchor_apply n c

/-- The auxiliary selection is the existing native torus anchor cycle,
without a cast of grid sizes. -/
theorem reflectedTorusAnchorCycle_eq_antiDiagonalCornerNativeCycle (n : ℕ) :
    reflectedTorusAnchorCycle n R = antiDiagonalCornerNativeCycle R (reflectedTorusGrid n)
      (by unfold consecutiveTorusGridSize; omega) (reflectedTorusGrid_O_apply n) := by
  apply (ModuleCat.mono_iff_injective
    ((laurentMaslovComplex (reflectedTorusGrid n) R).iCycles 0)).mp inferInstance
  apply (laurentMaslovChainEquiv (reflectedTorusGrid n) R 0).injective
  apply Subtype.ext
  rw [antiDiagonalCornerNativeCycle_apply]
  rw [show (laurentMaslovChainEquiv (reflectedTorusGrid n) R 0
      ((laurentMaslovComplex (reflectedTorusGrid n) R).iCycles 0
        (reflectedTorusAnchorCycle n R)) : LaurentChain R _) =
      Finsupp.single (reflectedTorusAnchor n) 1 from nativeCornerCycleOfChain_apply n R _ _ _]
  rw [reflectedTorusAnchor_eq_antiDiagonalCornerState]

/-- The existing anchor class is precisely the class selected by the auxiliary sequence. -/
theorem reflectedTorusAnchorClass_eq_antiDiagonalCornerNativeClass (n : ℕ) :
    reflectedTorusAnchorClass n R = antiDiagonalCornerNativeClass R (reflectedTorusGrid n)
      (by unfold consecutiveTorusGridSize; omega) (reflectedTorusGrid_O_apply n) := by
  rw [reflectedTorusAnchorClass, antiDiagonalCornerNativeClass,
    reflectedTorusAnchorCycle_eq_antiDiagonalCornerNativeCycle]

/-- The explicitly selected torus anchor survives in the actual full Laurent complex. -/
theorem reflectedTorusAnchorClass_ne_zero (n : ℕ) [Nontrivial R] :
    reflectedTorusAnchorClass n R ≠ 0 := by
  rw [reflectedTorusAnchorClass_eq_antiDiagonalCornerNativeClass]
  exact antiDiagonalCornerNativeClass_ne_zero R _ _ _

/-- The degree-zero polynomial homology image of the reflected grid is isomorphic to R. -/
def reflectedTorusPolynomialImageZeroEquiv (n : ℕ)
    (a : Fin (consecutiveTorusGridSize n)) :
    polynomialHomologyImage R (reflectedTorusGrid n) a 0 ≃ₗ[R] R :=
  antiDiagonalPolynomialImageZeroEquiv R (reflectedTorusGrid n)
    (by unfold consecutiveTorusGridSize; omega) (reflectedTorusGrid_O_apply n) a

/-- Over F₂ the anchor is the unique nonzero class in this polynomial image. -/
theorem reflectedTorusAnchorClass_unique (n : ℕ) (a : Fin (consecutiveTorusGridSize n))
    (ξ : (laurentMaslovComplex (reflectedTorusGrid n) (ZMod 2)).homology 0)
    (hmem : ξ ∈ polynomialHomologyImage (ZMod 2) (reflectedTorusGrid n) a 0) (hne : ξ ≠ 0) :
    ξ = reflectedTorusAnchorClass n (ZMod 2) := by
  rw [reflectedTorusAnchorClass_eq_antiDiagonalCornerNativeClass]
  exact antiDiagonalCornerNativeClass_unique _ _ _ a ξ hmem hne

/-- The first explicit torus representative also represents a nonzero homology class. -/
theorem firstTorusNativeCycle_class_ne_zero (n : ℕ) [Nontrivial R] :
    (laurentMaslovComplex (reflectedTorusGrid n) R).homologyπ 0
      (firstTorusNativeCycle n R) ≠ 0 := by
  rw [firstTorusNativeCycle_homology]
  exact reflectedTorusAnchorClass_ne_zero R n

end OnLeConjecture.KnotFloer.GridFull

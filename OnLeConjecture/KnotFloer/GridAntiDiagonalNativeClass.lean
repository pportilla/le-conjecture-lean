/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridAntiDiagonalReduction
public import OnLeConjecture.KnotFloer.GridFullReflectedCycles
public import OnLeConjecture.KnotFloer.GridPolynomialLatticeTwoByTwo
public import OnLeConjecture.KnotFloer.GridStabilizationNativeTransferred

/-!
# Native classes of the auxiliary anti-diagonal sequence

The auxiliary X generators have Maslov degree zero and are cycles for the
full Laurent differential. Their polynomial-image classes are the ones that
must be tracked in the explicit stabilization sequence. Nonvanishing will
require the remaining stabilization comparison.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

/-- The tracked generator has absolute Maslov degree zero in every size. -/
theorem maslovO_antiDiagonalAuxiliaryGrid_X (n : ℕ) :
    (antiDiagonalAuxiliaryGrid n).maslovOℤ (antiDiagonalAuxiliaryGrid n).X = 0 := by
  induction n with
  | zero =>
    have h := GridDiagram.twoByTwo.maslovO_relabelRows_finRotate GridDiagram.twoByTwo.X
    rw [GridDiagram.maslovO_eq_intCast, GridDiagram.maslovO_eq_intCast] at h
    change ((antiDiagonalAuxiliaryGrid 0).maslovOℤ (antiDiagonalAuxiliaryGrid 0).X : ℚ) =
      (GridDiagram.twoByTwo.maslovOℤ GridDiagram.twoByTwo.X : ℚ) at h
    rw [GridDiagram.twoByTwo_X, GridDiagram.maslovOℤ_twoByTwo_twoByTwoSwap,
      Int.cast_zero] at h
    exact_mod_cast h
  | succ n ih =>
    have hmem : (Finsupp.single (antiDiagonalAuxiliaryGrid (n + 1)).X 1 :
        LaurentChain (ZMod 2) (n + 3)) ∈
        laurentMaslovPiece (antiDiagonalAuxiliaryGrid (n + 1)) (ZMod 2)
          ((antiDiagonalAuxiliaryGrid (n + 1)).maslovOℤ
            (antiDiagonalAuxiliaryGrid (n + 1)).X) := by
      simpa only [laurentMaslovDegree_zero, laurentMonomialGenerator,
        LaurentPolynomial.T_zero] using
        laurentMonomialGenerator_mem_laurentMaslovPiece
          (antiDiagonalAuxiliaryGrid (n + 1)) (ZMod 2) 0 (antiDiagonalAuxiliaryGrid (n + 1)).X
    have hp := fullStabilizationTransferredRetraction_proj_mem_maslovPiece
      (antiDiagonalAuxiliaryGrid n) (Fin.last (n + 1)) (ZMod 2)
      (show (Finsupp.single (antiDiagonalAuxiliaryGrid (n + 1)).X 1 :
          LaurentChain (ZMod 2) (n + 3)) ∈ _ from hmem)
    rw [antiDiagonalAuxiliaryGrid_proj_X] at hp
    have h := hp.1 (antiDiagonalAuxiliaryGrid n).X 0 (by simp)
    simpa only [laurentMaslovDegree_zero, ih] using h.symm

/-- Reflecting the auxiliary X state produces the identity grid state. -/
theorem reflectedState_antiDiagonalAuxiliaryGrid_X (n : ℕ) :
    (reflectedState (antiDiagonalAuxiliaryGrid n).X).toPerm =
      (finRotate (n + 2)) ^ 0 := by
  apply Equiv.ext
  intro c
  change reflectedState (antiDiagonalAuxiliaryGrid n).X c = c
  rw [reflectedState_apply, antiDiagonalAuxiliaryGrid_X_apply]
  simp

/-- The tracked generator is a cycle of the actual full Laurent differential. -/
theorem laurentDifferential_antiDiagonalAuxiliaryGrid_X (n : ℕ)
    (R : Type*) [CommSemiring R] [CharP R 2] :
    laurentDifferential (antiDiagonalAuxiliaryGrid n) R
      (Finsupp.single (antiDiagonalAuxiliaryGrid n).X 1) = 0 := by
  have h := laurentDifferential_reflected_cyclic_state
    (reflectedDiagram (antiDiagonalAuxiliaryGrid n)) R
    (reflectedState_antiDiagonalAuxiliaryGrid_X n)
  simpa only [reflectedDiagram_reflectedDiagram, reflectedState_reflectedState] using h

variable (n : ℕ) (R : Type*) [CommRing R] [CharP R 2]

omit [CharP R 2] in
/-- The tracked constant generator belongs to the native degree-zero piece. -/
theorem antiDiagonalAuxiliary_X_mem_maslovZero :
    (Finsupp.single (antiDiagonalAuxiliaryGrid n).X 1 : LaurentChain R (n + 2)) ∈
      laurentMaslovPiece (antiDiagonalAuxiliaryGrid n) R 0 := by
  simpa only [laurentMaslovDegree_zero, maslovO_antiDiagonalAuxiliaryGrid_X,
    laurentMonomialGenerator, LaurentPolynomial.T_zero] using
    laurentMonomialGenerator_mem_laurentMaslovPiece (antiDiagonalAuxiliaryGrid n) R 0
      (antiDiagonalAuxiliaryGrid n).X

/-- The auxiliary constant generator as a native degree-zero chain. -/
def antiDiagonalAuxiliaryNativeChain : (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).X 0 :=
  (laurentMaslovChainEquiv (antiDiagonalAuxiliaryGrid n) R 0).symm
    ⟨Finsupp.single (antiDiagonalAuxiliaryGrid n).X 1, antiDiagonalAuxiliary_X_mem_maslovZero n R⟩

theorem antiDiagonalAuxiliaryNativeChain_apply :
    (laurentMaslovChainEquiv (antiDiagonalAuxiliaryGrid n) R 0
      (antiDiagonalAuxiliaryNativeChain n R) : LaurentChain R (n + 2)) =
        Finsupp.single (antiDiagonalAuxiliaryGrid n).X 1 := by
  simp only [antiDiagonalAuxiliaryNativeChain, LinearEquiv.apply_symm_apply]

/-- The native differential vanishes on the tracked chain. -/
theorem antiDiagonalAuxiliaryNativeChain_d_zero :
    (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).d 0 (-1)
      (antiDiagonalAuxiliaryNativeChain n R) = 0 := by
  apply (laurentMaslovChainEquiv (antiDiagonalAuxiliaryGrid n) R (-1)).injective
  apply Subtype.ext
  simp only [map_zero, ZeroMemClass.coe_zero]
  have hd := laurentMaslovChainEquiv_d (antiDiagonalAuxiliaryGrid n) R (-1)
  rw [show (-1 : ℤ) + 1 = 0 by decide] at hd
  rw [hd, antiDiagonalAuxiliaryNativeChain_apply]
  exact laurentDifferential_antiDiagonalAuxiliaryGrid_X n R

/-- The tracked generator as a native cycle. -/
def antiDiagonalAuxiliaryNativeCycle :
    (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).cycles 0 :=
  (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).cyclesMk
    (antiDiagonalAuxiliaryNativeChain n R) (-1) (by simp)
    (antiDiagonalAuxiliaryNativeChain_d_zero n R)

theorem antiDiagonalAuxiliaryNativeCycle_apply :
    (laurentMaslovChainEquiv (antiDiagonalAuxiliaryGrid n) R 0
      ((laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).iCycles 0
        (antiDiagonalAuxiliaryNativeCycle n R)) : LaurentChain R (n + 2)) =
          Finsupp.single (antiDiagonalAuxiliaryGrid n).X 1 := by
  have h := (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).i_cyclesMk
    (antiDiagonalAuxiliaryNativeChain n R) (-1) (by simp)
    (antiDiagonalAuxiliaryNativeChain_d_zero n R)
  rw [show (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).iCycles 0
      (antiDiagonalAuxiliaryNativeCycle n R) = antiDiagonalAuxiliaryNativeChain n R from h]
  exact antiDiagonalAuxiliaryNativeChain_apply n R

/-- The homology class whose nonvanishing must be transported through the sequence. -/
def antiDiagonalAuxiliaryNativeClass :
    (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).homology 0 :=
  (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).homologyπ 0
    (antiDiagonalAuxiliaryNativeCycle n R)

/-- The tracked auxiliary class has a polynomial cycle representative. -/
theorem antiDiagonalAuxiliaryNativeClass_mem_polynomialImage (a : Fin (n + 2)) :
    antiDiagonalAuxiliaryNativeClass n R ∈
      polynomialHomologyImage R (antiDiagonalAuxiliaryGrid n) a 0 := by
  apply (mem_polynomialHomologyImage_iff_exists_cycle R (antiDiagonalAuxiliaryGrid n) a 0 _).mpr
  refine ⟨antiDiagonalAuxiliaryNativeCycle n R, ?_, rfl⟩
  have hpoly : (Finsupp.single (antiDiagonalAuxiliaryGrid n).X 1 : LaurentChain R (n + 2)) ∈
      LinearMap.range (oneVariableToLaurentChain R) := by
    refine ⟨Finsupp.single (antiDiagonalAuxiliaryGrid n).X 1, ?_⟩
    ext x
    simp [oneVariableToLaurentChain_apply, Finsupp.single_apply]
  rw [antiDiagonalAuxiliaryNativeCycle_apply]
  exact (mem_range_oneVariableToLaurentChain_iff R _).mp hpoly

/-- The native projection has the exact tracked generator in its first component. -/
theorem antiDiagonalAuxiliaryNativeProjection_apply :
    stabilizationNativePair R (antiDiagonalAuxiliaryGrid n) 0
      ((stabilizationTransferredNativeProjection R (antiDiagonalAuxiliaryGrid n)
        (Fin.last (n + 1))).f 0 (antiDiagonalAuxiliaryNativeChain (n + 1) R)) =
        (Finsupp.single (antiDiagonalAuxiliaryGrid n).X 1, 0) := by
  change (fullStabilizationTransferredRetraction (antiDiagonalAuxiliaryGrid n)
      (Fin.last (n + 1)) R).proj
    (laurentMaslovChainEquiv (antiDiagonalAuxiliaryGrid (n + 1)) R 0
      (antiDiagonalAuxiliaryNativeChain (n + 1) R) : LaurentChain R (n + 3)) = _
  rw [antiDiagonalAuxiliaryNativeChain_apply]
  exact antiDiagonalAuxiliaryGrid_proj_X R n

/-- The induced cycle map retains the same explicit first-component generator.
The target is the actual transferred complex, with no old-differential identification. -/
theorem antiDiagonalAuxiliaryNativeProjection_cycle :
    stabilizationNativePair R (antiDiagonalAuxiliaryGrid n) 0
      ((stabilizationTransferredMaslovComplex R (antiDiagonalAuxiliaryGrid n)
        (Fin.last (n + 1))).iCycles 0
        (cyclesMap (stabilizationTransferredNativeProjection R (antiDiagonalAuxiliaryGrid n)
          (Fin.last (n + 1))) 0 (antiDiagonalAuxiliaryNativeCycle (n + 1) R))) =
        (Finsupp.single (antiDiagonalAuxiliaryGrid n).X 1, 0) := by
  have h := congrArg (fun f :
      (laurentMaslovComplex (antiDiagonalAuxiliaryGrid (n + 1)) R).cycles 0 ⟶
        (stabilizationTransferredMaslovComplex R (antiDiagonalAuxiliaryGrid n)
          (Fin.last (n + 1))).X 0 => f (antiDiagonalAuxiliaryNativeCycle (n + 1) R))
    (cyclesMap_i (stabilizationTransferredNativeProjection R (antiDiagonalAuxiliaryGrid n)
      (Fin.last (n + 1))) 0)
  change (stabilizationTransferredMaslovComplex R (antiDiagonalAuxiliaryGrid n)
      (Fin.last (n + 1))).iCycles 0
    (cyclesMap (stabilizationTransferredNativeProjection R (antiDiagonalAuxiliaryGrid n)
      (Fin.last (n + 1))) 0 (antiDiagonalAuxiliaryNativeCycle (n + 1) R)) =
    (stabilizationTransferredNativeProjection R (antiDiagonalAuxiliaryGrid n)
    (Fin.last (n + 1))).f 0
      ((laurentMaslovComplex (antiDiagonalAuxiliaryGrid (n + 1)) R).iCycles 0
        (antiDiagonalAuxiliaryNativeCycle (n + 1) R)) at h
  rw [h]
  have hi := (laurentMaslovComplex (antiDiagonalAuxiliaryGrid (n + 1)) R).i_cyclesMk
    (antiDiagonalAuxiliaryNativeChain (n + 1) R) (-1) (by simp)
    (antiDiagonalAuxiliaryNativeChain_d_zero (n + 1) R)
  rw [show (laurentMaslovComplex (antiDiagonalAuxiliaryGrid (n + 1)) R).iCycles 0
      (antiDiagonalAuxiliaryNativeCycle (n + 1) R) =
      antiDiagonalAuxiliaryNativeChain (n + 1) R from hi]
  exact antiDiagonalAuxiliaryNativeProjection_apply n R

/-- The tracked base cycle is precisely the cyclic row image of the computed two-by-two cycle. -/
theorem antiDiagonalAuxiliaryNativeCycle_zero_eq :
    cyclesMap (antiDiagonalAuxiliaryBaseIso R).hom 0 (twoByTwoLaurentPolynomialCycle R) =
      antiDiagonalAuxiliaryNativeCycle 0 R := by
  apply (ModuleCat.mono_iff_injective
    ((laurentMaslovComplex (antiDiagonalAuxiliaryGrid 0) R).iCycles 0)).mp inferInstance
  apply (laurentMaslovChainEquiv (antiDiagonalAuxiliaryGrid 0) R 0).injective
  apply Subtype.ext
  have h := congrArg (fun f : (laurentMaslovComplex GridDiagram.twoByTwo R).cycles 0 ⟶
      (laurentMaslovComplex (antiDiagonalAuxiliaryGrid 0) R).X 0 =>
      f (twoByTwoLaurentPolynomialCycle R))
    (cyclesMap_i (antiDiagonalAuxiliaryBaseIso R).hom 0)
  change (laurentMaslovComplex (antiDiagonalAuxiliaryGrid 0) R).iCycles 0
      (cyclesMap (antiDiagonalAuxiliaryBaseIso R).hom 0 (twoByTwoLaurentPolynomialCycle R)) =
    (antiDiagonalAuxiliaryBaseIso R).hom.f 0
      ((laurentMaslovComplex GridDiagram.twoByTwo R).iCycles 0
        (twoByTwoLaurentPolynomialCycle R)) at h
  rw [h, antiDiagonalAuxiliaryNativeCycle_apply]
  change (laurentMaslovChainEquiv (GridDiagram.twoByTwo.relabelRows (finRotate 2)) R 0
      ((laurentMaslovCyclicRowsIso GridDiagram.twoByTwo R).hom.f 0 _ ) : LaurentChain R 2) = _
  rw [laurentMaslovChainEquiv_cyclicRows, twoByTwoLaurentPolynomialCycle_apply]
  simp only [laurentCyclicRowsEquiv, GridChain.relabelRowsEquiv_single,
    antiDiagonalAuxiliaryGrid_zero, GridDiagram.relabelRows_X]

/-- The selected base homology class is the actual cyclic image of the computed nonzero class. -/
theorem antiDiagonalAuxiliaryNativeClass_zero_eq :
    homologyMap (antiDiagonalAuxiliaryBaseIso R).hom 0 (twoByTwoLaurentPolynomialClass R) =
      antiDiagonalAuxiliaryNativeClass 0 R := by
  rw [twoByTwoLaurentPolynomialClass_eq_homologyπ]
  have h := congrArg (fun f : (laurentMaslovComplex GridDiagram.twoByTwo R).cycles 0 ⟶
      (laurentMaslovComplex (antiDiagonalAuxiliaryGrid 0) R).homology 0 =>
      f (twoByTwoLaurentPolynomialCycle R))
    (homologyπ_naturality (antiDiagonalAuxiliaryBaseIso R).hom 0)
  change homologyMap (antiDiagonalAuxiliaryBaseIso R).hom 0
      ((laurentMaslovComplex GridDiagram.twoByTwo R).homologyπ 0
        (twoByTwoLaurentPolynomialCycle R)) =
    (laurentMaslovComplex (antiDiagonalAuxiliaryGrid 0) R).homologyπ 0
      (cyclesMap (antiDiagonalAuxiliaryBaseIso R).hom 0
        (twoByTwoLaurentPolynomialCycle R)) at h
  rw [h, antiDiagonalAuxiliaryNativeCycle_zero_eq]
  rfl

/-- Nonvanishing is proved at the actual initial auxiliary grid. -/
theorem antiDiagonalAuxiliaryNativeClass_zero_ne_zero [Nontrivial R] :
    antiDiagonalAuxiliaryNativeClass 0 R ≠ 0 := by
  rw [← antiDiagonalAuxiliaryNativeClass_zero_eq]
  exact (map_ne_zero_iff _
    (homologyMapIso (antiDiagonalAuxiliaryBaseIso R) 0).toLinearEquiv.injective).mpr
    (twoByTwoLaurentPolynomialClass_ne_zero R)

/-- Changing only X markings transports the tracked native cycle to any anti-diagonal O grid. -/
def antiDiagonalAuxiliaryMarkingNativeCycle (G : GridDiagram (n + 2))
    (hO : ∀ c, G.O c = c.rev) : (laurentMaslovComplex G R).cycles 0 :=
  cyclesMap (antiDiagonalAuxiliaryMarkingIso R G hO).hom 0
    (antiDiagonalAuxiliaryNativeCycle n R)

/-- The transported cycle is still exactly the constant anti-diagonal corner generator. -/
theorem antiDiagonalAuxiliaryMarkingNativeCycle_apply (G : GridDiagram (n + 2))
    (hO : ∀ c, G.O c = c.rev) :
    (laurentMaslovChainEquiv G R 0 ((laurentMaslovComplex G R).iCycles 0
      (antiDiagonalAuxiliaryMarkingNativeCycle n R G hO)) : LaurentChain R (n + 2)) =
        Finsupp.single (antiDiagonalAuxiliaryGrid n).X 1 := by
  have h := congrArg (fun f : (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).cycles 0 ⟶
      (laurentMaslovComplex G R).X 0 => f (antiDiagonalAuxiliaryNativeCycle n R))
    (cyclesMap_i (antiDiagonalAuxiliaryMarkingIso R G hO).hom 0)
  change (laurentMaslovComplex G R).iCycles 0
      (antiDiagonalAuxiliaryMarkingNativeCycle n R G hO) =
    (antiDiagonalAuxiliaryMarkingIso R G hO).hom.f 0
      ((laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).iCycles 0
        (antiDiagonalAuxiliaryNativeCycle n R)) at h
  rw [h]
  change (laurentMaslovChainEquiv G R 0 ((laurentMaslovMarkingIso R
    (antiDiagonalAuxiliaryGrid_O_eq G hO)).hom.f 0 _) : LaurentChain R (n + 2)) = _
  rw [laurentMaslovChainEquiv_markingIso, antiDiagonalAuxiliaryNativeCycle_apply]

/-- The transported corner class belongs to the actual target polynomial homology image. -/
theorem antiDiagonalAuxiliaryMarkingNativeClass_mem_polynomialImage
    (G : GridDiagram (n + 2)) (hO : ∀ c, G.O c = c.rev) (a b : Fin (n + 2)) :
    homologyMap (antiDiagonalAuxiliaryMarkingIso R G hO).hom 0
        (antiDiagonalAuxiliaryNativeClass n R) ∈ polynomialHomologyImage R G b 0 := by
  rw [← antiDiagonalAuxiliaryMarkingIso_polynomialImage R G hO a b 0]
  exact ⟨antiDiagonalAuxiliaryNativeClass n R,
    antiDiagonalAuxiliaryNativeClass_mem_polynomialImage n R a, rfl⟩

end OnLeConjecture.KnotFloer.GridFull

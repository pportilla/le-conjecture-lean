/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstSectorParity
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondSectorParity
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamMixedSectorParity
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPositivePathReduction
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamCanonical

/-!
# The seam parity identity

Every seam correction path with at least three internal transitions is absent
(`seamCorrectionPath_isEmpty_of_three_le`, record M607). The three positive-path comparisons
hold for all factor sizes (`seamPositivePathComparisons`, record M601). Consequently the
retained seam differential equals the tensor coordinate differential over `ZMod 2`, and the
binary seam comparison carries the canonical class of the seam grid to the pure tensor class
without a parity hypothesis (record M608).

The three sector theorems come from the written proofs J05, J06, and J07 in
`docs/route-n/written-proofs-J05-J06-J07-J21-J10-J15-J14.tex`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex
variable {n m : ℕ}

/-- Universal truncation at internal length two (M607): no seam correction path has three or
more internal transitions, for any factor sizes and any retained endpoints. -/
theorem seamCorrectionPath_isEmpty_of_three_le {k : ℕ} (hk : 3 ≤ k)
    (p q : SeamRetainedIndex n m) : IsEmpty (SeamCorrectionPath k p q) := by
  obtain ⟨x, z⟩ := p
  obtain ⟨y, w⟩ := q
  by_cases h₂ : z = w
  · subst h₂
    exact seamCorrectionPath_fixedSecond_isEmpty_of_three_le hk x y z
  · by_cases h₁ : x = y
    · subst h₁
      exact seamCorrectionPath_fixedFirst_isEmpty_of_three_le hk x z w
    · exact seamCorrectionPath_isEmpty_of_both_ne (x, z) (y, w) h₁ h₂

/-- The number of correction paths with at least three internal transitions is zero. -/
theorem seamLongCorrectionCount_eq_zero (p q : SeamRetainedIndex n m) :
    seamLongCorrectionCount p q = 0 := by
  unfold seamLongCorrectionCount
  apply Finset.sum_eq_zero
  intro k _
  have := seamCorrectionPath_isEmpty_of_three_le (k := k + 3) (by omega) p q
  exact Fintype.card_eq_zero

/-- The seam parity identity (M601): the three positive-path comparisons hold. -/
theorem seamPositivePathComparisons (n m : ℕ) : SeamPositivePathComparisons n m :=
  ⟨fun x y z => (seamFirstPositiveComparison_iff_long_paths x y z).mpr
      (seamFirstSector_parity n m x y z),
    fun x z w => seamSecondSector_parity n m x z w,
    fun p q h₁ h₂ => seamMixedSector_parity n m p q h₁ h₂⟩

section Comparison

variable (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
  (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)

include hO in
/-- Over `ZMod 2` the retained seam differential is the tensor coordinate differential. -/
theorem seamRetainedDifferential_eq_tensorCoordinate :
    seamRetainedDifferential G H hG hH (ZMod 2) =
      seamTensorCoordinateDifferential (K := ZMod 2) G H :=
  (seamRetainedDifferential_eq_tensorCoordinate_iff_positive_paths G H hG hH hO).mpr
    (seamPositivePathComparisons n m)

include hO in
/-- The Schur parity identity of the seam grid, entry by entry. This is the hypothesis
`hpar₂` of the binary seam comparison in `GridConnectedSumSeamCanonical`. -/
theorem seamParity (p q : SeamRetainedIndex n m) :
    laurentEvalOne (seamRetainedDifferential G H hG hH (ZMod 2) (Pi.single p 1) q) =
      (if p.2 = q.2 then ((GridRectangleBetween.emptyRectangles p.1 q.1).card : ZMod 2) else 0) +
        if p.1 = q.1 then ((GridRectangleBetween.emptyRectangles p.2 q.2).card : ZMod 2) else 0 :=
  (seamRetainedDifferential_eq_tensorCoordinate_iff_evalOne G H hG hH hO).mp
    (seamRetainedDifferential_eq_tensorCoordinate G H hG hH hO) p q

/-- The binary seam comparison sends the canonical class of the seam grid to the pure tensor
class of the two factor canonical classes (M608, now unconditional). -/
theorem seamNativeTensor_hom_canonicalClass_unconditional (hn : 2 ≤ n + 1) (hm : 2 ≤ m + 1) :
    homologyMap (seamNativeTensorHomotopyEquiv G H hG hH hO (seamParity G H hG hH hO)).hom 0
      (gridCanonicalClass (connectedSumSeamGrid G H hG hH) (by omega)) =
        gridCanonicalBinaryTensorClass G H hn hm :=
  seamNativeTensor_hom_canonicalClass G H hG hH hO (seamParity G H hG hH hO) hn hm

include hO in
/-- The weighted spectral thresholds of the seam canonical class and of the pure tensor class
agree, for every weight `t`. -/
theorem seamNativeTensor_canonical_spectralThreshold_unconditional
    (hn : 2 ≤ n + 1) (hm : 2 ≤ m + 1) (t : ℝ) :
    ((laurentTensorMaslovBifiltration (K := ZMod 2) G H).weighted t).spectralThreshold 0
      (gridCanonicalBinaryTensorClass G H hn hm) =
        RealFiltration.spectralThreshold
          ((laurentMaslovBifiltration (connectedSumSeamGrid G H hG hH) (ZMod 2)).weighted t)
          0 (gridCanonicalClass (connectedSumSeamGrid G H hG hH) (by omega)) :=
  seamNativeTensor_canonical_spectralThreshold G H hG hH hO (seamParity G H hG hH hO) hn hm t

end Comparison

end OnLeConjecture.KnotFloer.GridFull

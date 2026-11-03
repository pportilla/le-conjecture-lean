/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamCanonical
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamParity

/-!
# The binary seam comparison without a parity hypothesis

The positive-path comparisons `SeamPositivePathComparisons n m` imply the explicit
parity identity used as the hypothesis `hpar₂` of `seamNativeTensorHomotopyEquiv`. The
deduction composes the two proved equivalences
`seamRetainedDifferential_eq_tensorCoordinate_iff_positive_paths` and
`seamRetainedDifferential_eq_tensorCoordinate_iff_evalOne` (M608). Since the
comparisons are proved for all factor sizes (`seamPositivePathComparisons`, M601), the
binary native homotopy equivalence holds for every prepared pair of grids. Its
unconditional canonical class transport is
`seamNativeTensor_hom_canonicalClass_unconditional` in `GridConnectedSumSeamParity`.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n m : ℕ}

/-- The positive-path comparisons give the parity identity for every prepared pair (M608). -/
theorem seamParity_of_positivePaths (h : SeamPositivePathComparisons n m)
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1)) (hG : G.X (Fin.last n) = Fin.last n)
    (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0) (p q : SeamRetainedIndex n m) :
    laurentEvalOne (seamRetainedDifferential G H hG hH (ZMod 2) (Pi.single p 1) q) =
      (if p.2 = q.2 then ((GridRectangleBetween.emptyRectangles p.1 q.1).card : ZMod 2) else 0) +
        if p.1 = q.1 then ((GridRectangleBetween.emptyRectangles p.2 q.2).card : ZMod 2) else 0 :=
  (seamRetainedDifferential_eq_tensorCoordinate_iff_evalOne G H hG hH hO).mp
    ((seamRetainedDifferential_eq_tensorCoordinate_iff_positive_paths G H hG hH hO).mpr h) p q

variable (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
  (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)

/-- The binary native seam equivalence over `ZMod 2`, without a parity hypothesis. -/
def seamNativeTensorHomotopyEquivZModTwo :
    HomotopyEquiv (laurentMaslovComplex (connectedSumSeamGrid G H hG hH) (ZMod 2))
      (laurentTensorMaslovComplex (K := ZMod 2) G H) :=
  seamNativeTensorHomotopyEquiv G H hG hH hO (seamParity G H hG hH hO)

/-- The projection to the binary tensor has shifts `(0,0)`. -/
theorem seamNativeTensorHomotopyEquivZModTwo_hom_shifts :
    (laurentMaslovBifiltration (connectedSumSeamGrid G H hG hH) (ZMod 2)).Shifts
      (laurentTensorMaslovBifiltration (K := ZMod 2) G H)
      (seamNativeTensorHomotopyEquivZModTwo G H hG hH hO).hom 0 0 :=
  seamNativeTensorHomotopyEquiv_hom_shifts G H hG hH hO _

/-- The inclusion of the binary tensor has shifts `(0,0)`. -/
theorem seamNativeTensorHomotopyEquivZModTwo_inv_shifts :
    (laurentTensorMaslovBifiltration (K := ZMod 2) G H).Shifts
      (laurentMaslovBifiltration (connectedSumSeamGrid G H hG hH) (ZMod 2))
      (seamNativeTensorHomotopyEquivZModTwo G H hG hH hO).inv 0 0 :=
  seamNativeTensorHomotopyEquiv_inv_shifts G H hG hH hO _

end OnLeConjecture.KnotFloer.GridFull

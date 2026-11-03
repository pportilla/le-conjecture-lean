/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingIdentification
public import OnLeConjecture.KnotFloer.GridStabilizationNativeTransferred

/-!
# Native stabilization equivalence with the old doubled complex

The proved coefficient identity identifies the constructed transferred differential
with the old differential on both summands. The resulting isomorphism is the
identity on homogeneous pairs, so the native comparison retains the constructed
full projection and inclusion.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]
variable (G : GridDiagram n) (s : Fin n)

/-- The homogeneous transferred differential is the product of the old homogeneous maps. -/
theorem stabilizationTransferredGradedDifferential_eq_old_double (m : ℤ) :
    stabilizationTransferredGradedDifferential R G s m =
      (laurentGradedDifferential G R m).prodMap
        (laurentGradedDifferential G R (m + 1)) := by
  apply LinearMap.ext
  intro x
  apply stabilizationNativePair_injective R G m
  exact stabilizationTransferredDifferential_apply_eq_old_double G s R
    (stabilizationNativePair R G (m + 1) x)

/-- Identity on the two homogeneous summands identifies the native transferred and old complexes. -/
def stabilizationTransferredNativeOldIso :
    stabilizationTransferredMaslovComplex R G s ≅ shiftedDouble (laurentMaslovComplex G R) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    rw [ComplexShape.down_Rel] at hij
    subst i
    simp only [Iso.refl_hom]
    rw [shiftedDouble_d, laurentMaslovComplex_d, laurentMaslovComplex_d,
      stabilizationTransferredMaslovComplex_d,
      stabilizationTransferredGradedDifferential_eq_old_double]
    rfl)

/-- The identification leaves the underlying homogeneous pair unchanged. -/
theorem stabilizationTransferredNativeOldIso_hom_apply (m : ℤ)
    (x : stabilizationLaurentPairPiece R G m) :
    (stabilizationTransferredNativeOldIso R G s).hom.f m x = x := rfl

/-- The inverse identification also leaves the homogeneous pair unchanged. -/
theorem stabilizationTransferredNativeOldIso_inv_apply (m : ℤ)
    (x : (shiftedDouble (laurentMaslovComplex G R)).X m) :
    (stabilizationTransferredNativeOldIso R G s).inv.f m x = x := rfl

/-- The full stabilized native complex is homotopy equivalent to the shifted old double. -/
def stabilizationNativeOldHomotopyEquiv :
    HomotopyEquiv (laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R)
      (shiftedDouble (laurentMaslovComplex G R)) :=
  (stabilizationTransferredNativeHomotopyEquiv R G s).trans
    (HomotopyEquiv.ofIso (stabilizationTransferredNativeOldIso R G s))

/-- The comparison to the old double has exactly the constructed projection coefficients. -/
theorem stabilizationNativeOldHomotopyEquiv_hom_apply (m : ℤ)
    (x : laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m) :
    stabilizationNativePair R G m ((stabilizationNativeOldHomotopyEquiv R G s).hom.f m x) =
      (fullStabilizationTransferredRetraction G s R).proj x.val := rfl

/-- The inverse comparison has exactly the constructed inclusion coefficients. -/
theorem stabilizationNativeOldHomotopyEquiv_inv_apply (m : ℤ)
    (x : (shiftedDouble (laurentMaslovComplex G R)).X m) :
    ((stabilizationNativeOldHomotopyEquiv R G s).inv.f m x :
      laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m).val =
      (fullStabilizationTransferredRetraction G s R).incl (stabilizationNativePair R G m x) := rfl

/-- Native stabilized homology splits into the old degrees m and m+1. -/
def stabilizationNativeOldHomologyEquiv (m : ℤ) :
    (laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R).homology m ≃ₗ[R]
      (laurentMaslovComplex G R).homology m × (laurentMaslovComplex G R).homology (m + 1) :=
  ((stabilizationNativeOldHomotopyEquiv R G s).toHomologyIso m).toLinearEquiv.trans
    (polynomialDoubleHomologyEquiv R G m)

/-- The homology splitting is the actual projection followed by the two-degree decomposition. -/
theorem stabilizationNativeOldHomologyEquiv_apply (m : ℤ)
    (ξ : (laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R).homology m) :
    stabilizationNativeOldHomologyEquiv R G s m ξ =
      polynomialDoubleHomologyEquiv R G m
        (homologyMap (stabilizationNativeOldHomotopyEquiv R G s).hom m ξ) := rfl

end OnLeConjecture.KnotFloer.GridFull

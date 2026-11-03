/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationNativeOld
public import OnLeConjecture.KnotFloer.BifilteredShift

/-!
# The first stabilization summand as a filtered retract

The constructed full stabilization inclusion, restricted to the first old
summand, and the first component of its projection preserve both filtration
coordinates. Their composite on the old complex is the identity. In particular,
including a homology class preserves its spectral thresholds exactly. This is
a statement about the specified summand, not an equivalence with the full
stabilized complex.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]
variable (G : GridDiagram n) (s : Fin n)

/-- Include the first old summand through the constructed full stabilization map. -/
def stabilizationCanonicalInclusion :
    laurentMaslovComplex G R ⟶
      laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R :=
  shiftedDoubleInl (laurentMaslovComplex G R) ≫
    (stabilizationNativeOldHomotopyEquiv R G s).inv

/-- Take the first component of the constructed full stabilization projection. -/
def stabilizationCanonicalProjection :
    laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R ⟶
      laurentMaslovComplex G R :=
  (stabilizationNativeOldHomotopyEquiv R G s).hom ≫
    shiftedDoubleFst (laurentMaslovComplex G R)

/-- The inclusion has the full HPL coefficients on the pair `(x,0)`. -/
theorem stabilizationCanonicalInclusion_apply (m : ℤ)
    (x : (laurentMaslovComplex G R).X m) :
    (laurentMaslovChainEquiv (G.stabilizeX s.castSucc (G.X s).castSucc s) R m
      ((stabilizationCanonicalInclusion R G s).f m x) : LaurentChain R (n + 1)) =
      (fullStabilizationTransferredRetraction G s R).incl
        ((laurentMaslovChainEquiv G R m x : LaurentChain R n), 0) := rfl

/-- The projection is the first component of the full HPL projection. -/
theorem stabilizationCanonicalProjection_apply (m : ℤ)
    (x : (laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R).X m) :
    (laurentMaslovChainEquiv G R m
      ((stabilizationCanonicalProjection R G s).f m x) : LaurentChain R n) =
      ((fullStabilizationTransferredRetraction G s R).proj
        (laurentMaslovChainEquiv (G.stabilizeX s.castSucc (G.X s).castSucc s) R m x)).1 := rfl

/-- The first-summand inclusion has zero shift in both coordinates. -/
theorem stabilizationCanonicalInclusion_shifts :
    (laurentMaslovBifiltration G R).Shifts
      (laurentMaslovBifiltration (G.stabilizeX s.castSucc (G.X s).castSucc s) R)
      (stabilizationCanonicalInclusion R G s) 0 0 := by
  intro u v m x hx
  change (laurentMaslovChainEquiv _ R m
    ((stabilizationCanonicalInclusion R G s).f m x) : LaurentChain R (n + 1)) ∈
      laurentBifiltrationLevel _ R (u + 0) (v + 0)
  rw [stabilizationCanonicalInclusion_apply, add_zero, add_zero]
  exact fullStabilizationTransferredRetraction_incl_mem_bifiltrationLevel G s R
    ⟨hx, Submodule.zero_mem _⟩

/-- The first component of the projection has zero shift in both coordinates. -/
theorem stabilizationCanonicalProjection_shifts :
    (laurentMaslovBifiltration (G.stabilizeX s.castSucc (G.X s).castSucc s) R).Shifts
      (laurentMaslovBifiltration G R) (stabilizationCanonicalProjection R G s) 0 0 := by
  intro u v m x hx
  change (laurentMaslovChainEquiv G R m
    ((stabilizationCanonicalProjection R G s).f m x) : LaurentChain R n) ∈
      laurentBifiltrationLevel G R (u + 0) (v + 0)
  rw [stabilizationCanonicalProjection_apply, add_zero, add_zero]
  exact (fullStabilizationTransferredRetraction_proj_mem_bifiltrationLevel G s R hx).1

/-- Projection after inclusion is exactly the identity on the old complex. -/
theorem stabilizationCanonicalInclusion_projection :
    stabilizationCanonicalInclusion R G s ≫ stabilizationCanonicalProjection R G s =
      𝟙 (laurentMaslovComplex G R) := by
  ext m x
  apply (laurentMaslovChainEquiv G R m).injective
  apply Subtype.ext
  change (laurentMaslovChainEquiv G R m
    ((stabilizationCanonicalProjection R G s).f m
      ((stabilizationCanonicalInclusion R G s).f m x)) : LaurentChain R n) = _
  rw [stabilizationCanonicalProjection_apply, stabilizationCanonicalInclusion_apply,
    LinearSpecialContraction.proj_incl_apply]
  rfl

/-- Under the full comparison the included class lies in exactly the first summand. -/
theorem stabilizationCanonicalInclusion_old_projection :
    stabilizationCanonicalInclusion R G s ≫ (stabilizationNativeOldHomotopyEquiv R G s).hom =
      shiftedDoubleInl (laurentMaslovComplex G R) := by
  ext m x
  apply stabilizationNativePair_injective R G m
  change (fullStabilizationTransferredRetraction G s R).proj
    ((fullStabilizationTransferredRetraction G s R).incl
      ((laurentMaslovChainEquiv G R m x : LaurentChain R n), 0)) = _
  rw [LinearSpecialContraction.proj_incl_apply]
  rfl

/-- Exact class transport into the first summand of the full native comparison. -/
theorem stabilizationCanonical_homology_first_summand (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) :
    homologyMap (stabilizationNativeOldHomotopyEquiv R G s).hom m
      (homologyMap (stabilizationCanonicalInclusion R G s) m ξ) =
        homologyMap (shiftedDoubleInl (laurentMaslovComplex G R)) m ξ := by
  have h : homologyMap (stabilizationCanonicalInclusion R G s) m ≫
      homologyMap (stabilizationNativeOldHomotopyEquiv R G s).hom m =
        homologyMap (shiftedDoubleInl (laurentMaslovComplex G R)) m := by
    rw [← homologyMap_comp, stabilizationCanonicalInclusion_old_projection]
  exact congrArg (fun f : (laurentMaslovComplex G R).homology m ⟶
    (shiftedDouble (laurentMaslovComplex G R)).homology m => f ξ) h

/-- The selected included class projects to the original class in every degree. -/
theorem stabilizationCanonical_homology_retraction (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) :
    homologyMap (stabilizationCanonicalProjection R G s) m
      (homologyMap (stabilizationCanonicalInclusion R G s) m ξ) = ξ := by
  have h : homologyMap (stabilizationCanonicalInclusion R G s) m ≫
      homologyMap (stabilizationCanonicalProjection R G s) m = 𝟙 _ := by
    rw [← homologyMap_comp, stabilizationCanonicalInclusion_projection, homologyMap_id]
  exact congrArg (fun f : (laurentMaslovComplex G R).homology m ⟶
    (laurentMaslovComplex G R).homology m => f ξ) h

/-- Inclusion cannot kill a nonzero homology class. -/
theorem stabilizationCanonical_homology_injective (m : ℤ) :
    Function.Injective (homologyMap (stabilizationCanonicalInclusion R G s) m) :=
  Function.LeftInverse.injective (stabilizationCanonical_homology_retraction R G s m)

/-- The included class is nonzero exactly when the old class is nonzero. -/
theorem stabilizationCanonical_homology_ne_zero_iff (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) :
    homologyMap (stabilizationCanonicalInclusion R G s) m ξ ≠ 0 ↔ ξ ≠ 0 :=
  map_ne_zero_iff _ (stabilizationCanonical_homology_injective R G s m)

/-- The weighted spectral threshold is unchanged for the included class.
The statement includes infinite thresholds and does not require attainment. -/
theorem stabilizationCanonical_spectralThreshold (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) (t : ℝ) :
    RealFiltration.spectralThreshold
      ((laurentMaslovBifiltration (G.stabilizeX s.castSucc (G.X s).castSucc s) R).weighted t)
        m (homologyMap (stabilizationCanonicalInclusion R G s) m ξ) =
      ((laurentMaslovBifiltration G R).weighted t).spectralThreshold m ξ := by
  have hI := (stabilizationCanonicalInclusion_shifts R G s).weighted t
  have hP := (stabilizationCanonicalProjection_shifts R G s).weighted t
  simp only [mul_zero, add_zero] at hI hP
  obtain ⟨hle, hge⟩ := RealFiltration.spectralThreshold_comparison_of_maps hI hP m ξ
    (stabilizationCanonical_homology_retraction R G s m ξ)
  simp only [EReal.coe_zero, add_zero] at hle hge
  exact le_antisymm hle hge

end OnLeConjecture.KnotFloer.GridFull

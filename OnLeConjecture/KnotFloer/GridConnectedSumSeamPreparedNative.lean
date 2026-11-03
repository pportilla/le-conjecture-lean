/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPreparedMaslov
public import OnLeConjecture.KnotFloer.BifilteredShift
public import OnLeConjecture.KnotFloer.GridFullLaurentSpectral

/-!
# Native filtered contraction for a prepared connected-sum seam

The target uses the proved Schur differential. All maps come from the
full rectangle differential and its constructed matching inverse.
Identification of the target with the factor tensor complex is separate.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex
variable {n m : ℕ} (R : Type*) [CommRing R] [CharP R 2]
variable (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
  (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)

/-- The actual Schur differential restricted to consecutive homogeneous submodules. -/
def seamRetainedGradedDifferential (d : ℤ) :
    seamRetainedMaslovPiece G H hG hH R (d + 1) →ₗ[R]
      seamRetainedMaslovPiece G H hG hH R d :=
  ((seamRetainedDifferential G H hG hH R).restrictScalars R).restrict
    (fun _ hc => by simpa only [add_sub_cancel_right, LinearMap.restrictScalars_apply] using
      seamRetainedDifferential_mem_maslov_of_last_O G H hG hH hO R hc)

/-- The native complex of the retained state coefficients and their actual Schur differential. -/
def seamRetainedMaslovComplex : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun d => ModuleCat.of R (seamRetainedMaslovPiece G H hG hH R d))
    (fun d => ModuleCat.ofHom (seamRetainedGradedDifferential R G H hG hH hO d))
    (fun d => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (seamRetainedDifferential_comp_self G H hG hH R) x.val)

/-- The native differential is the constructed Schur differential on underlying coefficients. -/
theorem seamRetainedMaslovComplex_d (d : ℤ) :
    (seamRetainedMaslovComplex R G H hG hH hO).d (d + 1) d =
      ModuleCat.ofHom (seamRetainedGradedDifferential R G H hG hH hO d) := by
  simp only [seamRetainedMaslovComplex, ChainComplex.of_d]

/-- The actual inclusion restricted to each degree. -/
def seamNativeInclusionPiece (d : ℤ) :
    seamRetainedMaslovPiece G H hG hH R d →ₗ[R]
      laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R d :=
  ((seamFullContraction G H hG hH R).incl.restrictScalars R).restrict
    (fun _ hc => seamFullContraction_incl_mem_maslov_of_last_O G H hG hH hO R hc)

/-- The actual projection restricted to each degree. -/
def seamNativeProjectionPiece (d : ℤ) :
    laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R d →ₗ[R]
      seamRetainedMaslovPiece G H hG hH R d :=
  ((seamFullContraction G H hG hH R).proj.restrictScalars R).restrict
    (fun _ hc => seamFullContraction_proj_mem_maslov_of_last_O G H hG hH hO R hc)

/-- The corrected inclusion is a native chain map. -/
def seamNativeInclusion :
    seamRetainedMaslovComplex R G H hG hH hO ⟶
      laurentMaslovComplex (connectedSumSeamGrid G H hG hH) R where
  f d := ModuleCat.ofHom (seamNativeInclusionPiece R G H hG hH hO d)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    rw [seamRetainedMaslovComplex_d, laurentMaslovComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (seamFullContraction G H hG hH R).dM_incl_apply x.val

/-- The corrected projection is a native chain map. -/
def seamNativeProjection :
    laurentMaslovComplex (connectedSumSeamGrid G H hG hH) R ⟶
      seamRetainedMaslovComplex R G H hG hH hO where
  f d := ModuleCat.ofHom (seamNativeProjectionPiece R G H hG hH hO d)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    rw [seamRetainedMaslovComplex_d, laurentMaslovComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact ((seamFullContraction G H hG hH R).proj_dM_apply x.val).symm

/-- Projection after inclusion is the identity in the native graded category. -/
theorem seamNative_inclusion_projection :
    seamNativeInclusion R G H hG hH hO ≫ seamNativeProjection R G H hG hH hO =
      𝟙 (seamRetainedMaslovComplex R G H hG hH hO) := by
  ext d x
  apply Subtype.ext
  exact (seamFullContraction G H hG hH R).proj_incl_apply x.val

/-- The negative degree-one contraction homotopy uses the native sign convention. -/
def seamNativeHomotopyPiece (d : ℤ) :
    laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R d →ₗ[R]
      laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R (d + 1) :=
  (-((seamFullContraction G H hG hH R).homotopy.restrictScalars R)).restrict
    (fun _ hx => Submodule.neg_mem _
      (seamFullContraction_homotopy_mem_maslov_of_last_O G H hG hH hO R hx))

/-- Extend the homotopy by zero away from degree one. -/
def seamNativeHomotopyComponent (i j : ℤ) :
    (laurentMaslovComplex (connectedSumSeamGrid G H hG hH) R).X i ⟶
      (laurentMaslovComplex (connectedSumSeamGrid G H hG hH) R).X j :=
  if h : j = i + 1 then by
    subst j
    exact ModuleCat.ofHom (seamNativeHomotopyPiece R G H hG hH hO i)
  else 0

theorem seamNativeHomotopyComponent_succ (i : ℤ) :
    seamNativeHomotopyComponent R G H hG hH hO i (i + 1) =
      ModuleCat.ofHom (seamNativeHomotopyPiece R G H hG hH hO i) := by
  simp [seamNativeHomotopyComponent]

theorem seamNativeHomotopyComponent_zero (i j : ℤ)
    (h : ¬ (ComplexShape.down ℤ).Rel j i) :
    seamNativeHomotopyComponent R G H hG hH hO i j = 0 := by
  rw [seamNativeHomotopyComponent, dif_neg]
  simpa only [ComplexShape.down_Rel, eq_comm] using h

/-- The concrete contraction equation in every native homogeneous component. -/
theorem seamNative_homotopy_component (d : ℤ) :
    (seamNativeProjection R G H hG hH hO ≫ seamNativeInclusion R G H hG hH hO).f (d + 1) =
      (laurentMaslovComplex (connectedSumSeamGrid G H hG hH) R).d (d + 1) d ≫
          seamNativeHomotopyComponent R G H hG hH hO d (d + 1) +
        seamNativeHomotopyComponent R G H hG hH hO (d + 1) (d + 1 + 1) ≫
          (laurentMaslovComplex (connectedSumSeamGrid G H hG hH) R).d (d + 1 + 1) (d + 1) +
        𝟙 ((laurentMaslovComplex (connectedSumSeamGrid G H hG hH) R).X (d + 1)) := by
  rw [seamNativeHomotopyComponent_succ, seamNativeHomotopyComponent_succ,
    laurentMaslovComplex_d, laurentMaslovComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (seamFullContraction G H hG hH R).incl ((seamFullContraction G H hG hH R).proj x.val) =
    -(seamFullContraction G H hG hH R).homotopy
      (laurentDifferential (connectedSumSeamGrid G H hG hH) R x.val) +
    laurentDifferential (connectedSumSeamGrid G H hG hH) R
      (-(seamFullContraction G H hG hH R).homotopy x.val) + x.val
  rw [map_neg, LinearSpecialContraction.incl_proj_apply]
  abel

/-- The corrected projection and inclusion compose to the identity up to the proved homotopy. -/
def seamNativeHomotopy :
    Homotopy (seamNativeProjection R G H hG hH hO ≫ seamNativeInclusion R G H hG hH hO)
      (𝟙 (laurentMaslovComplex (connectedSumSeamGrid G H hG hH) R)) where
  hom := seamNativeHomotopyComponent R G H hG hH hO
  zero := seamNativeHomotopyComponent_zero R G H hG hH hO
  comm i := by
    obtain ⟨d, rfl⟩ : ∃ d : ℤ, d + 1 = i := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (d + 1) d from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (d + 1 + 1) (d + 1) from rfl)]
    exact seamNative_homotopy_component R G H hG hH hO d

/-- The full seam complex is homotopy equivalent to its actual retained complex. -/
def seamNativeHomotopyEquiv :
    HomotopyEquiv (laurentMaslovComplex (connectedSumSeamGrid G H hG hH) R)
      (seamRetainedMaslovComplex R G H hG hH hO) where
  hom := seamNativeProjection R G H hG hH hO
  inv := seamNativeInclusion R G H hG hH hO
  homotopyHomInvId := seamNativeHomotopy R G H hG hH hO
  homotopyInvHomId := Homotopy.ofEq (seamNative_inclusion_projection R G H hG hH hO)

/-- The two filtrations restricted to the native retained complex. -/
def seamRetainedMaslovBifiltration : Bifiltration (seamRetainedMaslovComplex R G H hG hH hO) where
  level u v d := (seamRetainedBifiltrationLevel G H hG hH R u v).comap
    (seamRetainedMaslovPiece G H hG hH R d).subtype
  mono d _ _ _ _ hu hv := Submodule.comap_mono (Submodule.comap_mono
    (laurentBifiltrationLevel_mono _ R hu hv))
  differential_mem u v i j c hc := by
    by_cases h : j + 1 = i
    · subst i
      rw [seamRetainedMaslovComplex_d]
      exact seamRetainedDifferential_mem_bifiltration_of_last_O G H hG hH hO R hc
    · have hrel : ¬ (ComplexShape.down ℤ).Rel i j := by
        simpa only [ComplexShape.down_Rel] using h
      rw [(seamRetainedMaslovComplex R G H hG hH hO).shape i j hrel]
      exact Submodule.zero_mem _

/-- The native inclusion has zero shift in both filtration coordinates. -/
theorem seamNativeInclusion_shifts :
    (seamRetainedMaslovBifiltration R G H hG hH hO).Shifts
      (laurentMaslovBifiltration (connectedSumSeamGrid G H hG hH) R)
      (seamNativeInclusion R G H hG hH hO) 0 0 := by
  intro u v d x hx
  change (seamFullContraction G H hG hH R).incl x.val ∈
    laurentBifiltrationLevel _ R (u + 0) (v + 0)
  rw [add_zero, add_zero]
  exact seamFullContraction_incl_mem_bifiltration_of_last_O G H hG hH hO R hx

/-- The native projection has zero shift in both filtration coordinates. -/
theorem seamNativeProjection_shifts :
    (laurentMaslovBifiltration (connectedSumSeamGrid G H hG hH) R).Shifts
      (seamRetainedMaslovBifiltration R G H hG hH hO)
      (seamNativeProjection R G H hG hH hO) 0 0 := by
  intro u v d x hx
  change (seamFullContraction G H hG hH R).proj x.val ∈
    seamRetainedBifiltrationLevel G H hG hH R (u + 0) (v + 0)
  rw [add_zero, add_zero]
  exact seamFullContraction_proj_mem_bifiltration_of_last_O G H hG hH hO R hx

end OnLeConjecture.KnotFloer.GridFull

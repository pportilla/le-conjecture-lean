/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPolynomialLatticeTransferred
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Native graded equivalence with the transferred stabilization complex

The constructed full inclusion, projection and homotopy restrict to Maslov
degrees and give a native chain homotopy equivalence. The target retains its
actual transferred differential throughout.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]
variable (G : GridDiagram n) (s : Fin n)

/-- The constructed inclusion restricted to a homogeneous pair. -/
def stabilizationTransferredInclusionPiece (m : ℤ) :
    stabilizationLaurentPairPiece R G m →ₗ[R]
      laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m :=
  (((fullStabilizationTransferredRetraction G s R).incl.restrictScalars R).comp
    (stabilizationNativePair R G m)).codRestrict _ (fun x =>
      fullStabilizationTransferredRetraction_incl_mem_maslovPiece G s R
        (show stabilizationNativePair R G m x ∈ stabilizationTargetMaslovPiece G R m from
          ⟨x.1.property, x.2.property⟩))

/-- The constructed projection restricted to a homogeneous source chain. -/
def stabilizationTransferredProjectionPiece (m : ℤ) :
    laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m →ₗ[R]
      stabilizationLaurentPairPiece R G m where
  toFun x :=
    let h := fullStabilizationTransferredRetraction_proj_mem_maslovPiece G s R x.property
    (⟨((fullStabilizationTransferredRetraction G s R).proj x.val).1, h.1⟩,
      ⟨((fullStabilizationTransferredRetraction G s R).proj x.val).2, h.2⟩)
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst
        ((fullStabilizationTransferredRetraction G s R).proj.map_add x.val y.val)
    · exact congrArg Prod.snd
        ((fullStabilizationTransferredRetraction G s R).proj.map_add x.val y.val)
  map_smul' r x := by
    have h :=
      ((fullStabilizationTransferredRetraction G s R).proj.restrictScalars R).map_smul r x.val
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

/-- The native inclusion is the original Laurent inclusion on underlying coefficients. -/
theorem stabilizationTransferredInclusionPiece_apply (m : ℤ)
    (x : stabilizationLaurentPairPiece R G m) :
    (stabilizationTransferredInclusionPiece R G s m x : LaurentChain R (n + 1)) =
      (fullStabilizationTransferredRetraction G s R).incl (stabilizationNativePair R G m x) := rfl

/-- The native projection is the original Laurent projection on underlying coefficients. -/
theorem stabilizationTransferredProjectionPiece_apply (m : ℤ)
    (x : laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m) :
    stabilizationNativePair R G m (stabilizationTransferredProjectionPiece R G s m x) =
      (fullStabilizationTransferredRetraction G s R).proj x.val := rfl

/-- The full inclusion as a native Maslov-graded chain map. -/
def stabilizationTransferredNativeInclusion :
    stabilizationTransferredMaslovComplex R G s ⟶
      laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R where
  f m := ModuleCat.ofHom (stabilizationTransferredInclusionPiece R G s m)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    rw [stabilizationTransferredMaslovComplex_d, laurentMaslovComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (fullStabilizationTransferredRetraction G s R).dM_incl_apply
      (stabilizationNativePair R G (j + 1) x)

/-- The full projection as a native Maslov-graded chain map. -/
def stabilizationTransferredNativeProjection :
    laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R ⟶
      stabilizationTransferredMaslovComplex R G s where
  f m := ModuleCat.ofHom (stabilizationTransferredProjectionPiece R G s m)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    rw [stabilizationTransferredMaslovComplex_d, laurentMaslovComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply stabilizationNativePair_injective R G j
    exact ((fullStabilizationTransferredRetraction G s R).proj_dM_apply x.val).symm

/-- The projection retracts the inclusion in the native graded category. -/
theorem stabilizationTransferredNative_inclusion_projection :
    stabilizationTransferredNativeInclusion R G s ≫ stabilizationTransferredNativeProjection R G s =
      𝟙 (stabilizationTransferredMaslovComplex R G s) := by
  ext m x
  apply stabilizationNativePair_injective R G m
  exact (fullStabilizationTransferredRetraction G s R).proj_incl_apply
    (stabilizationNativePair R G m x)

/-- The negative contraction homotopy gives the native convention f=dH+Hd+g. -/
def stabilizationTransferredHomotopyPiece (m : ℤ) :
    laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m →ₗ[R]
      laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R (m + 1) :=
  (-((fullStabilizationTransferredRetraction G s R).homotopy.restrictScalars R)).restrict
    (fun _x hx => Submodule.neg_mem _
      (fullStabilizationTransferredRetraction_homotopy_mem_maslovPiece G s R hx))

/-- Extend the degree-one homotopy by zero outside adjacent degrees. -/
def stabilizationTransferredNativeHomotopyComponent (i j : ℤ) :
    (laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R).X i ⟶
      (laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R).X j :=
  if h : j = i + 1 then by
    subst j
    exact ModuleCat.ofHom (stabilizationTransferredHomotopyPiece R G s i)
  else 0

/-- On adjacent degrees this is the constructed negative homotopy. -/
theorem stabilizationTransferredNativeHomotopyComponent_succ (i : ℤ) :
    stabilizationTransferredNativeHomotopyComponent R G s i (i + 1) =
      ModuleCat.ofHom (stabilizationTransferredHomotopyPiece R G s i) := by
  simp [stabilizationTransferredNativeHomotopyComponent]

/-- Off the homotopy shape the component is zero. -/
theorem stabilizationTransferredNativeHomotopyComponent_zero (i j : ℤ)
    (h : ¬ (ComplexShape.down ℤ).Rel j i) :
    stabilizationTransferredNativeHomotopyComponent R G s i j = 0 := by
  rw [stabilizationTransferredNativeHomotopyComponent, dif_neg]
  simpa only [ComplexShape.down_Rel, eq_comm] using h

/-- The contraction identity holds in each native homogeneous component. -/
theorem stabilizationTransferredNative_homotopy_component (m : ℤ) :
    (stabilizationTransferredNativeProjection R G s ≫
      stabilizationTransferredNativeInclusion R G s).f (m + 1) =
      (laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R).d (m + 1) m ≫
          stabilizationTransferredNativeHomotopyComponent R G s m (m + 1) +
        stabilizationTransferredNativeHomotopyComponent R G s (m + 1) (m + 1 + 1) ≫
          (laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R).d
            (m + 1 + 1) (m + 1) +
        𝟙 ((laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R).X (m + 1)) := by
  rw [stabilizationTransferredNativeHomotopyComponent_succ,
    stabilizationTransferredNativeHomotopyComponent_succ, laurentMaslovComplex_d,
    laurentMaslovComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (fullStabilizationTransferredRetraction G s R).incl
    ((fullStabilizationTransferredRetraction G s R).proj x.val) =
      -(fullStabilizationTransferredRetraction G s R).homotopy
        (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R x.val) +
      laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
        (-(fullStabilizationTransferredRetraction G s R).homotopy x.val) + x.val
  rw [map_neg, LinearSpecialContraction.incl_proj_apply]
  abel

/-- The actual native projection followed by inclusion is homotopic to the identity. -/
def stabilizationTransferredNativeHomotopy :
    Homotopy (stabilizationTransferredNativeProjection R G s ≫
      stabilizationTransferredNativeInclusion R G s)
      (𝟙 (laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R)) where
  hom := stabilizationTransferredNativeHomotopyComponent R G s
  zero := stabilizationTransferredNativeHomotopyComponent_zero R G s
  comm i := by
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, m + 1 = i := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (m + 1 + 1) (m + 1) from rfl)]
    exact stabilizationTransferredNative_homotopy_component R G s m

/-- The full stabilized complex is homotopy equivalent to its actual transferred complex. -/
def stabilizationTransferredNativeHomotopyEquiv :
    HomotopyEquiv (laurentMaslovComplex (G.stabilizeX s.castSucc (G.X s).castSucc s) R)
      (stabilizationTransferredMaslovComplex R G s) where
  hom := stabilizationTransferredNativeProjection R G s
  inv := stabilizationTransferredNativeInclusion R G s
  homotopyHomInvId := stabilizationTransferredNativeHomotopy R G s
  homotopyInvHomId := Homotopy.ofEq (stabilizationTransferredNative_inclusion_projection R G s)

end OnLeConjecture.KnotFloer.GridFull

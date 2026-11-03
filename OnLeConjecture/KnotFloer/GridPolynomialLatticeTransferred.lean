/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPolynomialLatticeDouble
public import OnLeConjecture.KnotFloer.GridStabilizationTransferredFilteredComparison

/-!
# The polynomial lattice of the transferred stabilization differential

The constructed transferred differential gives a native graded Laurent complex.
Its polynomial restriction uses the same two coefficient inclusions as the
standard shifted double, with the transferred differential retained explicitly.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]
variable (G : GridDiagram n) (s a : Fin n)

/-- The two homogeneous Laurent summands in the transferred target. -/
abbrev stabilizationLaurentPairPiece (m : ℤ) :=
  laurentMaslovPiece G R m × laurentMaslovPiece G R (m + 1)

/-- The corresponding homogeneous polynomial summands. -/
abbrev stabilizationPolynomialPairPiece (m : ℤ) :=
  oneVariableMaslovPiece R G a m × oneVariableMaslovPiece R G a (m + 1)

/-- Forget the homogeneous proofs in the two Laurent summands. -/
def stabilizationNativePair (m : ℤ) :
    stabilizationLaurentPairPiece R G m →ₗ[R]
      LaurentChain R n × LaurentChain R n :=
  (laurentMaslovPiece G R m).subtype.prodMap (laurentMaslovPiece G R (m + 1)).subtype

omit [CharP R 2] in
/-- The native pair map is injective. -/
theorem stabilizationNativePair_injective (m : ℤ) :
    Function.Injective (stabilizationNativePair R G m) := by
  intro x y h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

/-- The constructed transferred differential between its two homogeneous degrees. -/
def stabilizationTransferredGradedDifferential (m : ℤ) :
    stabilizationLaurentPairPiece R G (m + 1) →ₗ[R]
      stabilizationLaurentPairPiece R G m where
  toFun x :=
    let h : stabilizationTransferredDifferential G s R (stabilizationNativePair R G (m + 1) x) ∈
        stabilizationTargetMaslovPiece G R m := by
      have h' := stabilizationTransferredDifferential_mem_maslovPiece G s R
        (show stabilizationNativePair R G (m + 1) x ∈
          stabilizationTargetMaslovPiece G R (m + 1) from ⟨x.1.property, x.2.property⟩)
      simpa only [add_sub_cancel_right] using h'
    (show laurentMaslovPiece G R m from
      ⟨(stabilizationTransferredDifferential G s R (stabilizationNativePair R G (m + 1) x)).1,
        h.1⟩,
      show laurentMaslovPiece G R (m + 1) from
      ⟨(stabilizationTransferredDifferential G s R (stabilizationNativePair R G (m + 1) x)).2,
        h.2⟩)
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst
        ((stabilizationTransferredDifferential G s R).map_add
          (stabilizationNativePair R G (m + 1) x) (stabilizationNativePair R G (m + 1) y))
    · exact congrArg Prod.snd
        ((stabilizationTransferredDifferential G s R).map_add
          (stabilizationNativePair R G (m + 1) x) (stabilizationNativePair R G (m + 1) y))
  map_smul' r x := by
    have h := ((stabilizationTransferredDifferential G s R).restrictScalars R).map_smul r
      (stabilizationNativePair R G (m + 1) x)
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h

/-- The native graded differential has exactly the transferred Laurent coefficients. -/
theorem stabilizationNativePair_transferredDifferential (m : ℤ)
    (x : stabilizationLaurentPairPiece R G (m + 1)) :
    stabilizationNativePair R G m (stabilizationTransferredGradedDifferential R G s m x) =
      stabilizationTransferredDifferential G s R (stabilizationNativePair R G (m + 1) x) := rfl

/-- The transferred homogeneous differentials square to zero. -/
theorem stabilizationTransferredGradedDifferential_comp (m : ℤ) :
    (stabilizationTransferredGradedDifferential R G s m).comp
      (stabilizationTransferredGradedDifferential R G s (m + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply stabilizationNativePair_injective R G m
  rw [LinearMap.comp_apply, LinearMap.zero_apply, map_zero,
    stabilizationNativePair_transferredDifferential,
    stabilizationNativePair_transferredDifferential]
  exact LinearMap.congr_fun (stabilizationTransferredDifferential_comp_self G s R)
    (stabilizationNativePair R G (m + 1 + 1) x)

/-- The native Maslov-graded complex of the actual transferred differential. -/
def stabilizationTransferredMaslovComplex : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (stabilizationLaurentPairPiece R G m))
    (fun m => ModuleCat.ofHom (stabilizationTransferredGradedDifferential R G s m))
    (fun m => by
      rw [← ModuleCat.ofHom_comp, stabilizationTransferredGradedDifferential_comp,
        ModuleCat.ofHom_zero])

/-- Its differential is the specified transferred homogeneous map. -/
theorem stabilizationTransferredMaslovComplex_d (m : ℤ) :
    (stabilizationTransferredMaslovComplex R G s).d (m + 1) m =
      ModuleCat.ofHom (stabilizationTransferredGradedDifferential R G s m) := by
  simp only [stabilizationTransferredMaslovComplex, ChainComplex.of_d]

/-- A homogeneous pair is polynomial exactly when it has a finite bound
with first coordinate zero. -/
theorem mem_polynomialDouble_iff_exists_zero_level (m : ℤ)
    (x : stabilizationLaurentPairPiece R G m) :
    x ∈ LinearMap.range ((polynomialDoubleInclusion R G a).f m).hom ↔
      ∃ B : ℝ, stabilizationNativePair R G m x ∈
        stabilizationTargetBifiltrationLevel G R 0 B := by
  apply (mem_range_polynomialDoubleInclusion_iff R G a m x).trans
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨B₁, h₁⟩ := (mem_polynomialLattice_iff_exists_zero_level R G a m x.1).mp h₁
    obtain ⟨B₂, h₂⟩ := (mem_polynomialLattice_iff_exists_zero_level R G a (m + 1) x.2).mp h₂
    refine ⟨max B₁ (B₂ - 1), ?_⟩
    exact ⟨laurentBifiltrationLevel_mono G R le_rfl (le_max_left _ _) h₁,
      laurentBifiltrationLevel_mono G R le_rfl (by linarith [le_max_right B₁ (B₂ - 1)]) h₂⟩
  · rintro ⟨B, hB⟩
    exact ⟨(mem_polynomialLattice_iff_exists_zero_level R G a m x.1).mpr ⟨B, hB.1⟩,
      (mem_polynomialLattice_iff_exists_zero_level R G a (m + 1) x.2).mpr ⟨B + 1, hB.2⟩⟩

/-- The actual transferred differential preserves the polynomial coefficient lattice. -/
theorem stabilizationTransferredGradedDifferential_preserves_polynomial (m : ℤ)
    (x : stabilizationLaurentPairPiece R G (m + 1))
    (hx : x ∈ LinearMap.range ((polynomialDoubleInclusion R G a).f (m + 1)).hom) :
    stabilizationTransferredGradedDifferential R G s m x ∈
      LinearMap.range ((polynomialDoubleInclusion R G a).f m).hom := by
  obtain ⟨B, hB⟩ := (mem_polynomialDouble_iff_exists_zero_level R G a (m + 1) x).mp hx
  apply (mem_polynomialDouble_iff_exists_zero_level R G a m _).mpr
  refine ⟨B, ?_⟩
  rw [stabilizationNativePair_transferredDifferential]
  exact stabilizationTransferredDifferential_mem_bifiltrationLevel G s R hB

/-- Restrict the transferred homogeneous differential along the injective polynomial inclusion. -/
def stabilizationTransferredPolynomialDifferential (m : ℤ) :
    stabilizationPolynomialPairPiece R G a (m + 1) →ₗ[R]
      stabilizationPolynomialPairPiece R G a m :=
  ((stabilizationTransferredGradedDifferential R G s m).comp
    ((polynomialDoubleInclusion R G a).f (m + 1)).hom).codRestrictOfInjective
      ((polynomialDoubleInclusion R G a).f m).hom
      (polynomialDoubleInclusion_injective R G a m)
      (fun x => stabilizationTransferredGradedDifferential_preserves_polynomial
        R G s a m _ ⟨x, rfl⟩)

/-- The restricted polynomial differential has the same included Laurent coefficients. -/
theorem stabilizationTransferredPolynomialDifferential_inclusion (m : ℤ)
    (x : stabilizationPolynomialPairPiece R G a (m + 1)) :
    (polynomialDoubleInclusion R G a).f m
        (stabilizationTransferredPolynomialDifferential R G s a m x) =
      stabilizationTransferredGradedDifferential R G s m
        ((polynomialDoubleInclusion R G a).f (m + 1) x) :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ x

/-- The polynomial transferred differentials also square to zero. -/
theorem stabilizationTransferredPolynomialDifferential_comp (m : ℤ) :
    (stabilizationTransferredPolynomialDifferential R G s a m).comp
      (stabilizationTransferredPolynomialDifferential R G s a (m + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply polynomialDoubleInclusion_injective R G a m
  have h₁ := stabilizationTransferredPolynomialDifferential_inclusion R G s a m
    (stabilizationTransferredPolynomialDifferential R G s a (m + 1) x)
  have h₂ := congrArg (stabilizationTransferredGradedDifferential R G s m)
    (stabilizationTransferredPolynomialDifferential_inclusion R G s a (m + 1) x)
  have h₃ := LinearMap.congr_fun (stabilizationTransferredGradedDifferential_comp R G s m)
    ((polynomialDoubleInclusion R G a).f (m + 1 + 1) x)
  exact (h₁.trans (h₂.trans h₃)).trans (((polynomialDoubleInclusion R G a).f m).hom.map_zero).symm

/-- The native polynomial complex with the constructed transferred differential. -/
def stabilizationTransferredPolynomialComplex : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (stabilizationPolynomialPairPiece R G a m))
    (fun m => ModuleCat.ofHom (stabilizationTransferredPolynomialDifferential R G s a m))
    (fun m => by
      rw [← ModuleCat.ofHom_comp, stabilizationTransferredPolynomialDifferential_comp,
        ModuleCat.ofHom_zero])

/-- Coefficient inclusion for the actual transferred polynomial and Laurent complexes. -/
def stabilizationTransferredPolynomialInclusion :
    stabilizationTransferredPolynomialComplex R G s a ⟶
      stabilizationTransferredMaslovComplex R G s where
  f m := (polynomialDoubleInclusion R G a).f m
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    simp only [stabilizationTransferredPolynomialComplex, stabilizationTransferredMaslovComplex,
      ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (stabilizationTransferredPolynomialDifferential_inclusion R G s a j x).symm

/-- The polynomial coefficient inclusion for the transferred differential
is injective degreewise. -/
theorem stabilizationTransferredPolynomialInclusion_injective (m : ℤ) :
    Function.Injective ((stabilizationTransferredPolynomialInclusion R G s a).f m) :=
  polynomialDoubleInclusion_injective R G a m

/-- Its degreewise image is the first-coordinate-zero polynomial lattice. -/
theorem mem_range_stabilizationTransferredPolynomialInclusion_iff (m : ℤ)
    (x : (stabilizationTransferredMaslovComplex R G s).X m) :
    x ∈ LinearMap.range ((stabilizationTransferredPolynomialInclusion R G s a).f m).hom ↔
      ∃ B : ℝ, stabilizationNativePair R G m x ∈
        stabilizationTargetBifiltrationLevel G R 0 B :=
  mem_polynomialDouble_iff_exists_zero_level R G a m x

/-- Polynomial homology inside the actual transferred Laurent homology. -/
def stabilizationTransferredPolynomialHomologyImage (m : ℤ) :
    Submodule R ((stabilizationTransferredMaslovComplex R G s).homology m) :=
  LinearMap.range (homologyMap (stabilizationTransferredPolynomialInclusion R G s a) m).hom

end OnLeConjecture.KnotFloer.GridFull

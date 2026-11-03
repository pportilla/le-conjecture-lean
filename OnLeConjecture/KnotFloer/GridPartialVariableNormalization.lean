/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPartialVariableCone
public import OnLeConjecture.KnotFloer.GridVariableQuotientComplex

/-!
# Native normalization after any finite set of variable identifications

Adding one new variable relation has a concrete Maslov-graded cone comparison.
The geometric X-marking shear splits that cone into two copies of the earlier
identified complex, with the second copy shifted by `(M,A)=(-1,-1)`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti MvPolynomial CategoryTheory HomologicalComplex

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The homogeneous cone pair with all earlier coefficient identifications imposed. -/
noncomputable def identifiedConeMaslovPiece (a : Fin n) (s : Finset (Fin n))
    (m : ℤ) : Submodule R (VariableConeChains R n) :=
  variableConeMaslovPiece G R m ⊓ identifiedConeChains R a s

/-- Either the next relation cone or its split two-summand differential. -/
noncomputable def identifiedPairDifferential (a b : Fin n) (s : Finset (Fin n))
    (twisted : Bool) : VariableConeChains R n →ₗ[R] VariableConeChains R n :=
  if twisted then identifiedConeDifferential G R a b s else identifiedSplitDifferential G R a s

omit [CharP R 2] in
/-- Both next-step pair differentials preserve the imposed identifications and lower degree. -/
theorem identifiedPairDifferential_mem (a b : Fin n) (s : Finset (Fin n)) (hb : b ∉ s)
    (twisted : Bool) {m : ℤ} {c : VariableConeChains R n}
    (hc : c ∈ identifiedConeMaslovPiece G R a s m) :
    identifiedPairDifferential G R a b s twisted c ∈
      identifiedConeMaslovPiece G R a s (m - 1) := by
  have h₁ := identifiedDifferential_mem_maslovPiece R G a s hc.1.1
  have h₂ := identifiedDifferential_mem_maslovPiece R G a s hc.1.2
  have hf := variableRelationAction_mem_maslovPiece G R a b hc.1.2
  have h₂' : identifiedDifferential R G a s c.2 ∈ maslovPiece G R (m - 1 + 1) := by
    simpa only [add_sub_cancel_right, sub_add_cancel] using h₂
  have hf' : variableRelationAction R a b c.2 ∈ maslovPiece G R (m - 1) := by
    simpa only [show m + 1 - 2 = m - 1 by omega] using hf
  cases twisted
  · exact ⟨⟨h₁, h₂'⟩,
      identifiedDifferential_mem_identifiedChains R G a s c.1,
      identifiedDifferential_mem_identifiedChains R G a s c.2⟩
  · exact ⟨⟨Submodule.add_mem _ h₁ hf', h₂'⟩,
      Submodule.add_mem _ (identifiedDifferential_mem_identifiedChains R G a s c.1)
        (relation_smul_mem_identifiedChains R a b s hb hc.2.2),
      identifiedDifferential_mem_identifiedChains R G a s c.2⟩

/-- Both next-step pair differentials square to zero. -/
theorem identifiedPairDifferential_sq (a b : Fin n) (s : Finset (Fin n)) (hb : b ∉ s)
    (twisted : Bool) (c : VariableConeChains R n) :
    identifiedPairDifferential G R a b s twisted
      (identifiedPairDifferential G R a b s twisted c) = 0 := by
  cases twisted
  · exact Prod.ext (identifiedDifferential_sq R G a s c.1)
      (identifiedDifferential_sq R G a s c.2)
  · exact identifiedConeDifferential_sq G R a b s hb c

/-- Restrict the explicit pair differential to consecutive Maslov degrees. -/
noncomputable def identifiedPairGradedDifferential (a b : Fin n) (s : Finset (Fin n))
    (hb : b ∉ s) (twisted : Bool) (m : ℤ) :
    identifiedConeMaslovPiece G R a s (m + 1) →ₗ[R] identifiedConeMaslovPiece G R a s m :=
  (identifiedPairDifferential G R a b s twisted).restrict fun _ hc => by
    simpa using identifiedPairDifferential_mem G R a b s hb twisted hc

/-- The native next-step cone complex or its split two-summand counterpart. -/
noncomputable def identifiedPairComplex (a b : Fin n) (s : Finset (Fin n))
    (hb : b ∉ s) (twisted : Bool) : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (identifiedConeMaslovPiece G R a s m))
    (fun m => ModuleCat.ofHom (identifiedPairGradedDifferential G R a b s hb twisted m))
    (fun m => by
      ext c : 2
      exact Subtype.ext (identifiedPairDifferential_sq G R a b s hb twisted c))

theorem identifiedPairComplex_d (a b : Fin n) (s : Finset (Fin n))
    (hb : b ∉ s) (twisted : Bool) (m : ℤ) :
    (identifiedPairComplex G R a b s hb twisted).d (m + 1) m =
      ModuleCat.ofHom (identifiedPairGradedDifferential G R a b s hb twisted m) := by
  simp only [identifiedPairComplex, ChainComplex.of_d]

/-- The next cone projection in a fixed Maslov degree. -/
noncomputable def identifiedConeToQuotientPiece (a b : Fin n) (s : Finset (Fin n)) (m : ℤ) :
    identifiedConeMaslovPiece G R a s m →ₗ[R]
      identifiedMaslovPiece R G a (insert b s) m :=
  (identifiedConeToQuotient R a b).restrict fun _ hc =>
    ⟨quotientProjection_mem_maslovPiece G R a b hc.1.1,
      identifiedConeToQuotient_mem R a b s hc.2⟩

/-- The corrected next quotient inclusion in a fixed Maslov degree. -/
noncomputable def identifiedQuotientToConePiece (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) (m : ℤ) :
    identifiedMaslovPiece R G a (insert b s) m →ₗ[R]
      identifiedConeMaslovPiece G R a s m :=
  (identifiedQuotientToCone G R a b s).restrict fun c hc => by
    refine ⟨⟨hc.1, ?_⟩, identifiedQuotientToCone_mem G R a b hab s hb hc.2⟩
    have h := variableSumChainDivision_mem_maslovPiece R G a b
      (identifiedDifferential_mem_maslovPiece R G a s hc.1)
    change variableSumChainDivision R a b (identifiedDifferential R G a s c) ∈
      maslovPiece G R (m + 1)
    simpa only [show m - 1 + 2 = m + 1 by omega] using h

/-- The next cone projection as a native graded chain map. -/
noncomputable def identifiedConeToQuotientHom (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) :
    identifiedPairComplex G R a b s hb true ⟶ identifiedMaslovComplex R G a (insert b s) where
  f m := ModuleCat.ofHom (identifiedConeToQuotientPiece G R a b s m)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    rw [identifiedPairComplex_d, identifiedMaslovComplex_d]
    ext c : 2
    exact Subtype.ext (identifiedConeToQuotient_differential G R a b hab s hb
      ((show identifiedConeMaslovPiece G R a s (j + 1) from c) : VariableConeChains R n)).symm

/-- The corrected inclusion as a native graded chain map. -/
noncomputable def identifiedQuotientToConeHom (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) :
    identifiedMaslovComplex R G a (insert b s) ⟶ identifiedPairComplex G R a b s hb true where
  f m := ModuleCat.ofHom (identifiedQuotientToConePiece G R a b hab s hb m)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    rw [identifiedPairComplex_d, identifiedMaslovComplex_d]
    ext c : 2
    exact Subtype.ext (identifiedQuotientToCone_differential G R a b hab s hb
      ((show identifiedMaslovPiece R G a (insert b s) (j + 1) from c) : GridChainMinus R n))

/-- The next quotient-side composite is the identity chain map. -/
theorem identifiedQuotientToConeHom_comp (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) :
    identifiedQuotientToConeHom G R a b hab s hb ≫
      identifiedConeToQuotientHom G R a b hab s hb =
        𝟙 (identifiedMaslovComplex R G a (insert b s)) := by
  ext m : 1
  ext c : 2
  exact Subtype.ext (identifiedConeToQuotient_quotientToCone G R a b s c.property.2)

/-- The division contraction on the restricted cone raises Maslov degree by one. -/
noncomputable def identifiedQuotientConeHomotopyPiece (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) (m : ℤ) :
    identifiedConeMaslovPiece G R a s m →ₗ[R] identifiedConeMaslovPiece G R a s (m + 1) :=
  (variableQuotientConeHomotopy R a b).restrict fun _ hc =>
    ⟨quotientConeHomotopy_mem_maslovPiece G R a b hc.1,
      identifiedQuotientConeHomotopy_mem R a b hab s hb hc.2⟩

/-- The contraction between arbitrary native complex degrees. -/
noncomputable def identifiedQuotientConeHomotopyComponent (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) (i j : ℤ) :
    (identifiedPairComplex G R a b s hb true).X i ⟶
      (identifiedPairComplex G R a b s hb true).X j :=
  if hij : j = i + 1 then
    (by subst j; exact ModuleCat.ofHom (identifiedQuotientConeHomotopyPiece G R a b hab s hb i))
  else 0

@[simp]
theorem identifiedQuotientConeHomotopyComponent_succ (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) (i : ℤ) :
    identifiedQuotientConeHomotopyComponent G R a b hab s hb i (i + 1) =
      ModuleCat.ofHom (identifiedQuotientConeHomotopyPiece G R a b hab s hb i) := by
  simp [identifiedQuotientConeHomotopyComponent]
  rfl

private theorem pair_add_self (c : VariableConeChains R n) : c + c = 0 := by
  apply Prod.ext <;> apply Finsupp.ext <;> intro x <;> exact CharTwo.add_self_eq_zero _

/-- The next comparison equation in the order required by native chain homotopies. -/
theorem identifiedQuotientCone_homotopy_rearranged (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) (c : VariableConeChains R n) :
    identifiedQuotientToCone G R a b s (identifiedConeToQuotient R a b c) =
      variableQuotientConeHomotopy R a b (identifiedConeDifferential G R a b s c) +
      identifiedConeDifferential G R a b s (variableQuotientConeHomotopy R a b c) + c := by
  let A := identifiedQuotientToCone G R a b s (identifiedConeToQuotient R a b c)
  let B := identifiedConeDifferential G R a b s (variableQuotientConeHomotopy R a b c)
  let C := variableQuotientConeHomotopy R a b (identifiedConeDifferential G R a b s c)
  have h : A + B + C = c := identifiedQuotientCone_homotopy G R a b hab s hb c
  change A = C + B + c
  calc
    A = A + ((B + C) + (B + C)) := by rw [pair_add_self, add_zero]
    _ = (A + B + C) + (C + B) := by abel
    _ = C + B + c := by rw [h]; abel

/-- The next divided comparison gives a native inverse homotopy. -/
noncomputable def identifiedQuotientConeNativeHomotopy (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) :
    Homotopy (identifiedConeToQuotientHom G R a b hab s hb ≫
      identifiedQuotientToConeHom G R a b hab s hb)
        (𝟙 (identifiedPairComplex G R a b s hb true)) where
  hom := identifiedQuotientConeHomotopyComponent G R a b hab s hb
  zero i j hij := by
    have h : j ≠ i + 1 := fun h => hij h.symm
    simp [identifiedQuotientConeHomotopyComponent, h]
  comm i := by
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, m + 1 = i := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel ((m + 1) + 1) (m + 1) from rfl)]
    simp only [identifiedQuotientConeHomotopyComponent_succ, identifiedPairComplex_d]
    ext c : 2
    exact Subtype.ext (identifiedQuotientCone_homotopy_rearranged G R a b hab s hb
      ((show identifiedConeMaslovPiece G R a s (m + 1) from c) : VariableConeChains R n))

/-- The next variable quotient is homotopy equivalent to its genuine graded cone. -/
noncomputable def identifiedQuotientConeHomotopyEquiv (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) :
    HomotopyEquiv (identifiedPairComplex G R a b s hb true)
      (identifiedMaslovComplex R G a (insert b s)) where
  hom := identifiedConeToQuotientHom G R a b hab s hb
  inv := identifiedQuotientToConeHom G R a b hab s hb
  homotopyHomInvId := identifiedQuotientConeNativeHomotopy G R a b hab s hb
  homotopyInvHomId := Homotopy.ofEq (identifiedQuotientToConeHom_comp G R a b hab s hb)

omit [CharP R 2] in
/-- The geometric shear preserves the earlier identified homogeneous cone. -/
theorem identifiedConeShear_mem_maslovPiece (hG : G.IsKnot) (a b : Fin n)
    (s : Finset (Fin n)) {m : ℤ} {c : VariableConeChains R n}
    (hc : c ∈ identifiedConeMaslovPiece G R a s m) :
    identifiedConeShear G R hG a b s c ∈ identifiedConeMaslovPiece G R a s m := by
  refine ⟨⟨Submodule.add_mem _ hc.1.1 ?_, hc.1.2⟩,
    identifiedConeShear_mem G R hG a b s hc.2⟩
  simpa using identifiedVariableHomotopy_mem_maslovPiece R G hG a b s hc.1.2

/-- The restricted geometric shear is an involutive equivalence in every degree. -/
noncomputable def identifiedConeShearPieceEquiv (hG : G.IsKnot) (a b : Fin n)
    (s : Finset (Fin n)) (m : ℤ) :
    identifiedConeMaslovPiece G R a s m ≃ₗ[R] identifiedConeMaslovPiece G R a s m :=
  { toLinearMap := (identifiedConeShear G R hG a b s).restrict
      fun _ hc => identifiedConeShear_mem_maslovPiece G R hG a b s hc
    invFun := fun c => ⟨identifiedConeShear G R hG a b s c,
      identifiedConeShear_mem_maslovPiece G R hG a b s c.property⟩
    left_inv := fun c => Subtype.ext (identifiedConeShear_involutive G R hG a b s c)
    right_inv := fun c => Subtype.ext (identifiedConeShear_involutive G R hG a b s c) }

/-- The next graded cone splits into the two shifted earlier identified summands. -/
noncomputable def identifiedConeSplitIso (hG : G.IsKnot) (a b : Fin n)
    (s : Finset (Fin n)) (hb : b ∉ s) :
    identifiedPairComplex G R a b s hb true ≅ identifiedPairComplex G R a b s hb false :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => (identifiedConeShearPieceEquiv G R hG a b s m).toModuleIso) (by
      intro i j hij
      rw [ComplexShape.down_Rel] at hij
      subst i
      rw [identifiedPairComplex_d, identifiedPairComplex_d]
      ext c : 2
      exact Subtype.ext (identifiedConeShear_differential G R hG a b s hb c.property.2).symm)

/-- The split-side inverse homotopy is the conjugate of the divided contraction. -/
noncomputable def identifiedNormalizationSplitHomotopy (hG : G.IsKnot) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    Homotopy ((identifiedConeSplitIso G R hG a b s hb).inv ≫
      identifiedConeToQuotientHom G R a b hab s hb ≫
      identifiedQuotientToConeHom G R a b hab s hb ≫
      (identifiedConeSplitIso G R hG a b s hb).hom)
      (𝟙 (identifiedPairComplex G R a b s hb false)) where
  hom i j := ((identifiedConeSplitIso G R hG a b s hb).inv.f i ≫
    (identifiedQuotientConeNativeHomotopy G R a b hab s hb).hom i j) ≫
      (identifiedConeSplitIso G R hG a b s hb).hom.f j
  zero i j hij := by
    simp [(identifiedQuotientConeNativeHomotopy G R a b hab s hb).zero i j hij]
  comm i := by
    have h := (((identifiedQuotientConeNativeHomotopy G R a b hab s hb).compLeft
      (identifiedConeSplitIso G R hG a b s hb).inv).compRight
        (identifiedConeSplitIso G R hG a b s hb).hom).comm i
    dsimp only [Homotopy.compLeft, Homotopy.compRight] at h
    simpa only [Category.assoc, Category.id_comp, Iso.inv_hom_id] using h

/-- Adding a new variable identification produces the shifted two-copy normalization. -/
noncomputable def identifiedNormalizationHomotopyEquiv (hG : G.IsKnot) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    HomotopyEquiv (identifiedMaslovComplex R G a (insert b s))
      (identifiedPairComplex G R a b s hb false) where
  hom := identifiedQuotientToConeHom G R a b hab s hb ≫
    (identifiedConeSplitIso G R hG a b s hb).hom
  inv := (identifiedConeSplitIso G R hG a b s hb).inv ≫
    identifiedConeToQuotientHom G R a b hab s hb
  homotopyHomInvId := Homotopy.ofEq (by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, identifiedQuotientToConeHom_comp])
  homotopyInvHomId := by simpa only [Category.assoc] using
    identifiedNormalizationSplitHomotopy G R hG a b hab s hb

end OnLeConjecture.KnotFloer.GridFull

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridVariableQuotientCone

/-!
# Native graded complexes for the variable quotient comparison

The full variable-dependent grid differential descends to the quotient by
`V_a + V_b`. The representative model is identified with the genuine module
quotient in `GridVariableQuotientCone`. This file restricts the explicit maps
and contraction to Maslov homogeneous pieces.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The homogeneous part of the canonical representative model of the variable quotient. -/
noncomputable def variableQuotientMaslovPiece (a b : Fin n) (m : ℤ) :
    Submodule R (GridChainMinus R n) :=
  maslovPiece G R m ⊓ variableQuotientRepresentatives R a b

/-- The quotient differential restricted to consecutive Maslov degrees. -/
noncomputable def variableQuotientGradedDifferential (a b : Fin n) (hab : a ≠ b) (m : ℤ) :
    variableQuotientMaslovPiece G R a b (m + 1) →ₗ[R] variableQuotientMaslovPiece G R a b m :=
  ((variableQuotientProjection R a b).comp ((differential G R).restrictScalars R)).restrict
    fun c hc => ⟨quotientProjection_mem_maslovPiece G R a b
      (by simpa using differential_mem_maslovPiece G hc.1),
      division_quotientProjection R a b hab (differential G R c)⟩

/-- Restricted quotient differentials compose to zero. -/
theorem variableQuotientGradedDifferential_comp_eq_zero (a b : Fin n) (hab : a ≠ b) (m : ℤ) :
    (variableQuotientGradedDifferential G R a b hab m).comp
      (variableQuotientGradedDifferential G R a b hab (m + 1)) = 0 := by
  ext c : 1
  apply Subtype.ext
  change variableQuotientProjection R a b
    (differential G R (variableQuotientProjection R a b (differential G R c))) = 0
  rw [quotientProjection_differential_projection G R a b hab, differential_sq_eq_zero, map_zero]

/-- The genuine Maslov-graded quotient complex, expressed through its canonical representatives. -/
noncomputable def variableQuotientComplex (a b : Fin n) (hab : a ≠ b) :
    ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (variableQuotientMaslovPiece G R a b m))
    (fun m => ModuleCat.ofHom (variableQuotientGradedDifferential G R a b hab m))
    (fun m => by rw [← ModuleCat.ofHom_comp,
      variableQuotientGradedDifferential_comp_eq_zero, ModuleCat.ofHom_zero])

theorem variableQuotientComplex_d (a b : Fin n) (hab : a ≠ b) (m : ℤ) :
    (variableQuotientComplex G R a b hab).d (m + 1) m =
      ModuleCat.ofHom (variableQuotientGradedDifferential G R a b hab m) := by
  simp only [variableQuotientComplex, ChainComplex.of_d]

/-- The cone projection restricted to one Maslov degree. -/
noncomputable def variableConeToQuotientPiece (a b : Fin n) (hab : a ≠ b) (m : ℤ) :
    variableConeMaslovPiece G R m →ₗ[R] variableQuotientMaslovPiece G R a b m :=
  ((variableQuotientProjection R a b).comp (LinearMap.fst _ _ _)).restrict fun c hc =>
    ⟨quotientProjection_mem_maslovPiece G R a b hc.1,
      division_quotientProjection R a b hab c.1⟩

/-- The corrected inclusion restricted to one Maslov degree. -/
noncomputable def variableQuotientToConePiece (a b : Fin n) (m : ℤ) :
    variableQuotientMaslovPiece G R a b m →ₗ[R] variableConeMaslovPiece G R m :=
  ((variableQuotientToCone G R a b).comp
    (Submodule.inclusion (inf_le_right : variableQuotientMaslovPiece G R a b m ≤
      variableQuotientRepresentatives R a b))).codRestrict _ fun c =>
        quotientToCone_mem_maslovPiece G R a b ⟨c, c.property.2⟩ c.property.1

/-- The cone projection as a morphism of native integer-graded complexes. -/
noncomputable def variableConeToQuotientHom (hG : G.IsKnot) (a b : Fin n) (hab : a ≠ b) :
    variablePairComplex G R hG a b true ⟶ variableQuotientComplex G R a b hab where
  f m := ModuleCat.ofHom (variableConeToQuotientPiece G R a b hab m)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    rw [variablePairComplex_d, variableQuotientComplex_d]
    ext c : 2
    exact Subtype.ext (congrArg Subtype.val (variableConeToQuotient_differential G R a b hab
      ((show variableConeMaslovPiece G R (j + 1) from c) : VariableConeChains R n))).symm

/-- The corrected inclusion as a morphism of native integer-graded complexes. -/
noncomputable def variableQuotientToConeHom (hG : G.IsKnot) (a b : Fin n) (hab : a ≠ b) :
    variableQuotientComplex G R a b hab ⟶ variablePairComplex G R hG a b true where
  f m := ModuleCat.ofHom (variableQuotientToConePiece G R a b m)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    rw [variableQuotientComplex_d, variablePairComplex_d]
    ext c : 2
    exact Subtype.ext (variableQuotientToCone_differential G R a b hab
      ⟨(show variableQuotientMaslovPiece G R a b (j + 1) from c), c.property.2⟩)

/-- The quotient-side composite is exactly the identity native chain map. -/
theorem variableQuotientToConeHom_comp (hG : G.IsKnot) (a b : Fin n) (hab : a ≠ b) :
    variableQuotientToConeHom G R hG a b hab ≫ variableConeToQuotientHom G R hG a b hab =
      𝟙 (variableQuotientComplex G R a b hab) := by
  ext m : 1
  ext c : 2
  apply Subtype.ext
  change variableQuotientProjection R a b
    ((show variableQuotientMaslovPiece G R a b m from c) : GridChainMinus R n) = _
  exact quotientProjection_eq_self R a b c.property.2

/-- The divided first component as a homogeneous degree-one linear map. -/
noncomputable def variableQuotientConeHomotopyPiece (a b : Fin n) (m : ℤ) :
    variableConeMaslovPiece G R m →ₗ[R] variableConeMaslovPiece G R (m + 1) :=
  (variableQuotientConeHomotopy R a b).restrict fun _ hc =>
    quotientConeHomotopy_mem_maslovPiece G R a b hc

/-- The explicit contraction component between arbitrary native complex degrees. -/
noncomputable def variableQuotientConeHomotopyComponent (hG : G.IsKnot) (a b : Fin n) (i j : ℤ) :
    (variablePairComplex G R hG a b true).X i ⟶ (variablePairComplex G R hG a b true).X j :=
  if hij : j = i + 1 then
    (by subst j; exact ModuleCat.ofHom (variableQuotientConeHomotopyPiece G R a b i))
  else 0

@[simp]
theorem variableQuotientConeHomotopyComponent_succ (hG : G.IsKnot) (a b : Fin n) (i : ℤ) :
    variableQuotientConeHomotopyComponent G R hG a b i (i + 1) =
      ModuleCat.ofHom (variableQuotientConeHomotopyPiece G R a b i) := by
  simp [variableQuotientConeHomotopyComponent]
  rfl

private theorem pair_add_self (c : VariableConeChains R n) : c + c = 0 := by
  apply Prod.ext <;> apply Finsupp.ext <;> intro x <;> exact CharTwo.add_self_eq_zero _

/-- The concrete contraction equation in the order used by native chain homotopies. -/
theorem variableQuotientCone_homotopy_rearranged (a b : Fin n) (hab : a ≠ b)
    (c : VariableConeChains R n) :
    variableQuotientToCone G R a b (variableConeToQuotient R a b hab c) =
      variableQuotientConeHomotopy R a b (variableConeDifferential G R a b c) +
      variableConeDifferential G R a b (variableQuotientConeHomotopy R a b c) + c := by
  let A := variableQuotientToCone G R a b (variableConeToQuotient R a b hab c)
  let B := variableConeDifferential G R a b (variableQuotientConeHomotopy R a b c)
  let C := variableQuotientConeHomotopy R a b (variableConeDifferential G R a b c)
  have h : A + B + C = c := variableQuotientCone_homotopy G R a b hab c
  change A = C + B + c
  calc
    A = A + ((B + C) + (B + C)) := by rw [pair_add_self, add_zero]
    _ = (A + B + C) + (C + B) := by abel
    _ = C + B + c := by rw [h]; abel

/-- The divided first component supplies the native source inverse homotopy. -/
noncomputable def variableQuotientConeNativeHomotopy (hG : G.IsKnot) (a b : Fin n)
    (hab : a ≠ b) :
    Homotopy (variableConeToQuotientHom G R hG a b hab ≫
      variableQuotientToConeHom G R hG a b hab) (𝟙 (variablePairComplex G R hG a b true)) where
  hom := variableQuotientConeHomotopyComponent G R hG a b
  zero i j hij := by
    have h : j ≠ i + 1 := fun h => hij h.symm
    simp [variableQuotientConeHomotopyComponent, h]
  comm i := by
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, m + 1 = i := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel ((m + 1) + 1) (m + 1) from rfl)]
    simp only [variableQuotientConeHomotopyComponent_succ, variablePairComplex_d]
    ext c : 2
    apply Subtype.ext
    exact variableQuotientCone_homotopy_rearranged G R a b hab
      ((show variableConeMaslovPiece G R (m + 1) from c) : VariableConeChains R n)

/-- The actual variable quotient is homotopy equivalent to its integer-graded cone. -/
noncomputable def variableQuotientConeHomotopyEquiv (hG : G.IsKnot) (a b : Fin n) (hab : a ≠ b) :
    HomotopyEquiv (variablePairComplex G R hG a b true) (variableQuotientComplex G R a b hab) where
  hom := variableConeToQuotientHom G R hG a b hab
  inv := variableQuotientToConeHom G R hG a b hab
  homotopyHomInvId := variableQuotientConeNativeHomotopy G R hG a b hab
  homotopyInvHomId := Homotopy.ofEq (variableQuotientToConeHom_comp G R hG a b hab)

omit [CharP R 2] in
/-- Polynomial exponents make the first coordinate nonpositive, independently of its prior bound. -/
theorem polynomial_bifiltration_first_zero {u v : ℝ} {c : GridChainMinus R n}
    (hc : c ∈ bifiltrationLevel G R u v) : c ∈ bifiltrationLevel G R 0 v := by
  rw [mem_bifiltrationLevel_iff] at hc ⊢
  intro x e he
  exact ⟨neg_nonpos.mpr (Nat.cast_nonneg _), (hc x e he).2⟩

omit [CharP R 2] in
/-- The same nonpositivity holds for both polynomial components of the shifted cone. -/
theorem variableConeBifiltration_first_zero {u v : ℝ} {c : VariableConeChains R n}
    (hc : c ∈ variableConeBifiltrationLevel G R u v) :
    c ∈ variableConeBifiltrationLevel G R 0 v :=
  ⟨polynomial_bifiltration_first_zero G R hc.1, polynomial_bifiltration_first_zero G R hc.2⟩

/-- The Alexander filtration on the explicit shifted cone. -/
noncomputable def variableConeAlexanderFiltration (hG : G.IsKnot) (a b : Fin n) :
    RealFiltration (variablePairComplex G R hG a b true) where
  level v m := (variablePairBifiltration G R hG a b true).level 0 v m
  mono m v v' hv := (variablePairBifiltration G R hG a b true).mono m 0 v 0 v' le_rfl hv
  differential_mem v i j c hc :=
    (variablePairBifiltration G R hG a b true).differential_mem 0 v i j c hc

/-- The quotient Alexander filtration on its canonical homogeneous representatives. -/
noncomputable def variableQuotientAlexanderFiltration (a b : Fin n) (hab : a ≠ b) :
    RealFiltration (variableQuotientComplex G R a b hab) where
  level v m := ((bifiltrationLevel G R 0 v).restrictScalars R).comap
    (variableQuotientMaslovPiece G R a b m).subtype
  mono m v v' hv := Submodule.comap_mono (bifiltrationLevel_mono G R le_rfl hv)
  differential_mem v i j c hc := by
    by_cases h : j + 1 = i
    · subst i
      rw [variableQuotientComplex_d]
      change variableQuotientProjection R a b
        (differential G R ((show variableQuotientMaslovPiece G R a b (j + 1) from c) :
          GridChainMinus R n)) ∈ bifiltrationLevel G R 0 v
      exact quotientProjection_mem_bifiltrationLevel G R a b
        (differential_mem_bifiltrationLevel G R 0 v _ hc)
    · rw [(variableQuotientComplex G R a b hab).shape i j h]
      exact Submodule.zero_mem _

/-- The native cone projection preserves Alexander filtration. -/
theorem variableConeToQuotientHom_preserves_Alexander (hG : G.IsKnot) (a b : Fin n)
    (hab : a ≠ b) :
    (variableConeAlexanderFiltration G R hG a b).Preserves
      (variableQuotientAlexanderFiltration G R a b hab)
        (variableConeToQuotientHom G R hG a b hab) := by
  intro v m c hc
  exact quotientProjection_mem_bifiltrationLevel G R a b hc.1

/-- The corrected native quotient inclusion preserves Alexander filtration. -/
theorem variableQuotientToConeHom_preserves_Alexander (hG : G.IsKnot) (a b : Fin n)
    (hab : a ≠ b) :
    (variableQuotientAlexanderFiltration G R a b hab).Preserves
      (variableConeAlexanderFiltration G R hG a b)
        (variableQuotientToConeHom G R hG a b hab) := by
  intro v m c hc
  exact variableConeBifiltration_first_zero G R
    (quotientToCone_mem_bifiltrationLevel G R a b
      ⟨(show variableQuotientMaslovPiece G R a b m from c), c.property.2⟩ hc)

/-- The native inverse homotopy also preserves Alexander filtration in every degree. -/
theorem variableQuotientConeNativeHomotopy_preserves_Alexander (hG : G.IsKnot) (a b : Fin n)
    (hab : a ≠ b) (v : ℝ) (i j : ℤ)
    (c : (variablePairComplex G R hG a b true).X i)
    (hc : c ∈ (variableConeAlexanderFiltration G R hG a b).level v i) :
    (variableQuotientConeNativeHomotopy G R hG a b hab).hom i j c ∈
      (variableConeAlexanderFiltration G R hG a b).level v j := by
  change variableQuotientConeHomotopyComponent G R hG a b i j c ∈ _
  by_cases h : j = i + 1
  · subst j
    rw [variableQuotientConeHomotopyComponent_succ]
    exact variableConeBifiltration_first_zero G R
      (quotientConeHomotopy_mem_bifiltrationLevel G R a b hc)
  · simp only [variableQuotientConeHomotopyComponent, dif_neg h]
    exact Submodule.zero_mem _

end OnLeConjecture.KnotFloer.GridFull

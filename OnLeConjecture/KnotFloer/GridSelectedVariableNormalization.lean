/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridSelectedVariableComplex

/-!
# Polynomial-linear normalization of the total grid complex

The next coefficient identification is homotopy equivalent over R[U] to the
two-copy complex. The maps and inverse homotopies are the divided inclusion,
coefficient projection, and geometric X-marking shear already used in the
Maslov-graded, Alexander-filtered normalization.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]

/-- The two total chain summands, over the selected polynomial variable. -/
noncomputable def selectedVariablePairModule (a : Fin n) : ModuleCat (Polynomial R) :=
  (ModuleCat.restrictScalars (oneVariableSection R a).toRingHom).obj
    (ModuleCat.of (MvPolynomial (Fin n) R) (VariableConeChains R n))

/-- Both components satisfy the earlier variable identifications. -/
noncomputable def selectedIdentifiedPairSubmodule (a : Fin n) (s : Finset (Fin n)) :
    Submodule (Polynomial R) (selectedVariablePairModule R a) where
  carrier := {c | (show VariableConeChains R n from c) ∈ identifiedConeChains R a s}
  zero_mem' := (identifiedConeChains R a s).zero_mem
  add_mem' := (identifiedConeChains R a s).add_mem
  smul_mem' p c hc := by
    exact ⟨(selectedIdentifiedSubmodule R a s).smul_mem p hc.1,
      (selectedIdentifiedSubmodule R a s).smul_mem p hc.2⟩

/-- The identified cone pair as an R[U] module. -/
noncomputable def selectedIdentifiedPairModule (a : Fin n) (s : Finset (Fin n)) :
    ModuleCat (Polynomial R) :=
  ModuleCat.of (Polynomial R) (selectedIdentifiedPairSubmodule R a s)

omit [CharP R 2] in
/-- The pair differential is linear over every retained-variable polynomial. -/
theorem identifiedPairDifferential_selected_smul (G : GridDiagram n) (a b : Fin n)
    (s : Finset (Fin n)) (twisted : Bool) (p : Polynomial R) (c : VariableConeChains R n) :
    identifiedPairDifferential G R a b s twisted (oneVariableSection R a p • c) =
      oneVariableSection R a p • identifiedPairDifferential G R a b s twisted c := by
  cases twisted
  · exact Prod.ext (identifiedDifferential_selected_smul R G a s p c.1)
      (identifiedDifferential_selected_smul R G a s p c.2)
  · apply Prod.ext
    · change identifiedDifferential R G a s (oneVariableSection R a p • c.1) +
        (MvPolynomial.X a + MvPolynomial.X b : MvPolynomial (Fin n) R) •
          (oneVariableSection R a p • c.2) = _
      rw [identifiedDifferential_selected_smul, smul_comm, ← smul_add]
      rfl
    · exact identifiedDifferential_selected_smul R G a s p c.2

omit [CharP R 2] in
/-- Both cone differentials preserve the already identified module. -/
theorem identifiedPairDifferential_mem_identified (G : GridDiagram n) (a b : Fin n)
    (s : Finset (Fin n)) (hb : b ∉ s) (twisted : Bool)
    {c : VariableConeChains R n} (hc : c ∈ identifiedConeChains R a s) :
    identifiedPairDifferential G R a b s twisted c ∈ identifiedConeChains R a s := by
  cases twisted
  · exact ⟨identifiedDifferential_mem_identifiedChains R G a s c.1,
      identifiedDifferential_mem_identifiedChains R G a s c.2⟩
  · exact ⟨Submodule.add_mem _ (identifiedDifferential_mem_identifiedChains R G a s c.1)
      (relation_smul_mem_identifiedChains R a b s hb hc.2),
      identifiedDifferential_mem_identifiedChains R G a s c.2⟩

/-- The R[U]-linear cone or split differential. -/
noncomputable def selectedPairDifferential (G : GridDiagram n) (a b : Fin n)
    (s : Finset (Fin n)) (hb : b ∉ s) (twisted : Bool) :
    selectedIdentifiedPairModule R a s ⟶ selectedIdentifiedPairModule R a s :=
  ModuleCat.ofHom {
    toFun c := ⟨identifiedPairDifferential G R a b s twisted c.val,
      identifiedPairDifferential_mem_identified R G a b s hb twisted c.property⟩
    map_add' c d := Subtype.ext (map_add _ c.val d.val)
    map_smul' p c := Subtype.ext (identifiedPairDifferential_selected_smul R G a b s
      twisted p c.val) }

/-- The total cone or split complex with its retained polynomial action. -/
noncomputable def selectedPairComplex (G : GridDiagram n) (a b : Fin n)
    (s : Finset (Fin n)) (hb : b ∉ s) (twisted : Bool) :
    HomologicalComplex (ModuleCat (Polynomial R)) (ComplexShape.refl Unit) where
  X _ := selectedIdentifiedPairModule R a s
  d _ _ := selectedPairDifferential R G a b s hb twisted
  shape i j h := by cases i; cases j; exact False.elim (h rfl)
  d_comp_d' _ _ _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact Subtype.ext (identifiedPairDifferential_sq G R a b s hb twisted c.val)

/-- The corrected inclusion is an R[U]-linear native chain map. -/
noncomputable def selectedQuotientToConeHom (G : GridDiagram n) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    selectedIdentifiedComplex R G a (insert b s) ⟶ selectedPairComplex R G a b s hb true where
  f _ := ModuleCat.ofHom {
    toFun c := ⟨identifiedQuotientToCone G R a b s c.val,
      identifiedQuotientToCone_mem G R a b hab s hb c.property⟩
    map_add' c d := Subtype.ext (map_add _ c.val d.val)
    map_smul' p c := Subtype.ext (identifiedQuotientToCone_selected_smul R G a b hab s p c.val) }
  comm' _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact Subtype.ext (identifiedQuotientToCone_differential G R a b hab s hb c.val)

/-- The coefficient projection is an R[U]-linear native chain map. -/
noncomputable def selectedConeToQuotientHom (G : GridDiagram n) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    selectedPairComplex R G a b s hb true ⟶ selectedIdentifiedComplex R G a (insert b s) where
  f _ := ModuleCat.ofHom {
    toFun c := ⟨identifiedConeToQuotient R a b c.val,
      identifiedConeToQuotient_mem R a b s c.property⟩
    map_add' c d := Subtype.ext (map_add _ c.val d.val)
    map_smul' p c := Subtype.ext (identifiedConeToQuotient_selected_smul R a b p c.val) }
  comm' _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact Subtype.ext (identifiedConeToQuotient_differential G R a b hab s hb c.val).symm

/-- The quotient-side composition is the identity over R[U]. -/
theorem selectedQuotientToConeHom_comp (G : GridDiagram n) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    selectedQuotientToConeHom R G a b hab s hb ≫ selectedConeToQuotientHom R G a b hab s hb =
      𝟙 (selectedIdentifiedComplex R G a (insert b s)) := by
  ext i : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact Subtype.ext (identifiedConeToQuotient_quotientToCone G R a b s c.property)

/-- The divided inverse homotopy has polynomial-linear components. -/
noncomputable def selectedQuotientConeHomotopy (G : GridDiagram n) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    Homotopy (selectedConeToQuotientHom R G a b hab s hb ≫
      selectedQuotientToConeHom R G a b hab s hb)
        (𝟙 (selectedPairComplex R G a b s hb true)) where
  hom _ _ := ModuleCat.ofHom {
    toFun c := ⟨variableQuotientConeHomotopy R a b c.val,
      identifiedQuotientConeHomotopy_mem R a b hab s hb c.property⟩
    map_add' c d := Subtype.ext (map_add _ c.val d.val)
    map_smul' p c := Subtype.ext (variableQuotientConeHomotopy_selected_smul R a b hab p c.val) }
  zero i j h := by cases i; cases j; exact False.elim (h rfl)
  comm i := by
    cases i
    rw [dNext_eq _ (show (ComplexShape.refl Unit).Rel () () from rfl),
      prevD_eq _ (show (ComplexShape.refl Unit).Rel () () from rfl)]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact Subtype.ext (identifiedQuotientCone_homotopy_rearranged G R a b hab s hb c.val)

/-- The total quotient-cone equivalence, with all maps and homotopies R[U]-linear. -/
noncomputable def selectedQuotientConeEquiv (G : GridDiagram n) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    HomotopyEquiv (selectedIdentifiedComplex R G a (insert b s))
      (selectedPairComplex R G a b s hb true) where
  hom := selectedQuotientToConeHom R G a b hab s hb
  inv := selectedConeToQuotientHom R G a b hab s hb
  homotopyHomInvId := Homotopy.ofEq (selectedQuotientToConeHom_comp R G a b hab s hb)
  homotopyInvHomId := selectedQuotientConeHomotopy R G a b hab s hb

/-- The X-marking cone shear is an R[U]-linear involution. -/
noncomputable def selectedConeShearEquiv (G : GridDiagram n) (hG : G.IsKnot)
    (a b : Fin n) (s : Finset (Fin n)) :
    selectedIdentifiedPairModule R a s ≃ₗ[Polynomial R] selectedIdentifiedPairModule R a s where
  toFun c := ⟨identifiedConeShear G R hG a b s c.val,
    identifiedConeShear_mem G R hG a b s c.property⟩
  invFun c := ⟨identifiedConeShear G R hG a b s c.val,
    identifiedConeShear_mem G R hG a b s c.property⟩
  left_inv c := Subtype.ext (identifiedConeShear_involutive G R hG a b s c.val)
  right_inv c := Subtype.ext (identifiedConeShear_involutive G R hG a b s c.val)
  map_add' c d := Subtype.ext (map_add _ c.val d.val)
  map_smul' p c := Subtype.ext (identifiedConeShear_selected_smul R G hG a b s p c.val)

/-- The total relation cone splits over the retained polynomial ring. -/
noncomputable def selectedConeSplitIso (G : GridDiagram n) (hG : G.IsKnot)
    (a b : Fin n) (s : Finset (Fin n)) (hb : b ∉ s) :
    selectedPairComplex R G a b s hb true ≅ selectedPairComplex R G a b s hb false :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (selectedConeShearEquiv R G hG a b s).toModuleIso) (by
      intro _ _ _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact Subtype.ext (identifiedConeShear_differential G R hG a b s hb c.property).symm)

/-- One actual variable identification contributes a two-copy factor over R[U]. -/
noncomputable def selectedVariableNormalizationEquiv (G : GridDiagram n) (hG : G.IsKnot)
    (a b : Fin n) (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    HomotopyEquiv (selectedIdentifiedComplex R G a (insert b s))
      (selectedPairComplex R G a b s hb false) :=
  (selectedQuotientConeEquiv R G a b hab s hb).trans
    (.ofIso (selectedConeSplitIso R G hG a b s hb))

end OnLeConjecture.KnotFloer.GridFull

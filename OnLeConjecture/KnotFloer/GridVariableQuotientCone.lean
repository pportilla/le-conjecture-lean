/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridVariableDivision

/-!
# The variable quotient and its concrete cone comparison

Division by `V_a + V_b` supplies canonical representatives for the quotient
of the grid-chain module. Its differential is obtained by applying the full
rectangle differential and then taking the representative. The comparison
with the cone includes the correction term given by division of the full
differential. Thus the construction allows the differential to depend on
both variables.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

private theorem chain_add_self (c : GridChainMinus R n) : c + c = 0 := by
  apply Finsupp.ext
  intro x
  exact CharTwo.add_self_eq_zero _

/-- Multiplication by the relation, regarded as a map over the coefficient ring. -/
noncomputable def variableRelationAction (a b : Fin n) :
    GridChainMinus R n →ₗ[R] GridChainMinus R n :=
  ((X a + X b : MvPolynomial (Fin n) R) •
    (LinearMap.id : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R]
      GridChainMinus R n)).restrictScalars R

/-- The representative projection associated to the explicit two-variable division. -/
noncomputable def variableQuotientProjection (a b : Fin n) :
    GridChainMinus R n →ₗ[R] GridChainMinus R n :=
  LinearMap.id + (variableRelationAction R a b).comp (variableSumChainDivision R a b)

omit [CharP R 2] in
@[simp]
theorem variableQuotientProjection_apply (a b : Fin n) (c : GridChainMinus R n) :
    variableQuotientProjection R a b c =
      c + (X a + X b : MvPolynomial (Fin n) R) • variableSumChainDivision R a b c := rfl

/-- Division of a canonical quotient representative vanishes. -/
theorem division_quotientProjection (a b : Fin n) (hab : a ≠ b) (c : GridChainMinus R n) :
    variableSumChainDivision R a b (variableQuotientProjection R a b c) = 0 := by
  rw [variableQuotientProjection_apply, map_add,
    variableSumChainDivision_relation_smul R a b hab, chain_add_self]

/-- The projection kills multiples of the relation. -/
theorem quotientProjection_relation_smul (a b : Fin n) (hab : a ≠ b)
    (c : GridChainMinus R n) :
    variableQuotientProjection R a b ((X a + X b : MvPolynomial (Fin n) R) • c) = 0 := by
  rw [variableQuotientProjection_apply, variableSumChainDivision_relation_smul R a b hab]
  exact chain_add_self R _

/-- A representative together with its divided multiple recovers the original chain. -/
theorem quotientProjection_add_relation_division (a b : Fin n) (c : GridChainMinus R n) :
    variableQuotientProjection R a b c +
      (X a + X b : MvPolynomial (Fin n) R) • variableSumChainDivision R a b c = c := by
  rw [variableQuotientProjection_apply, add_assoc, chain_add_self, add_zero]

/-- Canonical representatives are exactly the kernel of the explicit division. -/
noncomputable def variableQuotientRepresentatives (a b : Fin n) :
    Submodule R (GridChainMinus R n) := LinearMap.ker (variableSumChainDivision R a b)

omit [CharP R 2] in
/-- Projection fixes every chain whose division vanishes. -/
theorem quotientProjection_eq_self (a b : Fin n) {c : GridChainMinus R n}
    (hc : c ∈ variableQuotientRepresentatives R a b) :
    variableQuotientProjection R a b c = c := by
  change variableSumChainDivision R a b c = 0 at hc
  rw [variableQuotientProjection_apply, hc, smul_zero, add_zero]

/-- Projection into the specified representative submodule. -/
noncomputable def variableQuotientProjectionToRep (a b : Fin n) (hab : a ≠ b) :
    GridChainMinus R n →ₗ[R] variableQuotientRepresentatives R a b :=
  (variableQuotientProjection R a b).codRestrict _ (division_quotientProjection R a b hab)

/-- Every representative is obtained by the quotient projection. -/
theorem variableQuotientProjectionToRep_surjective (a b : Fin n) (hab : a ≠ b) :
    Function.Surjective (variableQuotientProjectionToRep R a b hab) := by
  intro c
  exact ⟨c, Subtype.ext (quotientProjection_eq_self R a b c.property)⟩

/-- The kernel is the actual image of multiplication by the variable relation. -/
theorem ker_variableQuotientProjectionToRep (a b : Fin n) (hab : a ≠ b) :
    LinearMap.ker (variableQuotientProjectionToRep R a b hab) =
      LinearMap.range (variableRelationAction R a b) := by
  ext c
  constructor
  · intro hc
    have hzero : variableQuotientProjection R a b c = 0 := congrArg Subtype.val hc
    refine ⟨variableSumChainDivision R a b c, ?_⟩
    change (X a + X b : MvPolynomial (Fin n) R) • variableSumChainDivision R a b c = c
    have h := quotientProjection_add_relation_division R a b c
    simpa only [hzero, zero_add] using h
  · rintro ⟨d, rfl⟩
    exact Subtype.ext (quotientProjection_relation_smul R a b hab d)

/-- The representative submodule is canonically isomorphic to the genuine module quotient. -/
noncomputable def variableQuotientRepresentativesEquiv (a b : Fin n) (hab : a ≠ b) :
    (GridChainMinus R n ⧸ LinearMap.range (variableRelationAction R a b)) ≃ₗ[R]
      variableQuotientRepresentatives R a b :=
  let φ : (GridChainMinus R n ⧸ LinearMap.range (variableRelationAction R a b)) →ₗ[R]
      variableQuotientRepresentatives R a b :=
    (LinearMap.range (variableRelationAction R a b)).liftQ
      (R₂ := R) (M₂ := variableQuotientRepresentatives R a b) (τ₁₂ := RingHom.id R)
      (variableQuotientProjectionToRep R a b hab) (by
        rw [ker_variableQuotientProjectionToRep R a b hab])
  { φ with
    invFun := fun c => Submodule.Quotient.mk (c : GridChainMinus R n)
    left_inv := by
      intro q
      refine Submodule.Quotient.induction_on _ q ?_
      intro c
      change (Submodule.Quotient.mk (variableQuotientProjection R a b c) :
        GridChainMinus R n ⧸ LinearMap.range (variableRelationAction R a b)) =
        Submodule.Quotient.mk c
      apply (Submodule.Quotient.eq _).mpr
      refine ⟨variableSumChainDivision R a b c, ?_⟩
      change (X a + X b : MvPolynomial (Fin n) R) • variableSumChainDivision R a b c =
        variableQuotientProjection R a b c - c
      rw [variableQuotientProjection_apply]
      abel
    right_inv := by
      intro c
      change variableQuotientProjectionToRep R a b hab c = c
      exact Subtype.ext (quotientProjection_eq_self R a b c.property) }

/-- Projecting the input before applying the differential does not change its quotient. -/
theorem quotientProjection_differential_projection (a b : Fin n) (hab : a ≠ b)
    (c : GridChainMinus R n) :
    variableQuotientProjection R a b
      (differential G R (variableQuotientProjection R a b c)) =
      variableQuotientProjection R a b (differential G R c) := by
  rw [variableQuotientProjection_apply R a b c, map_add, map_smul, map_add,
    quotientProjection_relation_smul R a b hab, add_zero]

/-- The divided correction for a projected chain includes the derivative of its division. -/
theorem division_differential_projection (a b : Fin n) (hab : a ≠ b)
    (c : GridChainMinus R n) :
    variableSumChainDivision R a b
      (differential G R (variableQuotientProjection R a b c)) =
      differential G R (variableSumChainDivision R a b c) +
        variableSumChainDivision R a b (differential G R c) := by
  rw [variableQuotientProjection_apply, map_add, map_smul, map_add,
    variableSumChainDivision_relation_smul R a b hab, add_comm]

/-- The quotient differential is the projected full rectangle differential. -/
noncomputable def variableQuotientDifferential (a b : Fin n) (hab : a ≠ b) :
    variableQuotientRepresentatives R a b →ₗ[R] variableQuotientRepresentatives R a b :=
  (variableQuotientProjectionToRep R a b hab).comp
    (((differential G R).restrictScalars R).comp (variableQuotientRepresentatives R a b).subtype)

/-- The quotient differential squares to zero for the full variable-dependent differential. -/
theorem variableQuotientDifferential_sq (a b : Fin n) (hab : a ≠ b)
    (c : variableQuotientRepresentatives R a b) :
    variableQuotientDifferential G R a b hab (variableQuotientDifferential G R a b hab c) = 0 := by
  apply Subtype.ext
  change variableQuotientProjection R a b
    (differential G R (variableQuotientProjection R a b (differential G R c))) = 0
  rw [quotientProjection_differential_projection G R a b hab, differential_sq_eq_zero, map_zero]

/-- The cone-to-quotient map sends its first component to the quotient representative. -/
noncomputable def variableConeToQuotient (a b : Fin n) (hab : a ≠ b) :
    VariableConeChains R n →ₗ[R] variableQuotientRepresentatives R a b :=
  (variableQuotientProjectionToRep R a b hab).comp (LinearMap.fst _ _ _)

/-- The quotient-to-cone map includes the divided differential as its second component. -/
noncomputable def variableQuotientToCone (a b : Fin n) :
    variableQuotientRepresentatives R a b →ₗ[R] VariableConeChains R n :=
  (variableQuotientRepresentatives R a b).subtype.prod
    ((variableSumChainDivision R a b).comp
      (((differential G R).restrictScalars R).comp
        (variableQuotientRepresentatives R a b).subtype))

/-- The cone projection commutes with the explicit differentials. -/
theorem variableConeToQuotient_differential (a b : Fin n) (hab : a ≠ b)
    (c : VariableConeChains R n) :
    variableConeToQuotient R a b hab (variableConeDifferential G R a b c) =
      variableQuotientDifferential G R a b hab (variableConeToQuotient R a b hab c) := by
  apply Subtype.ext
  change variableQuotientProjection R a b
    (differential G R c.1 + (X a + X b : MvPolynomial (Fin n) R) • c.2) =
      variableQuotientProjection R a b (differential G R (variableQuotientProjection R a b c.1))
  rw [map_add, quotientProjection_relation_smul R a b hab, add_zero,
    quotientProjection_differential_projection G R a b hab]

/-- The corrected inclusion commutes with the explicit differentials. -/
theorem variableQuotientToCone_differential (a b : Fin n) (hab : a ≠ b)
    (c : variableQuotientRepresentatives R a b) :
    variableConeDifferential G R a b (variableQuotientToCone G R a b c) =
      variableQuotientToCone G R a b (variableQuotientDifferential G R a b hab c) := by
  apply Prod.ext
  · rfl
  · change differential G R (variableSumChainDivision R a b (differential G R c)) =
      variableSumChainDivision R a b
        (differential G R (variableQuotientProjection R a b (differential G R c)))
    rw [division_differential_projection G R a b hab, differential_sq_eq_zero, map_zero, add_zero]

/-- Projecting the corrected inclusion is exactly the identity. -/
theorem variableConeToQuotient_quotientToCone (a b : Fin n) (hab : a ≠ b)
    (c : variableQuotientRepresentatives R a b) :
    variableConeToQuotient R a b hab (variableQuotientToCone G R a b c) = c :=
  Subtype.ext (quotientProjection_eq_self R a b c.property)

/-- The explicit contraction divides the first cone component into the second one. -/
noncomputable def variableQuotientConeHomotopy (a b : Fin n) :
    VariableConeChains R n →ₗ[R] VariableConeChains R n :=
  (0 : VariableConeChains R n →ₗ[R] GridChainMinus R n).prod
    ((variableSumChainDivision R a b).comp (LinearMap.fst _ _ _))

/-- The corrected inclusion and projection compose to the identity up to explicit homotopy. -/
theorem variableQuotientCone_homotopy (a b : Fin n) (hab : a ≠ b) (c : VariableConeChains R n) :
    variableQuotientToCone G R a b (variableConeToQuotient R a b hab c) +
      variableConeDifferential G R a b (variableQuotientConeHomotopy R a b c) +
      variableQuotientConeHomotopy R a b (variableConeDifferential G R a b c) = c := by
  apply Prod.ext
  · change variableQuotientProjection R a b c.1 +
      (differential G R 0 + (X a + X b : MvPolynomial (Fin n) R) •
        variableSumChainDivision R a b c.1) + 0 = c.1
    rw [map_zero, zero_add, add_zero, quotientProjection_add_relation_division]
  · change variableSumChainDivision R a b
      (differential G R (variableQuotientProjection R a b c.1)) +
      differential G R (variableSumChainDivision R a b c.1) +
      variableSumChainDivision R a b
        (differential G R c.1 + (X a + X b : MvPolynomial (Fin n) R) • c.2) = c.2
    rw [division_differential_projection G R a b hab, map_add,
      variableSumChainDivision_relation_smul R a b hab]
    have hh (x y z : GridChainMinus R n) : (x + y) + x + (y + z) = z := by
      calc
        _ = (x + x) + (y + y) + z := by abel
        _ = z := by rw [chain_add_self, chain_add_self, zero_add, zero_add]
    exact hh _ _ _

omit [CharP R 2] in
/-- Multiplication by either O variable lowers Maslov degree by two. -/
theorem variableRelationAction_mem_maslovPiece (a b : Fin n) {m : ℤ}
    {c : GridChainMinus R n} (hc : c ∈ maslovPiece G R m) :
    variableRelationAction R a b c ∈ maslovPiece G R (m - 2) := by
  have h (i : Fin n) : (X i : MvPolynomial (Fin n) R) • c ∈ maslovPiece G R (m - 2) := by
    simpa [X, exponentSize] using
      monomial_smul_mem_maslovPiece G (Finsupp.single i 1) (1 : R) hc
  change (X a + X b : MvPolynomial (Fin n) R) • c ∈ _
  rw [add_smul]
  exact Submodule.add_mem _ (h a) (h b)

omit [CharP R 2] in
/-- Quotient representatives retain the Maslov degree of the original chain. -/
theorem quotientProjection_mem_maslovPiece (a b : Fin n) {m : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ maslovPiece G R m) : variableQuotientProjection R a b c ∈ maslovPiece G R m := by
  refine Submodule.add_mem _ hc ?_
  have h := variableRelationAction_mem_maslovPiece G R a b
    (variableSumChainDivision_mem_maslovPiece R G a b hc)
  simpa only [add_sub_cancel_right, LinearMap.comp_apply] using h

omit [CharP R 2] in
/-- Projection to the variable quotient preserves both total-exponent filtration bounds. -/
theorem quotientProjection_mem_bifiltrationLevel (a b : Fin n) {u v : ℝ}
    {c : GridChainMinus R n} (hc : c ∈ bifiltrationLevel G R u v) :
    variableQuotientProjection R a b c ∈ bifiltrationLevel G R u v := by
  have hd := variableSumChainDivision_mem_bifiltrationLevel R G a b hc
  rw [variableQuotientProjection_apply, add_smul]
  refine Submodule.add_mem _ hc (Submodule.add_mem _ ?_ ?_)
  · simpa only [add_sub_cancel_right] using X_smul_mem_bifiltrationLevel G R a _ hd
  · simpa only [add_sub_cancel_right] using X_smul_mem_bifiltrationLevel G R b _ hd

omit [CharP R 2] in
/-- The quotient inclusion has Maslov degree zero with the cone's specified shift. -/
theorem quotientToCone_mem_maslovPiece (a b : Fin n) {m : ℤ}
    (c : variableQuotientRepresentatives R a b)
    (hc : (c : GridChainMinus R n) ∈ maslovPiece G R m) :
    variableQuotientToCone G R a b c ∈ variableConeMaslovPiece G R m := by
  refine ⟨hc, ?_⟩
  have h := variableSumChainDivision_mem_maslovPiece R G a b
    (differential_mem_maslovPiece G hc)
  change variableSumChainDivision R a b (differential G R c) ∈ maslovPiece G R (m + 1)
  simpa only [show m - 1 + 2 = m + 1 by omega] using h

omit [CharP R 2] in
/-- The quotient inclusion preserves Alexander and has first-coordinate shift at most one. -/
theorem quotientToCone_mem_bifiltrationLevel (a b : Fin n) {u v : ℝ}
    (c : variableQuotientRepresentatives R a b)
    (hc : (c : GridChainMinus R n) ∈ bifiltrationLevel G R u v) :
    variableQuotientToCone G R a b c ∈ variableConeBifiltrationLevel G R (u + 1) v := by
  refine ⟨bifiltrationLevel_mono G R (by linarith) le_rfl hc, ?_⟩
  exact variableSumChainDivision_mem_bifiltrationLevel R G a b
    (differential_mem_bifiltrationLevel G R u v c hc)

omit [CharP R 2] in
/-- The cone contraction raises Maslov degree by one. -/
theorem quotientConeHomotopy_mem_maslovPiece (a b : Fin n) {m : ℤ}
    {c : VariableConeChains R n} (hc : c ∈ variableConeMaslovPiece G R m) :
    variableQuotientConeHomotopy R a b c ∈ variableConeMaslovPiece G R (m + 1) := by
  refine ⟨Submodule.zero_mem _, ?_⟩
  have h := variableSumChainDivision_mem_maslovPiece R G a b hc.1
  change variableSumChainDivision R a b c.1 ∈ maslovPiece G R (m + 1 + 1)
  simpa only [show m + 1 + 1 = m + 2 by omega] using h

omit [CharP R 2] in
/-- The cone contraction preserves Alexander and has first-coordinate shift at most one. -/
theorem quotientConeHomotopy_mem_bifiltrationLevel (a b : Fin n) {u v : ℝ}
    {c : VariableConeChains R n} (hc : c ∈ variableConeBifiltrationLevel G R u v) :
    variableQuotientConeHomotopy R a b c ∈ variableConeBifiltrationLevel G R (u + 1) v :=
  ⟨Submodule.zero_mem _, variableSumChainDivision_mem_bifiltrationLevel R G a b hc.1⟩

end OnLeConjecture.KnotFloer.GridFull

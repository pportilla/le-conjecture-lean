/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPartialVariableDivision

/-!
# The next cone comparison after earlier variable identifications

The maps are the concrete quotient projection, divided differential, and
X-marking shear. Every identity uses the full grid differential after the
specified finite set of earlier coefficient identifications.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

private theorem chain_add_self (c : GridChainMinus R n) : c + c = 0 := by
  apply Finsupp.ext
  intro x
  exact CharTwo.add_self_eq_zero _

/-- Both components of a variable cone satisfy the earlier coefficient identifications. -/
noncomputable def identifiedConeChains (a : Fin n) (s : Finset (Fin n)) :
    Submodule R (VariableConeChains R n) :=
  (identifiedChains R a s).prod (identifiedChains R a s)

/-- The next variable cone differential after the earlier identifications. -/
noncomputable def identifiedConeDifferential (a b : Fin n) (s : Finset (Fin n)) :
    VariableConeChains R n →ₗ[R] VariableConeChains R n :=
  ((identifiedDifferential R G a s).comp (.fst _ _ _) +
    (variableRelationAction R a b).comp (.snd _ _ _)).prod
      ((identifiedDifferential R G a s).comp (.snd _ _ _))

/-- The direct-sum differential after the earlier identifications. -/
noncomputable def identifiedSplitDifferential (a : Fin n) (s : Finset (Fin n)) :
    VariableConeChains R n →ₗ[R] VariableConeChains R n :=
  (identifiedDifferential R G a s).prodMap (identifiedDifferential R G a s)

/-- The corrected inclusion uses division of the partially identified differential. -/
noncomputable def identifiedQuotientToCone (a b : Fin n) (s : Finset (Fin n)) :
    GridChainMinus R n →ₗ[R] VariableConeChains R n :=
  LinearMap.id.prod
    ((variableSumChainDivision R a b).comp (identifiedDifferential R G a s))

/-- The cone-to-quotient map applies the next coefficient identification. -/
noncomputable def identifiedConeToQuotient (a b : Fin n) :
    VariableConeChains R n →ₗ[R] GridChainMinus R n :=
  (variableQuotientProjection R a b).comp (.fst _ _ _)

/-- The projected geometric X-marking homotopy defines the next shear. -/
noncomputable def identifiedConeShear (hG : G.IsKnot) (a b : Fin n)
    (s : Finset (Fin n)) : VariableConeChains R n →ₗ[R] VariableConeChains R n :=
  (LinearMap.fst _ _ _ + (identifiedVariableHomotopy R G hG a b s).comp
    (.snd _ _ _)).prod (.snd _ _ _)

/-- Both partially identified cone differentials square to zero. -/
theorem identifiedConeDifferential_sq (a b : Fin n) (s : Finset (Fin n))
    (hb : b ∉ s) (c : VariableConeChains R n) :
    identifiedConeDifferential G R a b s (identifiedConeDifferential G R a b s c) = 0 := by
  apply Prod.ext
  · change identifiedDifferential R G a s (identifiedDifferential R G a s c.1 +
      (X a + X b : MvPolynomial (Fin n) R) • c.2) +
      (X a + X b : MvPolynomial (Fin n) R) • identifiedDifferential R G a s c.2 = 0
    rw [map_add, identifiedDifferential_relation_smul R G a b s hb,
      identifiedDifferential_sq, zero_add, chain_add_self]
  · exact identifiedDifferential_sq R G a s c.2

/-- The next quotient differential is projection of the earlier identified differential. -/
theorem identifiedDifferential_insert (a b : Fin n) (s : Finset (Fin n))
    (c : GridChainMinus R n) :
    identifiedDifferential R G a (insert b s) c =
      variableQuotientProjection R a b (identifiedDifferential R G a s c) :=
  (quotientProjection_identifyVariablesChain_insert R a b s (differential G R c)).symm

/-- Projecting an input before the earlier differential gives the same next quotient. -/
theorem quotientProjection_identifiedDifferential_projection (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) (c : GridChainMinus R n) :
    variableQuotientProjection R a b
      (identifiedDifferential R G a s (variableQuotientProjection R a b c)) =
      variableQuotientProjection R a b (identifiedDifferential R G a s c) := by
  rw [variableQuotientProjection_apply R a b c, map_add,
    identifiedDifferential_relation_smul R G a b s hb, map_add,
    quotientProjection_relation_smul R a b hab, add_zero]

/-- The next cone projection commutes with the identified differentials. -/
theorem identifiedConeToQuotient_differential (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) (c : VariableConeChains R n) :
    identifiedConeToQuotient R a b (identifiedConeDifferential G R a b s c) =
      identifiedDifferential R G a (insert b s) (identifiedConeToQuotient R a b c) := by
  change variableQuotientProjection R a b (identifiedDifferential R G a s c.1 +
    (X a + X b : MvPolynomial (Fin n) R) • c.2) =
      identifiedDifferential R G a (insert b s) (variableQuotientProjection R a b c.1)
  rw [identifiedDifferential_insert, map_add,
    quotientProjection_relation_smul R a b hab, add_zero,
    quotientProjection_identifiedDifferential_projection G R a b hab s hb]

/-- The divided inclusion commutes with the identified differentials. -/
theorem identifiedQuotientToCone_differential (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) (c : GridChainMinus R n) :
    identifiedConeDifferential G R a b s (identifiedQuotientToCone G R a b s c) =
      identifiedQuotientToCone G R a b s (identifiedDifferential R G a (insert b s) c) := by
  apply Prod.ext
  · exact (identifiedDifferential_insert G R a b s c).symm
  · change identifiedDifferential R G a s
      (variableSumChainDivision R a b (identifiedDifferential R G a s c)) =
        variableSumChainDivision R a b
          (identifiedDifferential R G a s (identifiedDifferential R G a (insert b s) c))
    rw [identifiedDifferential_insert, division_identifiedDifferential_projection R G a b hab s hb,
      identifiedDifferential_sq, map_zero, add_zero]

/-- On the enlarged identified module, projection after corrected inclusion is the identity. -/
theorem identifiedConeToQuotient_quotientToCone (a b : Fin n) (s : Finset (Fin n))
    {c : GridChainMinus R n} (hc : c ∈ identifiedChains R a (insert b s)) :
    identifiedConeToQuotient R a b (identifiedQuotientToCone G R a b s c) = c := by
  change variableQuotientProjection R a b c = c
  rw [variableQuotientProjection_eq_identifyVariablesChain]
  exact (mem_identifiedChains R a {b} c).mp
    (identifiedChains_antitone R a (by simp) hc)

/-- The same division contraction proves the next cone comparison after earlier eliminations. -/
theorem identifiedQuotientCone_homotopy (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) (c : VariableConeChains R n) :
    identifiedQuotientToCone G R a b s (identifiedConeToQuotient R a b c) +
      identifiedConeDifferential G R a b s (variableQuotientConeHomotopy R a b c) +
      variableQuotientConeHomotopy R a b (identifiedConeDifferential G R a b s c) = c := by
  apply Prod.ext
  · change variableQuotientProjection R a b c.1 +
      (identifiedDifferential R G a s 0 + (X a + X b : MvPolynomial (Fin n) R) •
        variableSumChainDivision R a b c.1) + 0 = c.1
    rw [map_zero, zero_add, add_zero, quotientProjection_add_relation_division]
  · change variableSumChainDivision R a b
      (identifiedDifferential R G a s (variableQuotientProjection R a b c.1)) +
      identifiedDifferential R G a s (variableSumChainDivision R a b c.1) +
      variableSumChainDivision R a b
        (identifiedDifferential R G a s c.1 +
          (X a + X b : MvPolynomial (Fin n) R) • c.2) = c.2
    rw [division_identifiedDifferential_projection R G a b hab s hb, map_add,
      variableSumChainDivision_relation_smul R a b hab]
    have hh (x y z : GridChainMinus R n) : (x + y) + x + (y + z) = z := by
      calc
        _ = (x + x) + (y + y) + z := by abel
        _ = z := by rw [chain_add_self, chain_add_self, zero_add, zero_add]
    exact hh _ _ _

/-- The projected geometric shear remains an involution. -/
theorem identifiedConeShear_involutive (hG : G.IsKnot) (a b : Fin n)
    (s : Finset (Fin n)) : Function.Involutive (identifiedConeShear G R hG a b s) := by
  intro c
  apply Prod.ext
  · change (c.1 + identifiedVariableHomotopy R G hG a b s c.2) +
      identifiedVariableHomotopy R G hG a b s c.2 = c.1
    rw [add_assoc, chain_add_self, add_zero]
  · rfl

/-- The geometric shear splits the next variable cone on the partially identified chains. -/
theorem identifiedConeShear_differential (hG : G.IsKnot) (a b : Fin n)
    (s : Finset (Fin n)) (hb : b ∉ s) {c : VariableConeChains R n}
    (hc : c ∈ identifiedConeChains R a s) :
    identifiedConeShear G R hG a b s (identifiedConeDifferential G R a b s c) =
      identifiedSplitDifferential G R a s (identifiedConeShear G R hG a b s c) := by
  have h := identifiedDifferential_variableHomotopy R G hG a b s hb hc.2
  apply Prod.ext
  · change identifiedDifferential R G a s c.1 +
      (X a + X b : MvPolynomial (Fin n) R) • c.2 +
      identifiedVariableHomotopy R G hG a b s (identifiedDifferential R G a s c.2) =
      identifiedDifferential R G a s (c.1 + identifiedVariableHomotopy R G hG a b s c.2)
    rw [map_add, ← h, add_assoc, add_assoc, chain_add_self, add_zero]
  · rfl

/-- The divided inclusion lands in the earlier identified cone module. -/
theorem identifiedQuotientToCone_mem (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) {c : GridChainMinus R n}
    (hc : c ∈ identifiedChains R a (insert b s)) :
    identifiedQuotientToCone G R a b s c ∈ identifiedConeChains R a s :=
  ⟨identifiedChains_antitone R a (Finset.subset_insert b s) hc,
    variableSumChainDivision_mem_identifiedChains R a b hab s hb
      (identifiedDifferential_mem_identifiedChains R G a s c)⟩

/-- The next projection lands in the enlarged identified module. -/
theorem identifiedConeToQuotient_mem (a b : Fin n) (s : Finset (Fin n))
    {c : VariableConeChains R n} (hc : c ∈ identifiedConeChains R a s) :
    identifiedConeToQuotient R a b c ∈ identifiedChains R a (insert b s) :=
  quotientProjection_mem_identifiedChains_insert R a b s hc.1

/-- The division contraction preserves all earlier identifications. -/
theorem identifiedQuotientConeHomotopy_mem (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) {c : VariableConeChains R n}
    (hc : c ∈ identifiedConeChains R a s) :
    variableQuotientConeHomotopy R a b c ∈ identifiedConeChains R a s :=
  ⟨Submodule.zero_mem _, variableSumChainDivision_mem_identifiedChains R a b hab s hb hc.1⟩

omit [CharP R 2] in
/-- The geometric shear preserves all earlier coefficient identifications. -/
theorem identifiedConeShear_mem (hG : G.IsKnot) (a b : Fin n) (s : Finset (Fin n))
    {c : VariableConeChains R n} (hc : c ∈ identifiedConeChains R a s) :
    identifiedConeShear G R hG a b s c ∈ identifiedConeChains R a s :=
  ⟨Submodule.add_mem _ hc.1
    (identifyVariablesChain_mem_identifiedChains R a s _), hc.2⟩

end OnLeConjecture.KnotFloer.GridFull

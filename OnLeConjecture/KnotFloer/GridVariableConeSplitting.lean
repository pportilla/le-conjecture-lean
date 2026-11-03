/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridVariableFilteredHomotopy

/-!
# Splitting the cone of two O-variable actions

For a knot grid, the concrete X-marking homotopy splits the cone differential
`(x, y) ↦ (Dx + (V_a + V_b)y, Dy)` by the involution `(x, y) ↦ (x + Hy, y)`.
The pair in degree `m` consists of chains of degrees `m` and `m + 1`. Its
Alexander bounds are `v` and `v + 1`. Thus the second summand has the shifts
`(M, A) = (-1, -1)` occurring in the factor W of Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Lemma 14.1.11.

The cone differential and its isomorphism are proved here from the actual grid
rectangle maps. The comparison with a quotient by `V_a + V_b`, and the iteration
over all O variables, are separate assertions.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The two grid-chain summands used in a variable-action cone. -/
abbrev VariableConeChains (n : ℕ) := GridChainMinus R n × GridChainMinus R n

/-- The direct-sum differential on the two grid-chain summands. -/
noncomputable def variableSplitDifferential :
    VariableConeChains R n →ₗ[MvPolynomial (Fin n) R] VariableConeChains R n :=
  (differential G R).prodMap (differential G R)

/-- The cone differential of multiplication by the sum of the two O variables. -/
noncomputable def variableConeDifferential (a b : Fin n) :
    VariableConeChains R n →ₗ[MvPolynomial (Fin n) R] VariableConeChains R n :=
  ((differential G R).comp (.fst _ _ _) +
    (MvPolynomial.X a + MvPolynomial.X b : MvPolynomial (Fin n) R) • .snd _ _ _).prod
      ((differential G R).comp (.snd _ _ _))

/-- The cone shear defined by the finite sum of X-marking derivatives. -/
noncomputable def variableConeShear (hG : G.IsKnot) (a b : Fin n) :
    VariableConeChains R n →ₗ[MvPolynomial (Fin n) R] VariableConeChains R n :=
  (LinearMap.fst _ _ _ + (knotVariableActionHomotopy G R hG a b).comp
    (.snd _ _ _)).prod (.snd _ _ _)

omit [CharP R 2] in
@[simp]
theorem variableConeShear_apply (hG : G.IsKnot) (a b : Fin n) (c : VariableConeChains R n) :
    variableConeShear G R hG a b c =
      (c.1 + knotVariableActionHomotopy G R hG a b c.2, c.2) := rfl

private theorem gridChain_add_self (c : GridChainMinus R n) : c + c = 0 := by
  apply Finsupp.ext
  intro x
  exact CharTwo.add_self_eq_zero _

/-- In characteristic two the explicit shear is its own inverse. -/
theorem variableConeShear_involutive (hG : G.IsKnot) (a b : Fin n) :
    Function.Involutive (variableConeShear G R hG a b) := by
  intro c
  apply Prod.ext
  · change (c.1 + knotVariableActionHomotopy G R hG a b c.2) +
      knotVariableActionHomotopy G R hG a b c.2 = c.1
    rw [add_assoc, gridChain_add_self, add_zero]
  · rfl

/-- The shear carries the variable-action cone differential to the direct-sum differential. -/
theorem variableConeShear_differential (hG : G.IsKnot) (a b : Fin n)
    (c : VariableConeChains R n) :
    variableConeShear G R hG a b (variableConeDifferential G R a b c) =
      variableSplitDifferential G R (variableConeShear G R hG a b c) := by
  have h := LinearMap.congr_fun (differential_knotVariableActionHomotopy G R hG a b) c.2
  change differential G R (knotVariableActionHomotopy G R hG a b c.2) +
    knotVariableActionHomotopy G R hG a b (differential G R c.2) =
      (MvPolynomial.X a + MvPolynomial.X b : MvPolynomial (Fin n) R) • c.2 at h
  apply Prod.ext
  · change differential G R c.1 +
      (MvPolynomial.X a + MvPolynomial.X b : MvPolynomial (Fin n) R) • c.2 +
      knotVariableActionHomotopy G R hG a b (differential G R c.2) =
      differential G R (c.1 + knotVariableActionHomotopy G R hG a b c.2)
    rw [map_add, ← h]
    simp only [add_assoc, gridChain_add_self, add_zero]
  · rfl

/-- The direct-sum differential squares to zero. -/
theorem variableSplitDifferential_sq (c : VariableConeChains R n) :
    variableSplitDifferential G R (variableSplitDifferential G R c) = 0 := by
  exact Prod.ext (differential_sq_eq_zero G R c.1) (differential_sq_eq_zero G R c.2)

/-- The variable-action cone differential squares to zero. -/
theorem variableConeDifferential_sq (a b : Fin n) (c : VariableConeChains R n) :
    variableConeDifferential G R a b (variableConeDifferential G R a b c) = 0 := by
  apply Prod.ext
  · change differential G R (differential G R c.1 +
      (MvPolynomial.X a + MvPolynomial.X b : MvPolynomial (Fin n) R) • c.2) +
      (MvPolynomial.X a + MvPolynomial.X b : MvPolynomial (Fin n) R) •
        differential G R c.2 = 0
    rw [map_add, map_smul, differential_sq_eq_zero, zero_add]
    exact gridChain_add_self R _
  · exact differential_sq_eq_zero G R c.2

/-- The explicit inverse linear equivalence splitting the variable-action cone. -/
noncomputable def variableConeShearEquiv (hG : G.IsKnot) (a b : Fin n) :
    VariableConeChains R n ≃ₗ[MvPolynomial (Fin n) R] VariableConeChains R n :=
  { variableConeShear G R hG a b with
    invFun := variableConeShear G R hG a b
    left_inv := variableConeShear_involutive G R hG a b
    right_inv := variableConeShear_involutive G R hG a b }

/-- The pair grading shifts the second copy by minus one in Maslov degree. -/
noncomputable def variableConeMaslovPiece (m : ℤ) : Submodule R (VariableConeChains R n) :=
  (maslovPiece G R m).prod (maslovPiece G R (m + 1))

/-- The pair filtration shifts the second copy by minus one in Alexander degree. -/
noncomputable def variableConeBifiltrationLevel (u v : ℝ) :
    Submodule (MvPolynomial (Fin n) R) (VariableConeChains R n) :=
  (bifiltrationLevel G R u v).prod (bifiltrationLevel G R u (v + 1))

omit [CharP R 2] in
/-- The cone shear preserves the specified Maslov degree. -/
theorem variableConeShear_mem_maslovPiece (hG : G.IsKnot) (a b : Fin n)
    {m : ℤ} {c : VariableConeChains R n} (hc : c ∈ variableConeMaslovPiece G R m) :
    variableConeShear G R hG a b c ∈ variableConeMaslovPiece G R m := by
  obtain ⟨h₁, h₂⟩ := hc
  refine ⟨Submodule.add_mem _ h₁ ?_, h₂⟩
  simpa using knotVariableActionHomotopy_mem_maslovPiece G R hG a b h₂

omit [CharP R 2] in
/-- The cone shear preserves both coordinates of the shifted pair filtration. -/
theorem variableConeShear_mem_bifiltrationLevel (hG : G.IsKnot) (a b : Fin n)
    {u v : ℝ} {c : VariableConeChains R n} (hc : c ∈ variableConeBifiltrationLevel G R u v) :
    variableConeShear G R hG a b c ∈ variableConeBifiltrationLevel G R u v := by
  obtain ⟨h₁, h₂⟩ := hc
  refine ⟨Submodule.add_mem _ h₁ ?_, h₂⟩
  simpa using knotVariableActionHomotopy_mem_bifiltrationLevel G R hG a b h₂

omit [CharP R 2] in
/-- The pair differential lowers the shifted Maslov degree by one. -/
theorem variableSplitDifferential_mem_maslovPiece {m : ℤ} {c : VariableConeChains R n}
    (hc : c ∈ variableConeMaslovPiece G R m) :
    variableSplitDifferential G R c ∈ variableConeMaslovPiece G R (m - 1) := by
  change differential G R c.1 ∈ maslovPiece G R (m - 1) ∧
    differential G R c.2 ∈ maslovPiece G R (m - 1 + 1)
  exact ⟨differential_mem_maslovPiece G hc.1,
    by simpa only [add_sub_cancel_right, sub_add_cancel] using differential_mem_maslovPiece G hc.2⟩

omit [CharP R 2] in
/-- The pair differential preserves the shifted filtration. -/
theorem variableSplitDifferential_mem_bifiltrationLevel {u v : ℝ} {c : VariableConeChains R n}
    (hc : c ∈ variableConeBifiltrationLevel G R u v) :
    variableSplitDifferential G R c ∈ variableConeBifiltrationLevel G R u v :=
  ⟨differential_mem_bifiltrationLevel G R _ _ _ hc.1,
    differential_mem_bifiltrationLevel G R _ _ _ hc.2⟩

/-- The explicit conjugation also proves the cone differential has degree minus one. -/
theorem variableConeDifferential_mem_maslovPiece (hG : G.IsKnot) (a b : Fin n)
    {m : ℤ} {c : VariableConeChains R n} (hc : c ∈ variableConeMaslovPiece G R m) :
    variableConeDifferential G R a b c ∈ variableConeMaslovPiece G R (m - 1) := by
  have h := variableConeShear_mem_maslovPiece G R hG a b
    (variableSplitDifferential_mem_maslovPiece G R
      (variableConeShear_mem_maslovPiece G R hG a b hc))
  rwa [← variableConeShear_differential,
    variableConeShear_involutive G R hG a b] at h

/-- The explicit conjugation proves the cone differential preserves both shifted bounds. -/
theorem variableConeDifferential_mem_bifiltrationLevel (hG : G.IsKnot) (a b : Fin n)
    {u v : ℝ} {c : VariableConeChains R n} (hc : c ∈ variableConeBifiltrationLevel G R u v) :
    variableConeDifferential G R a b c ∈ variableConeBifiltrationLevel G R u v := by
  have h := variableConeShear_mem_bifiltrationLevel G R hG a b
    (variableSplitDifferential_mem_bifiltrationLevel G R
      (variableConeShear_mem_bifiltrationLevel G R hG a b hc))
  rwa [← variableConeShear_differential,
    variableConeShear_involutive G R hG a b] at h

/-- The restricted shear is an involutive equivalence in every Maslov degree. -/
noncomputable def variableConeShearPieceEquiv (hG : G.IsKnot) (a b : Fin n) (m : ℤ) :
    variableConeMaslovPiece G R m ≃ₗ[R] variableConeMaslovPiece G R m :=
  { toLinearMap := ((variableConeShear G R hG a b).restrictScalars R).restrict
      fun _ hc => variableConeShear_mem_maslovPiece G R hG a b hc
    invFun := fun c => ⟨variableConeShear G R hG a b c,
      variableConeShear_mem_maslovPiece G R hG a b c.property⟩
    left_inv := fun c => Subtype.ext (variableConeShear_involutive G R hG a b c)
    right_inv := fun c => Subtype.ext (variableConeShear_involutive G R hG a b c) }

/-- The shifted pair differential, with or without the variable-action term. -/
noncomputable def variablePairDifferential (a b : Fin n) (twisted : Bool) :
    VariableConeChains R n →ₗ[MvPolynomial (Fin n) R] VariableConeChains R n :=
  if twisted then variableConeDifferential G R a b else variableSplitDifferential G R

/-- Both explicit pair differentials preserve the same Maslov grading. -/
theorem variablePairDifferential_mem_maslovPiece (hG : G.IsKnot) (a b : Fin n)
    (twisted : Bool) {m : ℤ} {c : VariableConeChains R n}
    (hc : c ∈ variableConeMaslovPiece G R m) :
    variablePairDifferential G R a b twisted c ∈ variableConeMaslovPiece G R (m - 1) := by
  cases twisted
  · exact variableSplitDifferential_mem_maslovPiece G R hc
  · exact variableConeDifferential_mem_maslovPiece G R hG a b hc

/-- Both explicit pair differentials square to zero. -/
theorem variablePairDifferential_sq (a b : Fin n) (twisted : Bool)
    (c : VariableConeChains R n) :
    variablePairDifferential G R a b twisted
      (variablePairDifferential G R a b twisted c) = 0 := by
  cases twisted
  · exact variableSplitDifferential_sq G R c
  · exact variableConeDifferential_sq G R a b c

/-- The pair differential restricted to consecutive Maslov degrees. -/
noncomputable def variablePairGradedDifferential (hG : G.IsKnot) (a b : Fin n)
    (twisted : Bool) (m : ℤ) :
    variableConeMaslovPiece G R (m + 1) →ₗ[R] variableConeMaslovPiece G R m :=
  ((variablePairDifferential G R a b twisted).restrictScalars R).restrict fun _ hc => by
    simpa using
      variablePairDifferential_mem_maslovPiece G R hG a b twisted hc

/-- Consecutive restricted pair differentials compose to zero. -/
theorem variablePairGradedDifferential_comp_eq_zero (hG : G.IsKnot) (a b : Fin n)
    (twisted : Bool) (m : ℤ) :
    (variablePairGradedDifferential G R hG a b twisted m).comp
      (variablePairGradedDifferential G R hG a b twisted (m + 1)) = 0 := by
  ext c : 1
  exact Subtype.ext (variablePairDifferential_sq G R a b twisted c)

/-- The integer-graded variable-action cone or its split counterpart. -/
noncomputable def variablePairComplex (hG : G.IsKnot) (a b : Fin n) (twisted : Bool) :
    ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (variableConeMaslovPiece G R m))
    (fun m => ModuleCat.ofHom (variablePairGradedDifferential G R hG a b twisted m))
    (fun m => by rw [← ModuleCat.ofHom_comp,
      variablePairGradedDifferential_comp_eq_zero, ModuleCat.ofHom_zero])

/-- The native pair-complex differential is the restricted explicit differential. -/
theorem variablePairComplex_d (hG : G.IsKnot) (a b : Fin n) (twisted : Bool) (m : ℤ) :
    (variablePairComplex G R hG a b twisted).d (m + 1) m =
      ModuleCat.ofHom (variablePairGradedDifferential G R hG a b twisted m) := by
  simp only [variablePairComplex, ChainComplex.of_d]

/-- The concrete variable-action cone is isomorphic to the two shifted grid summands. -/
noncomputable def variableConeSplitIso (hG : G.IsKnot) (a b : Fin n) :
    variablePairComplex G R hG a b true ≅ variablePairComplex G R hG a b false :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m => (variableConeShearPieceEquiv G R hG a b m).toModuleIso) (by
      intro i j hij
      rw [ComplexShape.down_Rel] at hij
      subst i
      rw [variablePairComplex_d, variablePairComplex_d]
      ext c : 2
      exact Subtype.ext (variableConeShear_differential G R hG a b
        ((show variableConeMaslovPiece G R (j + 1) from c) : VariableConeChains R n)).symm)

/-- The shifted filtration on either of the native pair complexes. -/
noncomputable def variablePairBifiltration (hG : G.IsKnot) (a b : Fin n) (twisted : Bool) :
    Bifiltration (variablePairComplex G R hG a b twisted) where
  level u v m := ((variableConeBifiltrationLevel G R u v).restrictScalars R).comap
    (variableConeMaslovPiece G R m).subtype
  mono m u v u' v' hu hv := by
    apply Submodule.comap_mono
    intro c hc
    exact ⟨bifiltrationLevel_mono G R hu hv hc.1,
      bifiltrationLevel_mono G R hu (by linarith : v + 1 ≤ v' + 1) hc.2⟩
  differential_mem u v i j c hc := by
    by_cases h : j + 1 = i
    · subst i
      rw [variablePairComplex_d]
      change variablePairDifferential G R a b twisted
        ((show variableConeMaslovPiece G R (j + 1) from c) : VariableConeChains R n) ∈
          variableConeBifiltrationLevel G R u v
      cases twisted
      · exact variableSplitDifferential_mem_bifiltrationLevel G R hc
      · exact variableConeDifferential_mem_bifiltrationLevel G R hG a b hc
    · rw [(variablePairComplex G R hG a b twisted).shape i j h]
      exact Submodule.zero_mem _

/-- The concrete native cone-splitting isomorphism preserves both filtrations. -/
theorem variableConeSplitIso_hom_preserves (hG : G.IsKnot) (a b : Fin n) :
    (variablePairBifiltration G R hG a b true).Preserves
      (variablePairBifiltration G R hG a b false) (variableConeSplitIso G R hG a b).hom := by
  intro u v m c hc
  exact variableConeShear_mem_bifiltrationLevel G R hG a b hc

/-- Its explicitly equal shear inverse also preserves both filtrations. -/
theorem variableConeSplitIso_inv_preserves (hG : G.IsKnot) (a b : Fin n) :
    (variablePairBifiltration G R hG a b false).Preserves
      (variablePairBifiltration G R hG a b true) (variableConeSplitIso G R hG a b).inv := by
  intro u v m c hc
  exact variableConeShear_mem_bifiltrationLevel G R hG a b hc

end OnLeConjecture.KnotFloer.GridFull

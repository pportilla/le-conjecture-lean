/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridVariableIdentification

/-!
# The full grid differential after partial variable identification

Finite coefficient identifications preserve the actual rectangle differential's
square-zero identity and the geometric X-marking homotopies. The construction uses
coefficient substitution in the existing maps, including their variable dependence.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti MvPolynomial CategoryTheory

variable {n : ℕ} (R : Type*) [CommRing R]

/-- Coefficient identification is semilinear for the same polynomial substitution. -/
theorem identifyVariablesChain_smul (a : Fin n) (s : Finset (Fin n))
    (p : MvPolynomial (Fin n) R) (c : GridChainMinus R n) :
    identifyVariablesChain R a s (p • c) =
      identifyVariables R a s p • identifyVariablesChain R a s c := by
  apply Finsupp.ext
  intro x
  change identifyVariables R a s (p * c x) =
    identifyVariables R a s p * identifyVariables R a s (c x)
  exact map_mul _ _ _

@[simp]
theorem identifyVariablesChain_single (a : Fin n) (s : Finset (Fin n))
    (x : GridState n) (p : MvPolynomial (Fin n) R) :
    identifyVariablesChain R a s (Finsupp.single x p) =
      Finsupp.single x (identifyVariables R a s p) := by
  exact Finsupp.mapRange_single (hf := (identifyVariables R a s).toLinearMap.map_zero)

/-- Reapplying a finite coefficient identification has no effect. -/
theorem identifyVariablesChain_idempotent (a : Fin n) (s : Finset (Fin n))
    (c : GridChainMinus R n) :
    identifyVariablesChain R a s (identifyVariablesChain R a s c) =
      identifyVariablesChain R a s c := by
  apply Finsupp.ext
  intro x
  exact identifyVariables_idempotent R a s (c x)

/-- Polynomial-linear maps descend through the concrete coefficient projection. -/
theorem identifyVariablesChain_linear_projection (a : Fin n) (s : Finset (Fin n))
    (T : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)
    (c : GridChainMinus R n) :
    identifyVariablesChain R a s (T (identifyVariablesChain R a s c)) =
      identifyVariablesChain R a s (T c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x p =>
    rw [identifyVariablesChain_single]
    have h (q : MvPolynomial (Fin n) R) : Finsupp.single x q = q • Finsupp.single x 1 := by
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h, h p]
    simp only [T.map_smul, identifyVariablesChain_smul, identifyVariables_idempotent]

/-- Every surviving substituted monomial has an input monomial of the same total degree. -/
theorem exists_support_identifyVariables (a : Fin n) (s : Finset (Fin n))
    (p : MvPolynomial (Fin n) R) {f : Fin n →₀ ℕ}
    (hf : f ∈ (identifyVariables R a s p).support) :
    ∃ e ∈ p.support, exponentSize e = exponentSize f := by
  classical
  have hp : identifyVariables R a s p =
      ∑ e ∈ p.support, identifyVariables R a s (monomial e (p.coeff e)) := by
    conv_lhs => rw [as_sum p]
    rw [map_sum]
  rw [hp] at hf
  obtain ⟨e, he, hef⟩ := Finset.mem_biUnion.mp (support_sum hf)
  have hm : (monomial e (p.coeff e)).IsHomogeneous (exponentSize e) :=
    isHomogeneous_monomial _ (Finsupp.degree_eq_sum e)
  have hh := hm.rename_isHomogeneous (f := fun i => if i ∈ s then a else i)
  exact ⟨e, he, (hh.degree_eq_sum_deg_support hef).trans (Finsupp.degree_eq_sum f)⟩

/-- Partial variable identification preserves Maslov degree. -/
theorem identifyVariablesChain_mem_maslovPiece (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) {m : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ maslovPiece G R m) :
    identifyVariablesChain R a s c ∈ maslovPiece G R m := by
  rw [mem_maslovPiece] at hc ⊢
  intro x f hf
  obtain ⟨e, he, hef⟩ := exists_support_identifyVariables R a s (c x) hf
  simpa only [maslovDegree, hef] using hc x e he

/-- Partial variable identification preserves both total-exponent filtration coordinates. -/
theorem identifyVariablesChain_mem_bifiltrationLevel (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) {u v : ℝ} {c : GridChainMinus R n}
    (hc : c ∈ bifiltrationLevel G R u v) :
    identifyVariablesChain R a s c ∈ bifiltrationLevel G R u v := by
  rw [mem_bifiltrationLevel_iff] at hc ⊢
  intro x f hf
  obtain ⟨e, he, hef⟩ := exists_support_identifyVariables R a s (c x) hf
  simpa only [hef] using hc x e he

/-- Chains whose coefficients already satisfy the chosen variable identifications. -/
noncomputable def identifiedChains (a : Fin n) (s : Finset (Fin n)) :
    Submodule R (GridChainMinus R n) :=
  LinearMap.ker (identifyVariablesChain R a s - LinearMap.id)

@[simp]
theorem mem_identifiedChains (a : Fin n) (s : Finset (Fin n)) (c : GridChainMinus R n) :
    c ∈ identifiedChains R a s ↔ identifyVariablesChain R a s c = c := by
  simp only [identifiedChains, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]

/-- Every projected chain satisfies the finite collection of identifications. -/
theorem identifyVariablesChain_mem_identifiedChains (a : Fin n) (s : Finset (Fin n))
    (c : GridChainMinus R n) : identifyVariablesChain R a s c ∈ identifiedChains R a s :=
  (mem_identifiedChains R a s _).mpr (identifyVariablesChain_idempotent R a s c)

/-- The full rectangle differential with the selected coefficient identifications. -/
noncomputable def identifiedDifferential (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) : GridChainMinus R n →ₗ[R] GridChainMinus R n :=
  (identifyVariablesChain R a s).comp ((differential G R).restrictScalars R)

@[simp]
theorem identifiedDifferential_apply (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) (c : GridChainMinus R n) :
    identifiedDifferential R G a s c = identifyVariablesChain R a s (differential G R c) := rfl

/-- Every differential output belongs to the identified coefficient module. -/
theorem identifiedDifferential_mem_identifiedChains (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) (c : GridChainMinus R n) :
    identifiedDifferential R G a s c ∈ identifiedChains R a s :=
  identifyVariablesChain_mem_identifiedChains R a s _

/-- The identified differential still lowers Maslov degree by one. -/
theorem identifiedDifferential_mem_maslovPiece (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) {m : ℤ} {c : GridChainMinus R n} (hc : c ∈ maslovPiece G R m) :
    identifiedDifferential R G a s c ∈ maslovPiece G R (m - 1) :=
  identifyVariablesChain_mem_maslovPiece R G a s (differential_mem_maslovPiece G hc)

/-- The identified differential preserves both filtration coordinates. -/
theorem identifiedDifferential_mem_bifiltrationLevel (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) {u v : ℝ} {c : GridChainMinus R n}
    (hc : c ∈ bifiltrationLevel G R u v) :
    identifiedDifferential R G a s c ∈ bifiltrationLevel G R u v :=
  identifyVariablesChain_mem_bifiltrationLevel R G a s
    (differential_mem_bifiltrationLevel G R u v c hc)

variable [CharP R 2]

/-- Finite coefficient identification preserves square zero for the full grid differential. -/
theorem identifiedDifferential_sq (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) (c : GridChainMinus R n) :
    identifiedDifferential R G a s (identifiedDifferential R G a s c) = 0 := by
  simp only [identifiedDifferential_apply, identifyVariablesChain_linear_projection,
    differential_sq_eq_zero, map_zero]

/-- Identify coefficients in the geometric X-marking homotopy between two O actions. -/
noncomputable def identifiedVariableHomotopy (G : GridDiagram n) (hG : G.IsKnot)
    (a b : Fin n) (s : Finset (Fin n)) :
    GridChainMinus R n →ₗ[R] GridChainMinus R n :=
  (identifyVariablesChain R a s).comp
    ((knotVariableActionHomotopy G R hG a b).restrictScalars R)

omit [CharP R 2] in
@[simp]
theorem identifiedVariableHomotopy_apply (G : GridDiagram n) (hG : G.IsKnot)
    (a b : Fin n) (s : Finset (Fin n)) (c : GridChainMinus R n) :
    identifiedVariableHomotopy R G hG a b s c =
      identifyVariablesChain R a s (knotVariableActionHomotopy G R hG a b c) := rfl

omit [CharP R 2] in
/-- The projected X-marking homotopy still lowers Maslov degree by one. -/
theorem identifiedVariableHomotopy_mem_maslovPiece (G : GridDiagram n) (hG : G.IsKnot)
    (a b : Fin n) (s : Finset (Fin n)) {m : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ maslovPiece G R m) :
    identifiedVariableHomotopy R G hG a b s c ∈ maslovPiece G R (m - 1) :=
  identifyVariablesChain_mem_maslovPiece R G a s
    (knotVariableActionHomotopy_mem_maslovPiece G R hG a b hc)

omit [CharP R 2] in
/-- The projected X-marking homotopy retains its strict Alexander decrease. -/
theorem identifiedVariableHomotopy_mem_bifiltrationLevel (G : GridDiagram n) (hG : G.IsKnot)
    (a b : Fin n) (s : Finset (Fin n)) {u v : ℝ} {c : GridChainMinus R n}
    (hc : c ∈ bifiltrationLevel G R u v) :
    identifiedVariableHomotopy R G hG a b s c ∈ bifiltrationLevel G R u (v - 1) :=
  identifyVariablesChain_mem_bifiltrationLevel R G a s
    (knotVariableActionHomotopy_mem_bifiltrationLevel G R hG a b hc)

/-- The next variable relation has its geometric null-homotopy after earlier eliminations. -/
theorem identifiedDifferential_variableHomotopy (G : GridDiagram n) (hG : G.IsKnot)
    (a b : Fin n) (s : Finset (Fin n)) (hb : b ∉ s) {c : GridChainMinus R n}
    (hc : c ∈ identifiedChains R a s) :
    identifiedDifferential R G a s (identifiedVariableHomotopy R G hG a b s c) +
      identifiedVariableHomotopy R G hG a b s (identifiedDifferential R G a s c) =
        (X a + X b : MvPolynomial (Fin n) R) • c := by
  rw [mem_identifiedChains] at hc
  simp only [identifiedDifferential_apply, identifiedVariableHomotopy_apply,
    identifyVariablesChain_linear_projection]
  rw [← map_add]
  have h := DFunLike.congr_fun (differential_knotVariableActionHomotopy G R hG a b) c
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at h
  rw [h, identifyVariablesChain_smul, map_add, identifyVariables_X_selected,
    identifyVariables_X, if_neg hb, hc]


/-- The homogeneous chains with coefficients in the partially identified polynomial ring. -/
noncomputable def identifiedMaslovPiece (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) (m : ℤ) : Submodule R (GridChainMinus R n) :=
  maslovPiece G R m ⊓ identifiedChains R a s

/-- The identified rectangle differential restricted to consecutive Maslov degrees. -/
noncomputable def identifiedGradedDifferential (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) (m : ℤ) :
    identifiedMaslovPiece R G a s (m + 1) →ₗ[R] identifiedMaslovPiece R G a s m :=
  (identifiedDifferential R G a s).restrict fun c hc =>
    ⟨by simpa using identifiedDifferential_mem_maslovPiece R G a s hc.1,
      identifiedDifferential_mem_identifiedChains R G a s c⟩

/-- The partially identified rectangle differential gives a native Maslov-graded complex. -/
noncomputable def identifiedMaslovComplex (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (identifiedMaslovPiece R G a s m))
    (fun m => ModuleCat.ofHom (identifiedGradedDifferential R G a s m))
    (fun m => by
      ext c : 2
      exact Subtype.ext (identifiedDifferential_sq R G a s c))

theorem identifiedMaslovComplex_d (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) (m : ℤ) :
    (identifiedMaslovComplex R G a s).d (m + 1) m =
      ModuleCat.ofHom (identifiedGradedDifferential R G a s m) := by
  simp only [identifiedMaslovComplex, ChainComplex.of_d]

/-- The existing two-coordinate support filtration restricted to the identified complex. -/
noncomputable def identifiedBifiltration (G : GridDiagram n) (a : Fin n)
    (s : Finset (Fin n)) : Bifiltration (identifiedMaslovComplex R G a s) where
  level u v m := ((bifiltrationLevel G R u v).restrictScalars R).comap
    (identifiedMaslovPiece R G a s m).subtype
  mono m _ _ _ _ hu hv := Submodule.comap_mono
    (bifiltrationLevel_mono G R hu hv)
  differential_mem u v i j c hc := by
    by_cases hij : j + 1 = i
    · subst i
      rw [identifiedMaslovComplex_d]
      exact identifiedDifferential_mem_bifiltrationLevel R G a s hc
    · rw [HomologicalComplex.shape _ _ _ (by simpa [ComplexShape.down_Rel] using hij)]
      exact Submodule.zero_mem _

end OnLeConjecture.KnotFloer.GridFull

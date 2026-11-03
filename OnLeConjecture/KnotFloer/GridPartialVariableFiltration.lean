/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPartialVariableNormalization

/-!
# Alexander filtration for successive variable normalization

The next quotient maps and the divided contraction preserve Alexander filtration
with the shifted second cone summand. Division raises the separate first
coordinate by one, so the quotient comparison is asserted only for Alexander.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti MvPolynomial CategoryTheory HomologicalComplex

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

omit [CharP R 2] in
/-- Both pair differentials preserve the shifted total-exponent bounds. -/
theorem identifiedPairDifferential_mem_bifiltrationLevel (a b : Fin n)
    (s : Finset (Fin n)) (twisted : Bool) {u v : ℝ} {c : VariableConeChains R n}
    (hc : c ∈ variableConeBifiltrationLevel G R u v) :
    identifiedPairDifferential G R a b s twisted c ∈ variableConeBifiltrationLevel G R u v := by
  have h₁ := identifiedDifferential_mem_bifiltrationLevel R G a s hc.1
  have h₂ := identifiedDifferential_mem_bifiltrationLevel R G a s hc.2
  cases twisted
  · exact ⟨h₁, h₂⟩
  · refine ⟨Submodule.add_mem _ h₁ ?_, h₂⟩
    change (X a + X b : MvPolynomial (Fin n) R) • c.2 ∈ bifiltrationLevel G R u v
    rw [add_smul]
    apply Submodule.add_mem
    · exact bifiltrationLevel_mono G R (by linarith) (by linarith)
        (X_smul_mem_bifiltrationLevel G R a c.2 hc.2)
    · exact bifiltrationLevel_mono G R (by linarith) (by linarith)
        (X_smul_mem_bifiltrationLevel G R b c.2 hc.2)

/-- Alexander filtration on either native pair complex after earlier identifications. -/
noncomputable def identifiedPairAlexanderFiltration (a b : Fin n)
    (s : Finset (Fin n)) (hb : b ∉ s) (twisted : Bool) :
    RealFiltration (identifiedPairComplex G R a b s hb twisted) where
  level v m := ((variableConeBifiltrationLevel G R 0 v).restrictScalars R).comap
    (identifiedConeMaslovPiece G R a s m).subtype
  mono m v v' hv := by
    apply Submodule.comap_mono
    intro c hc
    exact ⟨bifiltrationLevel_mono G R le_rfl hv hc.1,
      bifiltrationLevel_mono G R le_rfl (by linarith) hc.2⟩
  differential_mem v i j c hc := by
    by_cases h : j + 1 = i
    · subst i
      rw [identifiedPairComplex_d]
      exact identifiedPairDifferential_mem_bifiltrationLevel G R a b s twisted hc
    · rw [(identifiedPairComplex G R a b s hb twisted).shape i j h]
      exact Submodule.zero_mem _

/-- Alexander filtration on the native identified complex. -/
noncomputable def identifiedAlexanderFiltration (a : Fin n) (s : Finset (Fin n)) :
    RealFiltration (identifiedMaslovComplex R G a s) where
  level v m := (identifiedBifiltration R G a s).level 0 v m
  mono m v v' hv := (identifiedBifiltration R G a s).mono m 0 v 0 v' le_rfl hv
  differential_mem v i j c hc := (identifiedBifiltration R G a s).differential_mem 0 v i j c hc

/-- The next cone projection preserves Alexander filtration. -/
theorem identifiedConeToQuotientHom_preserves (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) :
    (identifiedPairAlexanderFiltration G R a b s hb true).Preserves
      (identifiedAlexanderFiltration G R a (insert b s))
        (identifiedConeToQuotientHom G R a b hab s hb) := by
  intro v m c hc
  exact quotientProjection_mem_bifiltrationLevel G R a b hc.1

/-- The next corrected inclusion preserves the shifted Alexander filtration. -/
theorem identifiedQuotientToConeHom_preserves (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) :
    (identifiedAlexanderFiltration G R a (insert b s)).Preserves
      (identifiedPairAlexanderFiltration G R a b s hb true)
        (identifiedQuotientToConeHom G R a b hab s hb) := by
  intro v m c hc
  refine ⟨hc, ?_⟩
  exact polynomial_bifiltration_first_zero G R
    (variableSumChainDivision_mem_bifiltrationLevel R G a b
      (identifiedDifferential_mem_bifiltrationLevel R G a s hc))

/-- The next divided inverse homotopy preserves Alexander filtration. -/
theorem identifiedQuotientConeNativeHomotopy_preserves (a b : Fin n) (hab : a ≠ b)
    (s : Finset (Fin n)) (hb : b ∉ s) (v : ℝ) (i j : ℤ)
    (c : (identifiedPairComplex G R a b s hb true).X i)
    (hc : c ∈ (identifiedPairAlexanderFiltration G R a b s hb true).level v i) :
    (identifiedQuotientConeNativeHomotopy G R a b hab s hb).hom i j c ∈
      (identifiedPairAlexanderFiltration G R a b s hb true).level v j := by
  change identifiedQuotientConeHomotopyComponent G R a b hab s hb i j c ∈ _
  by_cases h : j = i + 1
  · subst j
    rw [identifiedQuotientConeHomotopyComponent_succ]
    exact variableConeBifiltration_first_zero G R
      (quotientConeHomotopy_mem_bifiltrationLevel G R a b hc)
  · simp only [identifiedQuotientConeHomotopyComponent, dif_neg h]
    exact Submodule.zero_mem _

omit [CharP R 2] in
/-- The projected geometric shear preserves both shifted coordinate bounds. -/
theorem identifiedConeShear_mem_bifiltrationLevel (hG : G.IsKnot) (a b : Fin n)
    (s : Finset (Fin n)) {u v : ℝ} {c : VariableConeChains R n}
    (hc : c ∈ variableConeBifiltrationLevel G R u v) :
    identifiedConeShear G R hG a b s c ∈ variableConeBifiltrationLevel G R u v := by
  refine ⟨Submodule.add_mem _ hc.1 ?_, hc.2⟩
  change identifiedVariableHomotopy R G hG a b s c.2 ∈ bifiltrationLevel G R u v
  simpa only [add_sub_cancel_right] using
    identifiedVariableHomotopy_mem_bifiltrationLevel R G hG a b s hc.2

/-- The cone-splitting isomorphism preserves Alexander filtration. -/
theorem identifiedConeSplitIso_hom_preserves (hG : G.IsKnot) (a b : Fin n)
    (s : Finset (Fin n)) (hb : b ∉ s) :
    (identifiedPairAlexanderFiltration G R a b s hb true).Preserves
      (identifiedPairAlexanderFiltration G R a b s hb false)
        (identifiedConeSplitIso G R hG a b s hb).hom := by
  intro v m c hc
  exact identifiedConeShear_mem_bifiltrationLevel G R hG a b s hc

/-- Its equal geometric shear inverse also preserves Alexander filtration. -/
theorem identifiedConeSplitIso_inv_preserves (hG : G.IsKnot) (a b : Fin n)
    (s : Finset (Fin n)) (hb : b ∉ s) :
    (identifiedPairAlexanderFiltration G R a b s hb false).Preserves
      (identifiedPairAlexanderFiltration G R a b s hb true)
        (identifiedConeSplitIso G R hG a b s hb).inv := by
  intro v m c hc
  exact identifiedConeShear_mem_bifiltrationLevel G R hG a b s hc

/-- The next normalization map preserves Alexander filtration after any earlier identifications. -/
theorem identifiedNormalizationHomotopyEquiv_hom_preserves (hG : G.IsKnot) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    (identifiedAlexanderFiltration G R a (insert b s)).Preserves
      (identifiedPairAlexanderFiltration G R a b s hb false)
        (identifiedNormalizationHomotopyEquiv G R hG a b hab s hb).hom :=
  (identifiedQuotientToConeHom_preserves G R a b hab s hb).comp
    (identifiedConeSplitIso_hom_preserves G R hG a b s hb)

/-- The next normalization inverse preserves Alexander filtration. -/
theorem identifiedNormalizationHomotopyEquiv_inv_preserves (hG : G.IsKnot) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) :
    (identifiedPairAlexanderFiltration G R a b s hb false).Preserves
      (identifiedAlexanderFiltration G R a (insert b s))
        (identifiedNormalizationHomotopyEquiv G R hG a b hab s hb).inv :=
  (identifiedConeSplitIso_inv_preserves G R hG a b s hb).comp
    (identifiedConeToQuotientHom_preserves G R a b hab s hb)


/-- The nonzero split-side inverse homotopy preserves Alexander filtration. -/
theorem identifiedNormalizationSplitHomotopy_preserves (hG : G.IsKnot) (a b : Fin n)
    (hab : a ≠ b) (s : Finset (Fin n)) (hb : b ∉ s) (v : ℝ) (i j : ℤ)
    (c : (identifiedPairComplex G R a b s hb false).X i)
    (hc : c ∈ (identifiedPairAlexanderFiltration G R a b s hb false).level v i) :
    (identifiedNormalizationSplitHomotopy G R hG a b hab s hb).hom i j c ∈
      (identifiedPairAlexanderFiltration G R a b s hb false).level v j := by
  change (identifiedConeSplitIso G R hG a b s hb).hom.f j
    ((identifiedQuotientConeNativeHomotopy G R a b hab s hb).hom i j
      ((identifiedConeSplitIso G R hG a b s hb).inv.f i c)) ∈
        (identifiedPairAlexanderFiltration G R a b s hb false).level v j
  exact identifiedConeSplitIso_hom_preserves G R hG a b s hb v j _
    (identifiedQuotientConeNativeHomotopy_preserves G R a b hab s hb v i j _
      (identifiedConeSplitIso_inv_preserves G R hG a b s hb v i c hc))

end OnLeConjecture.KnotFloer.GridFull

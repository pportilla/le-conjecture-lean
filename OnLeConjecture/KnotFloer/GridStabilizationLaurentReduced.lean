/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationReducedFiltration
public import OnLeConjecture.KnotFloer.FinsuppCoefficientExtension
public import OnLeConjecture.KnotFloer.GridFullLaurent

/-!
# The reduced stabilization contraction with Laurent coefficients

The reduced differential and its constructed contraction are extended by applying the
constant inclusion to every matrix entry. The full Laurent exponents contribute `-2k`
to Maslov degree and `-k` to both filtration coordinates. The center Alexander shift
is the one proved in `GridStabilizationReducedFiltration`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R]

/-- Laurent chains on the reduced comparison-cone basis. -/
abbrev ReducedConeLaurentChain := G.StabilizeXOffCenterState s ⊕ GridState n →₀ LaurentPolynomial R

/-- Extend the reduced differential through the inclusion of constant Laurent polynomials. -/
noncomputable def laurentReducedConeDifferential : Module.End (LaurentPolynomial R)
    (ReducedConeLaurentChain G s R) :=
  coefficientExtension LaurentPolynomial.C (G.stabilizeXReducedCone s R)

variable [CharP R 2]

/-- Extend the proved reduced contracting homotopy through the constant inclusion. -/
noncomputable def laurentReducedConeHomotopy : Module.End (LaurentPolynomial R)
    (ReducedConeLaurentChain G s R) :=
  coefficientExtension LaurentPolynomial.C (reducedStabilizationHomotopy G s R)

/-- The constant-coefficient Laurent differential is square zero. -/
theorem laurentReducedConeDifferential_comp_self :
    laurentReducedConeDifferential G s R ∘ₗ laurentReducedConeDifferential G s R = 0 := by
  have h := congrArg (coefficientExtensionRingHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))
    (G.stabilizeXReducedCone_comp_self s R)
  simpa only [← Module.End.mul_eq_comp, map_mul, map_zero,
    coefficientExtensionRingHom_apply, laurentReducedConeDifferential] using h

/-- The extended maps satisfy the contracting equation as Laurent-linear maps. -/
theorem laurentReducedConeHomotopy_contracts :
    laurentReducedConeDifferential G s R ∘ₗ laurentReducedConeHomotopy G s R +
      laurentReducedConeHomotopy G s R ∘ₗ laurentReducedConeDifferential G s R = LinearMap.id := by
  have h := congrArg (coefficientExtensionRingHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))
    (reducedStabilizationHomotopy_contracts G s R)
  simpa only [← Module.End.mul_eq_comp, ← Module.End.one_eq_id, map_add, map_mul, map_one,
    coefficientExtensionRingHom_apply, laurentReducedConeDifferential,
    laurentReducedConeHomotopy] using h

/-- The extended homotopy retains the special-contraction side condition. -/
theorem laurentReducedConeHomotopy_comp_self :
    laurentReducedConeHomotopy G s R ∘ₗ laurentReducedConeHomotopy G s R = 0 := by
  have h := congrArg (coefficientExtensionRingHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))
    (reducedStabilizationHomotopy_comp_self G s R)
  simpa only [← Module.End.mul_eq_comp, map_mul, map_zero,
    coefficientExtensionRingHom_apply, laurentReducedConeHomotopy] using h

/-- A special contraction over the Laurent ring, with the proved matching homotopy. -/
noncomputable def laurentReducedConeContraction :
    LinearSpecialContraction (laurentReducedConeDifferential G s R)
      (0 : Module.End (LaurentPolynomial R) PUnit.{1}) where
  incl := 0
  proj := 0
  homotopy := laurentReducedConeHomotopy G s R
  dM_comp_incl := by simp
  proj_comp_dM := by simp
  proj_comp_incl := Subsingleton.elim _ _
  dM_comp_homotopy_add_homotopy_comp_dM := by
    change _ = (LinearMap.id : Module.End (LaurentPolynomial R)
      (ReducedConeLaurentChain G s R)) - 0
    calc
      _ = LinearMap.id := laurentReducedConeHomotopy_contracts G s R
      _ = _ := by
        apply LinearMap.ext
        intro c
        apply Finsupp.ext
        intro j
        change c j = c j - 0
        exact (sub_zero _).symm
  homotopy_comp_incl := by simp
  proj_comp_homotopy := by simp
  homotopy_comp_homotopy := laurentReducedConeHomotopy_comp_self G s R

omit [CharP R 2] in
/-- A nonzero extended coefficient keeps its Laurent exponent and comes from a base matrix entry. -/
theorem exists_support_coefficientExtension_C {ι : Type*} [Finite ι]
    (f : Module.End R (ι →₀ R)) (c : ι →₀ LaurentPolynomial R) {j : ι} {k : ℤ}
    (hk : k ∈ (coefficientExtension LaurentPolynomial.C f c j).coeff.support) :
    ∃ i : ι, k ∈ (c i).coeff.support ∧ f (single i 1) j ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  rw [coefficientExtension_apply_apply, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨a, ha, b, hb, hk⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hi)
  change b ∈ (single 0 (f (single i 1) j)).support at hb
  have hb0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hb)
  subst b
  have hi0 : f (single i 1) j ≠ 0 := by
    intro hz
    simp [hz] at hb
  have hk' : a = k := by simpa using hk
  exact ⟨i, hk' ▸ ha, hi0⟩

/-- Maslov-homogeneous Laurent chains on the shifted cone basis. -/
noncomputable def laurentReducedConeMaslovPiece (m : ℤ) :
    Submodule R (ReducedConeLaurentChain G s R) where
  carrier := {c | ∀ i k, k ∈ (c i).coeff.support → reducedConeMaslov G s i - 2 * k = m}
  zero_mem' := by simp
  add_mem' := by
    classical
    intro c d hc hd i k hk
    rw [Finsupp.add_apply, AddMonoidAlgebra.coeff_add] at hk
    exact (Finset.mem_union.mp (Finsupp.support_add hk)).elim (hc i k) (hd i k)
  smul_mem' := by
    intro a c hc i k hk
    rw [Finsupp.smul_apply, AddMonoidAlgebra.coeff_smul] at hk
    exact hc i k (Finsupp.support_smul hk)

/-- The two Laurent coordinate bounds, including the center shift of the comparison cone. -/
noncomputable def laurentReducedConeBifiltrationLevel (u v : ℚ) :
    Submodule R (ReducedConeLaurentChain G s R) where
  carrier := {c | ∀ i k, k ∈ (c i).coeff.support →
    -(k : ℚ) ≤ u ∧ reducedConeAlexander G s i - k ≤ v}
  zero_mem' := by simp
  add_mem' := by
    classical
    intro c d hc hd i k hk
    rw [Finsupp.add_apply, AddMonoidAlgebra.coeff_add] at hk
    exact (Finset.mem_union.mp (Finsupp.support_add hk)).elim (hc i k) (hd i k)
  smul_mem' := by
    intro a c hc i k hk
    rw [Finsupp.smul_apply, AddMonoidAlgebra.coeff_smul] at hk
    exact hc i k (Finsupp.support_smul hk)

omit [CharP R 2] in
/-- The extended reduced differential lowers the full Laurent Maslov degree by one. -/
theorem laurentReducedConeDifferential_mem_maslovPiece {m : ℤ}
    {c : ReducedConeLaurentChain G s R} (hc : c ∈ laurentReducedConeMaslovPiece G s R m) :
    laurentReducedConeDifferential G s R c ∈ laurentReducedConeMaslovPiece G s R (m - 1) := by
  intro j k hk
  obtain ⟨i, hi, hij⟩ := exists_support_coefficientExtension_C R _ c hk
  have hM := (reducedCone_grading_of_mem_support G s R i j
    (Finsupp.mem_support_iff.mpr hij)).1
  have hm := hc i k hi
  omega

omit [CharP R 2] in
/-- The extended reduced differential preserves both cone-coordinate bounds. -/
theorem laurentReducedConeDifferential_mem_bifiltrationLevel {u v : ℚ}
    {c : ReducedConeLaurentChain G s R}
    (hc : c ∈ laurentReducedConeBifiltrationLevel G s R u v) :
    laurentReducedConeDifferential G s R c ∈ laurentReducedConeBifiltrationLevel G s R u v := by
  intro j k hk
  obtain ⟨i, hi, hij⟩ := exists_support_coefficientExtension_C R _ c hk
  have hA := (reducedCone_grading_of_mem_support G s R i j
    (Finsupp.mem_support_iff.mpr hij)).2
  simpa only [hA] using hc i k hi

/-- The extended matching homotopy raises the full Laurent Maslov degree by one. -/
theorem laurentReducedConeHomotopy_mem_maslovPiece {m : ℤ}
    {c : ReducedConeLaurentChain G s R} (hc : c ∈ laurentReducedConeMaslovPiece G s R m) :
    laurentReducedConeHomotopy G s R c ∈ laurentReducedConeMaslovPiece G s R (m + 1) := by
  intro j k hk
  obtain ⟨i, hi, hij⟩ := exists_support_coefficientExtension_C R _ c hk
  have hsingle : (single i (1 : R)) ∈ reducedConeMaslovPiece G s R
      (reducedConeMaslov G s i) := Finsupp.single_mem_supported R 1 rfl
  have hM := (Finsupp.mem_supported R _).mp
    (reducedStabilizationHomotopy_mem_maslovPiece G s R hsingle)
    (Finsupp.mem_support_iff.mpr hij)
  change reducedConeMaslov G s j = reducedConeMaslov G s i + 1 at hM
  have hm := hc i k hi
  omega

/-- The extended matching homotopy preserves both cone-coordinate bounds. -/
theorem laurentReducedConeHomotopy_mem_bifiltrationLevel {u v : ℚ}
    {c : ReducedConeLaurentChain G s R}
    (hc : c ∈ laurentReducedConeBifiltrationLevel G s R u v) :
    laurentReducedConeHomotopy G s R c ∈ laurentReducedConeBifiltrationLevel G s R u v := by
  intro j k hk
  obtain ⟨i, hi, hij⟩ := exists_support_coefficientExtension_C R _ c hk
  have hsingle : (single i (1 : R)) ∈ reducedConeAlexanderLevel G s R
      (reducedConeAlexander G s i) := Finsupp.single_mem_supported R 1 (by
        change reducedConeAlexander G s i ≤ reducedConeAlexander G s i
        exact le_rfl)
  have hA := (Finsupp.mem_supported R _).mp
    (reducedStabilizationHomotopy_mem_alexanderLevel G s R hsingle)
    (Finsupp.mem_support_iff.mpr hij)
  obtain ⟨hfirst, hsecond⟩ := hc i k hi
  exact ⟨hfirst, (sub_le_sub_right hA (k : ℚ)).trans hsecond⟩

end OnLeConjecture.KnotFloer.GridFull

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullTwoByTwoHomology
public import OnLeConjecture.KnotFloer.BifilteredSpectral

/-!
# Degree-zero spectral normalization for the two-by-two grid

A homogeneous Laurent monomial of Maslov degree zero in the standard two-by-two grid is
necessarily the X-state with Laurent exponent zero. Hence every chain of this degree has
both filtration coordinates zero, and every nonzero native homology class in degree zero
has weighted threshold zero for parameters in `[0,2]`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable (R : Type*) [CommRing R] [CharP R 2]

/-- The computed zero differential also vanishes on each Maslov homogeneous piece. -/
theorem laurentGradedDifferential_twoByTwo_eq_zero (m : ℤ) :
    laurentGradedDifferential GridDiagram.twoByTwo R m = 0 := by
  ext c : 1
  apply Subtype.ext
  change laurentDifferential GridDiagram.twoByTwo R c = 0
  rw [laurentDifferential_twoByTwo_eq_zero, LinearMap.zero_apply]

/-- Every native graded differential of the two-by-two Laurent complex vanishes. -/
theorem laurentMaslovComplex_twoByTwo_d_eq_zero (i j : ℤ) :
    (laurentMaslovComplex GridDiagram.twoByTwo R).d i j = 0 := by
  by_cases h : j + 1 = i
  · subst i
    rw [laurentMaslovComplex_d, laurentGradedDifferential_twoByTwo_eq_zero,
      ModuleCat.ofHom_zero]
    simp only [CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
  · exact (laurentMaslovComplex GridDiagram.twoByTwo R).shape i j
      (by simpa only [ComplexShape.down_Rel] using h)

/-- Native homology in every Maslov degree is the corresponding homogeneous Laurent piece. -/
noncomputable def twoByTwoMaslovHomologyEquivPiece (m : ℤ) :
    (laurentMaslovComplex GridDiagram.twoByTwo R).homology m ≃ₗ[R]
      laurentMaslovPiece GridDiagram.twoByTwo R m :=
  (((laurentMaslovComplex GridDiagram.twoByTwo R).isoHomologyπ (m + 1) m (by simp)
      (laurentMaslovComplex_twoByTwo_d_eq_zero R _ _)).symm ≪≫
    (laurentMaslovComplex GridDiagram.twoByTwo R).iCyclesIso m (m - 1) (by simp)
      (laurentMaslovComplex_twoByTwo_d_eq_zero R _ _)).toLinearEquiv |>.trans
        (laurentMaslovChainEquiv GridDiagram.twoByTwo R m)

/-- There is precisely one state and exponent that can occur in Maslov degree zero. -/
theorem twoByTwo_degree_zero_support {x : GridState 2} {k : ℤ}
    (h : laurentMaslovDegree GridDiagram.twoByTwo k x = 0) :
    x = GridState.twoByTwoSwap ∧ k = 0 := by
  rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl
  · rw [laurentMaslovDegree_twoByTwo_O] at h
    omega
  · rw [laurentMaslovDegree_twoByTwo_X] at h
    exact ⟨rfl, by omega⟩

/-- The degree-zero homogeneous chain module is one copy of the coefficient ring. -/
noncomputable def twoByTwoDegreeZeroEquiv :
    laurentMaslovPiece GridDiagram.twoByTwo R 0 ≃ₗ[R] R where
  toFun c := ((c : LaurentChain R 2) GridState.twoByTwoSwap).coeff 0
  invFun a := ⟨Finsupp.single GridState.twoByTwoSwap (AddMonoidAlgebra.single 0 a), by
    simpa only [laurentMaslovDegree_twoByTwo_X, mul_zero] using
      single_monomial_mem_laurentMaslovPiece GridDiagram.twoByTwo R 0 GridState.twoByTwoSwap a⟩
  left_inv c := by
    apply Subtype.ext
    apply Finsupp.ext
    intro x
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro k
    by_cases hk : k ∈ ((c : LaurentChain R 2) x).coeff.support
    · obtain ⟨rfl, rfl⟩ := twoByTwo_degree_zero_support (c.property x k hk)
      simp
    · have hz := Finsupp.notMem_support_iff.mp hk
      by_cases hx : x = GridState.twoByTwoSwap
      · subst x
        by_cases hk0 : k = 0
        · subst k
          simp
        · simp [hk0, hz]
      · simp [Finsupp.single_eq_of_ne hx, hz]
  right_inv a := by simp
  map_add' a b := rfl
  map_smul' r a := rfl

/-- Native homology in Maslov degree zero is one copy of the coefficient ring. -/
noncomputable def twoByTwoDegreeZeroHomologyEquiv :
    (laurentMaslovComplex GridDiagram.twoByTwo R).homology 0 ≃ₗ[R] R :=
  (twoByTwoMaslovHomologyEquivPiece R 0).trans (twoByTwoDegreeZeroEquiv R)

/-- The degree-zero spectral normalization applies to a nonzero homology group. -/
theorem exists_nonzero_twoByTwo_degree_zero_homology [Nontrivial R] :
    ∃ ξ : (laurentMaslovComplex GridDiagram.twoByTwo R).homology 0, ξ ≠ 0 := by
  refine ⟨(twoByTwoDegreeZeroHomologyEquiv R).symm 1, ?_⟩
  intro h
  have h' := congrArg (twoByTwoDegreeZeroHomologyEquiv R) h
  simp at h'

/-- Every degree-zero chain lies at bifiltration level `(0,0)`. -/
theorem twoByTwo_degree_zero_mem_level (c : (laurentMaslovComplex GridDiagram.twoByTwo R).X 0) :
    c ∈ (laurentMaslovBifiltration GridDiagram.twoByTwo R).level 0 0 0 := by
  intro x k hk
  obtain ⟨rfl, rfl⟩ := twoByTwo_degree_zero_support
    ((laurentMaslovChainEquiv GridDiagram.twoByTwo R 0 c).property x k hk)
  simp only [Int.cast_zero, GridDiagram.alexander_twoByTwo_twoByTwoSwap, Rat.cast_zero,
    neg_zero, sub_zero, le_refl, and_self]

/-- A nonzero chain in degree zero forces both filtration levels to be nonnegative. -/
theorem twoByTwo_degree_zero_bounds (c : (laurentMaslovComplex GridDiagram.twoByTwo R).X 0)
    (hc : c ≠ 0) {a b : ℝ}
    (hmem : c ∈ (laurentMaslovBifiltration GridDiagram.twoByTwo R).level a b 0) :
    0 ≤ a ∧ 0 ≤ b := by
  let v := laurentMaslovChainEquiv GridDiagram.twoByTwo R 0 c
  have hv : (v : LaurentChain R 2) ≠ 0 := by
    intro h
    apply hc
    apply (laurentMaslovChainEquiv GridDiagram.twoByTwo R 0).injective
    rw [map_zero]
    exact Subtype.ext h
  obtain ⟨x, hx⟩ := Finsupp.ne_iff.mp hv
  rw [Finsupp.zero_apply] at hx
  have hx' : ((v : LaurentChain R 2) x).coeff ≠ 0 := by simpa using hx
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hx'
  obtain ⟨rfl, rfl⟩ := twoByTwo_degree_zero_support (v.property x k hk)
  simpa only [Int.cast_zero, neg_zero, GridDiagram.alexander_twoByTwo_twoByTwoSwap,
    Rat.cast_zero, sub_zero] using hmem GridState.twoByTwoSwap 0 hk

/-- Below zero the weighted degree-zero chain group vanishes. -/
theorem twoByTwo_weighted_level_eq_bot (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    {s : ℝ} (hs : s < 0) :
    ((laurentMaslovBifiltration GridDiagram.twoByTwo R).weighted t).level s 0 = ⊥ := by
  apply le_antisymm _ bot_le
  intro c hc
  induction hc using Submodule.span_induction with
  | mem c hc =>
    rw [Submodule.mem_bot]
    by_contra hne
    obtain ⟨a, b, hmem, hweight⟩ := hc
    obtain ⟨ha, hb⟩ := twoByTwo_degree_zero_bounds R c hne hmem
    have ha' := mul_nonneg (show 0 ≤ 1 - t / 2 by linarith) ha
    have hb' := mul_nonneg (show 0 ≤ t / 2 by linarith) hb
    linarith
  | zero => exact Submodule.zero_mem _
  | add c d _ _ hc hd => exact Submodule.add_mem _ hc hd
  | smul p c _ hc => exact Submodule.smul_mem _ p hc

/-- Every degree-zero homology class has a cycle representative at weighted level zero. -/
theorem twoByTwo_representedBelow_zero
    (ξ : (laurentMaslovComplex GridDiagram.twoByTwo R).homology 0) (t : ℝ) :
    ((laurentMaslovBifiltration GridDiagram.twoByTwo R).weighted t).RepresentedBelow 0 ξ 0 := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((laurentMaslovComplex GridDiagram.twoByTwo R).homologyπ 0)).mp inferInstance ξ
  refine ⟨z, Submodule.subset_span ⟨0, 0, twoByTwo_degree_zero_mem_level R _, ?_⟩, hz⟩
  simp

/-- Each nonzero native degree-zero homology class of the standard two-by-two grid has
weighted spectral threshold zero throughout `[0,2]`. -/
theorem spectralThreshold_twoByTwo_degree_zero
    (ξ : (laurentMaslovComplex GridDiagram.twoByTwo R).homology 0) (hξ : ξ ≠ 0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    ((laurentMaslovBifiltration GridDiagram.twoByTwo R).weighted t).spectralThreshold 0 ξ = 0 := by
  apply le_antisymm
  · simpa using RealFiltration.spectralThreshold_le_of_representedBelow
      (twoByTwo_representedBelow_zero R ξ t)
  · simpa using RealFiltration.le_spectralThreshold_of_level_eq_bot
      ((laurentMaslovBifiltration GridDiagram.twoByTwo R).weighted t) 0 ξ hξ 0
      (fun _ hs => twoByTwo_weighted_level_eq_bot R t ht0 ht2 hs)

/-- The algebraic per-class Upsilon value on the standard two-by-two grid is zero in degree zero. -/
theorem classUpsilon_twoByTwo_degree_zero
    (ξ : (laurentMaslovComplex GridDiagram.twoByTwo R).homology 0) (hξ : ξ ≠ 0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    (laurentMaslovBifiltration GridDiagram.twoByTwo R).classUpsilon 0 ξ t = 0 := by
  unfold Bifiltration.classUpsilon
  rw [spectralThreshold_twoByTwo_degree_zero R ξ hξ t ht0 ht2]
  simp

end OnLeConjecture.KnotFloer.GridFull

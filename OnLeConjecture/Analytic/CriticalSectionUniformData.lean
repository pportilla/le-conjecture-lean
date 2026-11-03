/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SectionImageSquareSum
public import OnLeConjecture.Analytic.ResolutionDeltaIdentity
public import OnLeConjecture.Analytic.PlaneSectionGeneric
public import OnLeConjecture.Analytic.MilnorBlowupRecurrence

/-!
# Section data in the coordinates of a resolution tree

For a locally injective germ `g : (ℂ², 0) → (ℂ³, 0)` and its weak-blowup tree
`T`, a generic member `v = q ⋅ g` of the tree satisfies
`2 δ(v) + Σ_p m_p = Σ_p m_p²`. A companion `r ⋅ g` meeting `v` finitely
completes `q` and `r` to an invertible target matrix with rows `q`, `s`, `r`.
In these coordinates the reduced image of `{v = 0}` has exact multiplicity
`S = Σ_p m_p²`, for every section image factorization of the transformed germ.

The file also defines the reduced local image equation of a level curve at a
point, chosen from a section image factorization of the recentred germ, and
proves the lower bound `δ(f) ≥ k (k - 1) / 2` for a reduced germ of exact
order `k`.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve

/-- The reduced local image equation at `G(x)` of the level curve of `G₀`
through `x`, chosen from a section image factorization of the recentred
germ, and zero when no such factorization exists. -/
noncomputable def localSectionEquation (G : Source 2 → Source 3) (x : Source 2) : Germ 2 := by
  classical
  exact if h : ∃ hG : AnalyticAt ℂ G x,
      Nonempty (SectionImageFactorization (PointedMapGerm.recenterOfFunction G x hG)) then
    (Classical.choice h.choose_spec).imageEquation
  else 0

/-- The chosen local image equation comes from a section image factorization
of the recentred germ, and computes the local delta invariant. -/
theorem exists_localSectionEquation_spec (G : Source 2 → Source 3) (x : Source 2)
    (hG : AnalyticAt ℂ G x)
    (hinj : (PointedMapGerm.recenterOfFunction G x hG).HasInjectiveRepresentative)
    (D : SectionImageFactorization (PointedMapGerm.recenterOfFunction G x hG)) :
    ∃ D' : SectionImageFactorization (PointedMapGerm.recenterOfFunction G x hG),
      localSectionEquation G x = D'.imageEquation ∧
      localSectionDelta G x = deltaInvariant (localSectionEquation G x) := by
  classical
  have h : ∃ hG : AnalyticAt ℂ G x,
      Nonempty (SectionImageFactorization (PointedMapGerm.recenterOfFunction G x hG)) :=
    ⟨hG, ⟨D⟩⟩
  refine ⟨Classical.choice h.choose_spec, ?_, ?_⟩
  · unfold localSectionEquation
    rw [dif_pos h]
  · have heq : localSectionEquation G x = (Classical.choice h.choose_spec).imageEquation := by
      unfold localSectionEquation
      rw [dif_pos h]
    rw [heq]
    exact localSectionDelta_eq G x hG hinj _

/-- A reduced germ of exact order `k > 0` has delta invariant at least
`k (k - 1) / 2`. -/
theorem choose_two_le_deltaInvariant {f : Germ 2} {k : ℕ} (hk : 0 < k)
    (hf : f ∈ maximalIdeal 2 ^ k) (hn : f ∉ maximalIdeal 2 ^ (k + 1)) (hsq : Squarefree f) :
    k.choose 2 ≤ deltaInvariant f := by
  obtain ⟨s, -, hrec⟩ :=
    exists_projectiveStrictTransform_milnorBranchDefect_recurrence k hk f hf hn hsq
  have h2 := two_mul_deltaInvariant hsq
  rw [Nat.choose_two_right]
  apply Nat.div_le_of_le_mul
  omega

namespace RawProjectiveWeakBlowupTree

/-- For every target change whose first component is a generic tree member
and whose components span the original components, the reduced image of the
first section has exact multiplicity equal to the tree square sum. -/
theorem imageEquation_exact_squareSum_of_component_zero
    {g : PointedMapGerm 2 3} (T : RawProjectiveWeakBlowupTree g.1.component)
    (hg : g.HasInjectiveRepresentative) (q₀ : Fin 3 → ℂ)
    (hq₀ : ∀ p, germLinearCombination (T.generators p) q₀ ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (f : PointedMapGerm 2 3) (hfi : f.HasInjectiveRepresentative)
    (hf₀ : f.1.component 0 = germLinearCombination g.1.component q₀)
    (hspan : Submodule.span ℂ (Set.range f.1.component) =
      Submodule.span ℂ (Set.range g.1.component))
    (D : SectionImageFactorization f) :
    D.imageEquation ∈ maximalIdeal 2 ^ (∑ p, (T.multiplicity p) ^ 2) ∧
      D.imageEquation ∉ maximalIdeal 2 ^ ((∑ p, (T.multiplicity p) ^ 2) + 1) := by
  classical
  have hnonzero (i : D.branches) : ∃ j, (D.parametrization i).pullbackRingHom
      (g.1.component j) ≠ 0 := by
    have hi := g.comp_hasInjectiveRepresentative (D.parametrization i) hg
      (D.parametrizationInjective i)
    obtain ⟨j, hj⟩ := PointedMapGerm.exists_nonzero_coordinate_pullback_of_injective_curve
      (g.comp (D.parametrization i)) hi
    refine ⟨j, ?_⟩
    simpa only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
      PointedMapGerm.pullback_coordinate] using hj
  obtain ⟨U, hU, hUdense, hUorder⟩ :=
    exists_open_dense_pullback_combinations_minimum_order g.1.component D.parametrization hnonzero
  obtain ⟨r, hr, hfinite, hinter⟩ := T.exists_companion_intersection_eq_squareSum_mem_open
    q₀ hq₀ U hU hUdense.nonempty
  have hmem : germLinearCombination g.1.component r ∈
      Submodule.span ℂ (Set.range f.1.component) := by
    rw [hspan]
    change (∑ j, r j • g.1.component j) ∈ _
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  obtain ⟨c, a, hdecomp⟩ :=
    exists_plane_linear_form_mod_first_component f _ hmem
  let q : Germ 2 := germLinearCombination (coordinate : Fin 2 → Germ 2) c
  let u := germLinearCombination g.1.component r
  let w := f.pullbackRingHom (hyperplaneExtension 2 q)
  have hdecomp' : u = w + a • f.1.component 0 := hdecomp
  have hsub : u - f.1.component 0 * constRingHom 2 a = w := by
    rw [hdecomp']
    change w + constRingHom 2 a * f.1.component 0 - f.1.component 0 * constRingHom 2 a = w
    ring
  have hideal : pairIdeal (f.1.component 0) w = pairIdeal (f.1.component 0) u := by
    rw [← hsub]
    exact pairIdeal_sub_mul_right _ _ _
  have hfiniteu : HasFiniteIntersection (f.1.component 0) u := by
    rwa [hf₀]
  have hfinitew := hfiniteu.of_pairIdeal_eq hideal.symm
  have hminimum (i : D.branches) :
      vanishingOrder ((D.parametrization i).pullbackRingHom w) =
        ⨅ j : Fin 3, vanishingOrder ((D.parametrization i).pullbackRingHom (f.1.component j)) := by
    have hpull : (D.parametrization i).pullbackRingHom u =
        (D.parametrization i).pullbackRingHom w := by
      rw [hdecomp', map_add, PointedMapGerm.pullback_complex_smul,
        D.section_zero i, smul_zero, add_zero]
    rw [← hpull, hUorder r hr i]
    exact (iInf_pullback_order_eq_of_span_eq (D.parametrization i)
      f.1.component g.1.component hspan).symm
  have hexact := D.imageEquation_exact_order_of_minimum hfi q hfinitew hminimum
  have hsum : intersectionMultiplicity (f.1.component 0) w hfinitew =
      ∑ p, (T.multiplicity p) ^ 2 := by
    rw [intersectionMultiplicity_eq_of_pairIdeal_eq hfinitew hfiniteu hideal]
    have h := hinter.trans (T.pointBasis_squareSum q₀ hq₀)
    simpa only [hf₀, u] using h
  rw [hsum] at hexact
  exact hexact

/-- **Tree coordinates.** A locally injective germ has a weak-blowup tree,
generic member coefficients `q`, and an invertible target matrix `A` with
first row `q`, such that the member `v = q ⋅ g` is reduced,
`2 δ(v) + Σ_p m_p = Σ_p m_p²`, and the third row gives a component meeting
`v` finitely. -/
theorem exists_tree_section_coordinates (g : PointedMapGerm 2 3)
    (hi : g.HasInjectiveRepresentative) :
    ∃ (T : RawProjectiveWeakBlowupTree g.1.component) (q : Fin 3 → ℂ)
      (A : Matrix (Fin 3) (Fin 3) ℂ),
      (∀ p, germLinearCombination (T.generators p) q ∉
        maximalIdeal 2 ^ (T.multiplicity p + 1)) ∧
      Squarefree (germLinearCombination g.1.component q) ∧
      2 * deltaInvariant (germLinearCombination g.1.component q) + (∑ p, T.multiplicity p) =
        ∑ p, (T.multiplicity p) ^ 2 ∧
      A.det ≠ 0 ∧ A 0 = q ∧
      HasFiniteIntersection (germLinearCombination g.1.component (A 0))
        (germLinearCombination g.1.component (A 2)) := by
  classical
  have hIdeal : g.1.coordinateIdeal = Ideal.span (Set.range g.1.component) := by
    apply le_antisymm
    · rw [MapGerm.coordinateIdeal_le]
      intro i
      exact Ideal.subset_span (Set.mem_range_self i)
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact g.1.component_mem_coordinateIdeal i
  have hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range g.1.component)) := by
    rw [← hIdeal]
    exact g.coordinateQuotient_moduleFinite (g.injective_isFiniteAtOrigin_two hi)
  obtain ⟨T⟩ := RawProjectiveWeakBlowupTree.exists_of_finite_colength g.1.component
    (fun i => g.coordinateIdeal_le_maximalIdeal (g.1.component_mem_coordinateIdeal i)) hfinite
  obtain ⟨q₀, -, hq₀⟩ := T.exists_exact_coefficients Set.univ isOpen_univ Set.univ_nonempty
  obtain ⟨V, -, ⟨q, hqV⟩, -, hV⟩ :=
    T.exists_open_reduced_members_delta_identity q₀ hq₀ Set.univ isOpen_univ Set.univ_nonempty
  obtain ⟨hmembers, hdelta⟩ := hV q hqV
  have hq := fun p => (hmembers p).1
  have hsq : Squarefree (germLinearCombination g.1.component q) := by
    simpa only [T.generators_root] using (hmembers T.root).2
  obtain ⟨r, -, hfin, -⟩ := T.exists_companion_intersection_eq_squareSum_mem_open q hq
    Set.univ isOpen_univ ⟨0, Set.mem_univ _⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsq
    exact not_squarefree_zero hsq
  obtain ⟨s, hs⟩ := exists_row_completion_of_finite_intersection g q r hq0 hfin
  refine ⟨T, q, targetThreeRows q s r, hq, hsq, hdelta, ?_, rfl, hfin⟩
  intro hdet
  apply hs
  simp [Matrix.det_fin_three, targetThreeRows] at hdet ⊢
  linear_combination -hdet

end RawProjectiveWeakBlowupTree

end OnLeConjecture.Analytic

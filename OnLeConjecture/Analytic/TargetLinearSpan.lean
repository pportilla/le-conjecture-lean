/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TargetPairLinearCompletion
public import OnLeConjecture.Analytic.GenericCurveCombinationOrder
public import OnLeConjecture.Analytic.SectionImageMultiplicity

/-!
# Linear target coordinates and orders on a section

An invertible target matrix preserves the complex linear span of the
component germs. The minimum order after restriction to a curve is therefore
unchanged. When the new first coordinate vanishes on that curve, this is
exactly the minimum order of its two plane image coordinates.
-/

public noncomputable section

open scoped BigOperators

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

theorem matrix_inverse_linear_combination {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0)
    (F : Fin n → V) (i : Fin n) :
    (∑ j, A⁻¹ i j • ∑ k, A j k • F k) = F i := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hinv := A.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hA)
  change (∑ k, (A⁻¹ * A) i k • F k) = _
  rw [hinv]
  simp [Matrix.one_apply]

theorem span_matrix_linear_combinations {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0) (F : Fin n → V) :
    Submodule.span ℂ (Set.range (fun i => ∑ j, A i j • F j)) =
      Submodule.span ℂ (Set.range F) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← matrix_inverse_linear_combination A hA F i]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))

/-- The prescribed finite pair can be made the first two coordinates while
retaining equality of the spans in both directions. -/
theorem exists_target_pair_with_span_eq
    (g : PointedMapGerm 2 3) (q r : Fin 3 → ℂ) (hq : q ≠ 0)
    (hfinite : PlaneCurve.HasFiniteIntersection
      (germLinearCombination g.1.component q) (germLinearCombination g.1.component r)) :
    ∃ f : PointedMapGerm 2 3, g.RightLeftEquivalent f ∧
      f.1.component 0 = germLinearCombination g.1.component q ∧
      f.1.component 1 = germLinearCombination g.1.component r ∧
      Submodule.span ℂ (Set.range f.1.component) =
        Submodule.span ℂ (Set.range g.1.component) := by
  obtain ⟨s, hs⟩ := exists_row_completion_of_finite_intersection g q r hq hfinite
  obtain ⟨e, he⟩ := exists_equiv_linear_matrix (targetThreeRows q r s) hs
  let f := e.forward.comp g
  have hf (i : Fin 3) : f.1.component i =
      germLinearCombination g.1.component (targetThreeRows q r s i) := by
    rw [PointedMapGerm.component_comp_eq_pullback, ← e.forward.pullback_coordinate i,
      he, map_sum]
    simp only [map_mul, PointedMapGerm.pullback_constRingHom, g.pullback_coordinate]
    rfl
  refine ⟨f, ?_, hf 0, hf 1, ?_⟩
  · refine ⟨PointedEquivGerm.identity 2, e, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
  · simp_rw [funext hf]
    exact span_matrix_linear_combinations _ hs _

theorem natCast_le_iInf_vanishingOrder_iff_span_le {ι : Type*}
    (F : ι → Germ 1) (m : ℕ) :
    ((m : ℕ∞) ≤ ⨅ i, vanishingOrder (F i)) ↔
      Submodule.span ℂ (Set.range F) ≤ (maximalIdeal 1 ^ m).restrictScalars ℂ := by
  simp only [le_iInf_iff, Submodule.span_le, Set.range_subset_iff]
  change (∀ i, (m : ℕ∞) ≤ vanishingOrder (F i)) ↔ ∀ i, F i ∈ maximalIdeal 1 ^ m
  simp only [mem_maximalIdeal_one_pow_iff]

/-- Minimum order depends only on the linear span of the curve germs. -/
theorem iInf_vanishingOrder_eq_of_span_eq {ι κ : Type*}
    (F : ι → Germ 1) (G : κ → Germ 1)
    (hspan : Submodule.span ℂ (Set.range F) = Submodule.span ℂ (Set.range G)) :
    (⨅ i, vanishingOrder (F i)) = ⨅ j, vanishingOrder (G j) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro m
  rw [natCast_le_iInf_vanishingOrder_iff_span_le,
    natCast_le_iInf_vanishingOrder_iff_span_le, hspan]

theorem iInf_pullback_order_eq_of_span_eq {ι κ : Type*}
    (γ : PointedMapGerm 1 2) (F : ι → Germ 2) (G : κ → Germ 2)
    (hspan : Submodule.span ℂ (Set.range F) = Submodule.span ℂ (Set.range G)) :
    (⨅ i, vanishingOrder (γ.pullbackRingHom (F i))) =
      ⨅ j, vanishingOrder (γ.pullbackRingHom (G j)) := by
  let L : Germ 2 →ₗ[ℂ] Germ 1 :=
    { toFun := γ.pullbackRingHom
      map_add' := map_add γ.pullbackRingHom
      map_smul' := γ.pullback_complex_smul }
  apply iInf_vanishingOrder_eq_of_span_eq
  have h := congrArg (Submodule.map L) hspan
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
    L, LinearMap.coe_mk, AddHom.coe_mk] using h

/-- A target linear form restricts to a linear form on the section plane.
The discarded term is a scalar multiple of the first component. -/
theorem exists_plane_linear_form_mod_first_component
    (f : PointedMapGerm 2 3) (u : Germ 2)
    (hu : u ∈ Submodule.span ℂ (Set.range f.1.component)) :
    ∃ c : Fin 2 → ℂ, ∃ a : ℂ,
      u = f.pullbackRingHom (hyperplaneExtension 2
        (germLinearCombination (coordinate : Fin 2 → Germ 2) c)) +
          a • f.1.component 0 := by
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu
  have htail (j : Fin 2) :
      (hyperplaneTailGerm 2).pullbackRingHom (coordinate j) = coordinate j.succ := by
    rw [PointedMapGerm.pullback_coordinate]
    apply Subtype.ext
    rfl
  refine ⟨fun j => r j.succ, r 0, ?_⟩
  rw [← hr]
  change (∑ i, r i • f.1.component i) =
    f.pullbackRingHom ((hyperplaneTailGerm 2).pullbackRingHom
      (∑ j : Fin 2, r j.succ • coordinate j)) + r 0 • f.1.component 0
  simp only [map_add, PointedMapGerm.pullback_complex_smul, htail,
    PointedMapGerm.pullback_coordinate, Fin.sum_univ_three, Fin.sum_univ_two]
  abel

/-- A change of target coordinates does not change the minimum branch
order. On the chosen section it equals the order of its plane image. -/
theorem sectionBranch_min_order_eq_original
    (g f : PointedMapGerm 2 3) (γ : PointedMapGerm 1 2)
    (hspan : Submodule.span ℂ (Set.range f.1.component) =
      Submodule.span ℂ (Set.range g.1.component))
    (hzero : γ.pullbackRingHom (f.1.component 0) = 0) :
    min (vanishingOrder ((f.sectionBranch γ).1.component 0))
        (vanishingOrder ((f.sectionBranch γ).1.component 1)) =
      ⨅ i, vanishingOrder (γ.pullbackRingHom (g.1.component i)) := by
  rw [← iInf_pullback_order_eq_of_span_eq γ f.1.component g.1.component hspan]
  exact (f.sectionBranch_min_component_order γ hzero).symm

end OnLeConjecture.Analytic

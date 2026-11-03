/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupGenericCompleteness

/-!
# Avoiding unrecorded exceptional-axis continuations

At any corner which is not a common weak basepoint, some weak generator
is a unit. Avoiding finitely many proper linear subspaces gives one open
coefficient set on which every such corner transform is a unit. Restricting
the actual transform identities to the old and new exceptional axes then
makes their terminal intersection orders equal to the vertex multiplicity.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- Unit generators in finitely many analytic families yield unit linear
combinations throughout a common nonempty open coefficient subset. -/
theorem exists_open_unit_linear_combinations
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (F : κ → ι → Germ 2) (hunit : ∀ k, ∃ i, IsUnit (F k i))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V, ∀ k, IsUnit (germLinearCombination (F k) q) := by
  classical
  let bad : κ → Submodule ℂ (ι → ℂ) := fun k =>
    ((maximalIdeal 2).restrictScalars ℂ).comap (germLinearCombination (F k))
  have hbad (k : κ) : bad k ≠ ⊤ := by
    obtain ⟨i, hi⟩ := hunit k
    intro htop
    have h : Pi.single i (1 : ℂ) ∈ bad k := by rw [htop]; trivial
    change germLinearCombination (F k) (Pi.single i 1) ∈ maximalIdeal 2 at h
    rw [germLinearCombination_single] at h
    exact (valueRingHom_ne_zero_of_isUnit hi) (mem_maximalIdeal_iff.mp h)
  let V : Set (ι → ℂ) := U ∩ ⋂ k, (bad k : Set (ι → ℂ))ᶜ
  have hVopen : IsOpen V := hU.inter (isOpen_iInter_of_finite (fun k =>
    (bad k).closed_of_finiteDimensional.isOpen_compl))
  obtain ⟨q₀, hq₀U, hq₀⟩ := exists_coefficients_avoiding_submodules_mem_open bad hbad U hU hUne
  refine ⟨V, hVopen, ⟨q₀, hq₀U, Set.mem_iInter.mpr hq₀⟩, fun _ h => h.1, ?_⟩
  intro q hq k
  apply isUnit_iff_valueRingHom_ne_zero.mpr
  intro hz
  exact (Set.mem_iInter.mp hq.2 k) (mem_maximalIdeal_iff.mpr hz)

namespace RawProjectiveWeakBlowupTree

open scoped BigOperators

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

/-- The two axis-continuation charts. The zero finite chart follows `x=0`,
and the complementary chart follows `y=0`. -/
@[expose] def cornerChart (b : Bool) : Option ℂ := if b then none else some 0

/-- Linear combinations satisfy the actual transform identity also at
projective points which are not recorded children. -/
theorem linearCombination_projective_transform_identity
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex) (t : Option ℂ) :
    (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
      ((projectiveChartSource t).forward.pullbackRingHom
        (germLinearCombination (T.generators p) q)) =
      coordinate (1 : Fin 2) ^ T.multiplicity p *
        germLinearCombination (projectiveWeakGenerators (T.multiplicity p)
          (T.generators p) (T.generator_mem p) t) q := by
  simp only [germLinearCombination, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    PointedMapGerm.pullback_complex_smul, projectiveWeakGenerators]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pointBlowupTransform_factor]
  exact (mul_smul_comm _ _ _).symm

omit [Fintype ι] in
/-- Every unrecorded corner has a unit weak generator, as a consequence
of completeness of the constructed weak-blowup tree. -/
theorem exists_unit_projectiveWeakGenerator_of_not_recorded
    (T : RawProjectiveWeakBlowupTree F) (p : T.Vertex) (t : Option ℂ)
    (ht : t ∉ (T.childFinset p).image T.chartPoint) :
    ∃ i, IsUnit (projectiveWeakGenerators (T.multiplicity p)
      (T.generators p) (T.generator_mem p) t i) := by
  classical
  by_contra! h
  have hzero : ∀ i, projectiveWeakGenerators (T.multiplicity p)
      (T.generators p) (T.generator_mem p) t i ∈ maximalIdeal 2 := by
    intro i
    rw [mem_maximalIdeal_iff]
    by_contra hne
    exact h i (isUnit_of_valueRingHom_ne_zero hne)
  exact ht ((T.mem_image_chartPoint_childFinset_iff p t).mpr hzero)

/-- Unrecorded continuation points on both coordinate axes are avoided
by every member of a common nonempty open coefficient subset. -/
theorem exists_open_unrecorded_corners_unit
    (T : RawProjectiveWeakBlowupTree F)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V, ∀ (p : T.Vertex) (b : Bool),
        cornerChart b ∉ (T.childFinset p).image T.chartPoint →
        IsUnit (germLinearCombination (projectiveWeakGenerators (T.multiplicity p)
          (T.generators p) (T.generator_mem p) (cornerChart b)) q) := by
  classical
  let K := {k : T.Vertex × Bool //
    cornerChart k.2 ∉ (T.childFinset k.1).image T.chartPoint}
  let A : K → ι → Germ 2 := fun k => projectiveWeakGenerators (T.multiplicity k.val.1)
    (T.generators k.val.1) (T.generator_mem k.val.1) (cornerChart k.val.2)
  have hunit (k : K) : ∃ i, IsUnit (A k i) :=
    T.exists_unit_projectiveWeakGenerator_of_not_recorded k.val.1 (cornerChart k.val.2) k.property
  obtain ⟨V, hVopen, hVne, hVU, hV⟩ := exists_open_unit_linear_combinations A hunit U hU hUne
  exact ⟨V, hVopen, hVne, hVU, fun q hq p b ht => hV q hq ⟨(p, b), ht⟩⟩

/-- A unit transform in the zero chart exhausts the intersection with
`x=0`: the original axis intersection equals the divided-out order. -/
theorem oldAxisOrder_eq_multiplicity_of_zero_transform_unit
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex)
    (hunit : IsUnit (germLinearCombination (projectiveWeakGenerators (T.multiplicity p)
      (T.generators p) (T.generator_mem p) (some 0)) q)) :
    T.oldAxisOrder q p = T.multiplicity p := by
  have h := T.linearCombination_projective_transform_identity q p (some 0)
  simp only [projectiveChartCenter, projectiveChartSource, PointedEquivGerm.identity_forward,
    PointedMapGerm.pullbackRingHom_identity, RingHom.id_apply] at h
  have hr := congrArg (hyperplaneRestriction 1) h
  have hy : hyperplaneRestriction 1 (coordinate (1 : Fin 2)) = coordinate (0 : Fin 1) :=
    hyperplaneRestriction_coordinate_succ 1 0
  rw [hyperplaneRestriction_pointBlowupChart_zero, map_mul, map_pow, hy] at hr
  unfold oldAxisOrder
  rw [hr, vanishingOrder_mul, vanishingOrder_coordinate_pow,
    vanishingOrder_eq_zero_iff_isUnit.mpr (hunit.map (hyperplaneRestriction 1)),
    add_zero, ENat.toNat_natCast]

/-- A unit transform in the complementary chart exhausts the
intersection with `y=0`. -/
theorem newestAxisOrder_eq_multiplicity_of_complementary_transform_unit
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex)
    (hunit : IsUnit (germLinearCombination (projectiveWeakGenerators (T.multiplicity p)
      (T.generators p) (T.generator_mem p) none) q)) :
    T.newestAxisOrder q p = T.multiplicity p := by
  have h := T.linearCombination_projective_transform_identity q p none
  simp only [projectiveChartCenter, projectiveChartSource] at h
  have hr := congrArg (hyperplaneRestriction 1) h
  have hy : hyperplaneRestriction 1 (coordinate (1 : Fin 2)) = coordinate (0 : Fin 1) :=
    hyperplaneRestriction_coordinate_succ 1 0
  rw [complementaryBlowupChart_secondAxisRestriction, map_mul, map_pow, hy] at hr
  unfold newestAxisOrder
  rw [hr, vanishingOrder_mul, vanishingOrder_coordinate_pow,
    vanishingOrder_eq_zero_iff_isUnit.mpr (hunit.map (hyperplaneRestriction 1)),
    add_zero, ENat.toNat_natCast]

/-- The absence of a recorded continuation forces the exact terminal
axis intersection on one common nonempty open coefficient set. -/
theorem exists_open_exact_axis_endpoints
    (T : RawProjectiveWeakBlowupTree F)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V, ∀ p : T.Vertex,
        (some 0 ∉ (T.childFinset p).image T.chartPoint →
          T.oldAxisOrder q p = T.multiplicity p) ∧
        (none ∉ (T.childFinset p).image T.chartPoint →
          T.newestAxisOrder q p = T.multiplicity p) := by
  obtain ⟨V, hVopen, hVne, hVU, hV⟩ := T.exists_open_unrecorded_corners_unit U hU hUne
  refine ⟨V, hVopen, hVne, hVU, fun q hq p => ⟨?_, ?_⟩⟩
  · intro ht
    exact T.oldAxisOrder_eq_multiplicity_of_zero_transform_unit q p (hV q hq p false ht)
  · intro ht
    exact T.newestAxisOrder_eq_multiplicity_of_complementary_transform_unit q p
      (hV q hq p true ht)

end RawProjectiveWeakBlowupTree

end OnLeConjecture.Analytic

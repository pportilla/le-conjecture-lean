/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationLaurentComparison
public import OnLeConjecture.KnotFloer.GridFullStabilizationXBlocking
public import OnLeConjecture.KnotFloer.GridXBlockedCrossingHomotopy

/-!
# The stabilization comparison with only the new X markings blocked

The off-center submodule is preserved when the two new X squares are blocked.
The derivative crossing the second new X, while avoiding the first, is a chain map
from that off-center differential to the old differential with its split X blocked.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R]

/-- Include the Laurent off-center generators as stabilized states. -/
noncomputable def laurentOffCenterInclusion :
    (G.StabilizeXOffCenterState s →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R]
      LaurentChain R (n + 1) :=
  Finsupp.lmapDomain (LaurentPolynomial R) (LaurentPolynomial R) Subtype.val

/-- Restrict a stabilized Laurent chain to its off-center generators. -/
noncomputable def laurentOffCenterProjection : LaurentChain R (n + 1) →ₗ[LaurentPolynomial R]
    (G.StabilizeXOffCenterState s →₀ LaurentPolynomial R) :=
  Finsupp.lcomapDomain _ Subtype.val_injective

@[simp]
theorem laurentOffCenterInclusion_single (y : G.StabilizeXOffCenterState s)
    (a : LaurentPolynomial R) :
    laurentOffCenterInclusion G s R (single y a) = single y.val a :=
  Finsupp.mapDomain_single

@[simp]
theorem laurentOffCenterProjection_apply (c : LaurentChain R (n + 1))
    (y : G.StabilizeXOffCenterState s) :
    laurentOffCenterProjection G s R c y = c y.val := rfl

/-- The off-center projection retracts its inclusion. -/
theorem laurentOffCenterProjection_inclusion
    (c : G.StabilizeXOffCenterState s →₀ LaurentPolynomial R) :
    laurentOffCenterProjection G s R (laurentOffCenterInclusion G s R c) = c :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ _ c

/-- The off-center inclusion is injective. -/
theorem laurentOffCenterInclusion_injective :
    Function.Injective (laurentOffCenterInclusion G s R) :=
  Function.LeftInverse.injective (laurentOffCenterProjection_inclusion G s R)

/-- Restricting and including recovers every chain whose center coefficients vanish. -/
theorem laurentOffCenterInclusion_projection_of_center_zero (c : LaurentChain R (n + 1))
    (hc : laurentStabilizationCenterProjection G s R c = 0) :
    laurentOffCenterInclusion G s R (laurentOffCenterProjection G s R c) = c := by
  classical
  apply Finsupp.ext
  intro y
  by_cases hy : y s.succ ≠ (G.X s).succ
  · exact Finsupp.mapDomain_apply Subtype.val_injective _ ⟨y, hy⟩
  · obtain ⟨x, rfl⟩ := GridState.exists_insertPoint_eq (not_ne_iff.mp hy)
    have hzero := congrArg (fun c => c x) hc
    simp only [laurentStabilizationCenterProjection_apply, Finsupp.zero_apply] at hzero
    rw [hzero]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨z, hz⟩
    exact z.2 (hz ▸ GridState.insertPoint_apply_newColumn _ _ _)

/-- The two-new-X-blocked off-center differential. -/
noncomputable def localComparisonOffCenterDifferential :
    Module.End (LaurentPolynomial R) (G.StabilizeXOffCenterState s →₀ LaurentPolynomial R) :=
  laurentOffCenterProjection G s R ∘ₗ
    laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ} ∘ₗ laurentOffCenterInclusion G s R

/-- The off-center inclusion intertwines the actual partially blocked differentials. -/
theorem localComparisonOffCenterInclusion_chain :
    laurentOffCenterInclusion G s R ∘ₗ localComparisonOffCenterDifferential G s R =
      laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
        R {s.castSucc, s.succ} ∘ₗ laurentOffCenterInclusion G s R := by
  classical
  apply Finsupp.lhom_ext'
  intro y
  apply LinearMap.ext_ring
  change laurentOffCenterInclusion G s R (laurentOffCenterProjection G s R
    (laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ} (laurentOffCenterInclusion G s R (single y 1)))) = _
  apply laurentOffCenterInclusion_projection_of_center_zero
  apply Finsupp.ext
  intro x
  rw [laurentStabilizationCenterProjection_apply, laurentOffCenterInclusion_single]
  exact laurentXBlocked_stabilization_offCenter_to_center G s R y.2 (by simp)

/-- Cross the second new X while retaining the block at the first new X. -/
noncomputable def localComparisonCrossing :
    Module.End (LaurentPolynomial R) (LaurentChain R (n + 1)) :=
  xBlockedCrossingHomotopy (G.stabilizeX s.castSucc (G.X s).castSucc s)
    R {s.castSucc} s.succ

/-- The actual off-center-to-center crossing comparison. -/
noncomputable def localComparisonOffCenterToCenter :
    (G.StabilizeXOffCenterState s →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R]
      LaurentChain R n :=
  laurentStabilizationCenterProjection G s R ∘ₗ localComparisonCrossing G s R ∘ₗ
    laurentOffCenterInclusion G s R

variable [CharP R 2]

/-- The restricted off-center differential squares to zero. -/
theorem localComparisonOffCenterDifferential_comp_self :
    localComparisonOffCenterDifferential G s R ∘ₗ
      localComparisonOffCenterDifferential G s R = 0 := by
  apply LinearMap.ext
  intro c
  apply laurentOffCenterInclusion_injective G s R
  have hc := LinearMap.congr_fun (localComparisonOffCenterInclusion_chain G s R)
  simp only [LinearMap.comp_apply] at hc
  rw [LinearMap.comp_apply, hc, hc]
  have hs := LinearMap.congr_fun (laurentXBlockedDifferential_comp_self
    (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ})
    (laurentOffCenterInclusion G s R c)
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using hs

/-- The crossing map commutes with the differential blocking both new X markings. -/
theorem localComparisonCrossing_chain :
    laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
        R {s.castSucc, s.succ} ∘ₗ localComparisonCrossing G s R +
      localComparisonCrossing G s R ∘ₗ
        laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
          R {s.castSucc, s.succ} = 0 := by
  simpa only [localComparisonCrossing, Finset.pair_comm] using
    xBlockedCrossingHomotopy_insert_chain
      (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc} s.succ


/-- The concrete crossing component intertwines the two partially blocked differentials. -/
theorem localComparisonOffCenterToCenter_chain :
    localComparisonOffCenterToCenter G s R ∘ₗ localComparisonOffCenterDifferential G s R =
      laurentXBlockedDifferential G R {s} ∘ₗ localComparisonOffCenterToCenter G s R := by
  apply LinearMap.ext
  intro c
  have hh := LinearMap.congr_fun (localComparisonCrossing_chain G s R)
    (laurentOffCenterInclusion G s R c)
  have h := congrArg (laurentStabilizationCenterProjection G s R) hh
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    map_add, map_zero] at h
  have hN := LinearMap.congr_fun (localComparisonOffCenterInclusion_chain G s R) c
  have hI := LinearMap.congr_fun (laurentStabilizationCenterProjection_xBlocked_chain G s R)
    (localComparisonCrossing G s R (laurentOffCenterInclusion G s R c))
  simp only [LinearMap.comp_apply] at hN hI
  rw [hI, ← hN] at h
  apply Finsupp.ext
  intro y
  have hy := congrArg (fun f => f y) h
  exact (CharTwo.add_eq_zero.mp hy).symm

/-- The comparison cone counting arbitrary other X crossings. -/
noncomputable def localComparisonCone : Module.End (LaurentPolynomial R)
    (ReducedConeLaurentChain G s R) :=
  LinearMap.sumMappingCone (localComparisonOffCenterDifferential G s R)
    (laurentXBlockedDifferential G R {s}) (localComparisonOffCenterToCenter G s R)

/-- The partially blocked comparison cone is an actual differential. -/
theorem localComparisonCone_comp_self :
    localComparisonCone G s R ∘ₗ localComparisonCone G s R = 0 :=
  LinearMap.sumMappingCone_comp_self
    (localComparisonOffCenterDifferential_comp_self G s R)
    (laurentXBlockedDifferential_comp_self G R {s})
    (localComparisonOffCenterToCenter_chain G s R)


/-- Rectangles in the comparison with only the two newly created X markings blocked. -/
noncomputable def localComparisonRectangles :
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n) →
    Finset (GridRectangleBetween (comparisonConeState G s i) (comparisonConeState G s j))
  | .inl y, .inl z =>
      (GridRectangleBetween.emptyRectangles y.val z.val).filter (fun r =>
        (s.castSucc, (G.stabilizeX s.castSucc (G.X s).castSucc s).X s.castSucc) ∉
          r.toGridRectangle.coveredSquares ∧
        (s.succ, (G.stabilizeX s.castSucc (G.X s).castSucc s).X s.succ) ∉
          r.toGridRectangle.coveredSquares)
  | .inl y, .inr x =>
      (GridRectangleBetween.emptyRectangles y.val (x.insertPoint s.succ (G.X s).succ)).filter
        (fun r => (s.succ, (G.stabilizeX s.castSucc (G.X s).castSucc s).X s.succ) ∈
          r.toGridRectangle.coveredSquares ∧
          (s.castSucc, (G.stabilizeX s.castSucc (G.X s).castSucc s).X s.castSucc) ∉
          r.toGridRectangle.coveredSquares)
  | .inr _, .inl _ => ∅
  | .inr x, .inr y =>
      GridRectangleBetween.emptyRectangles (x.insertPoint s.succ (G.X s).succ)
        (y.insertPoint s.succ (G.X s).succ)

/-- The partially blocked cone has exactly these weighted rectangle coefficients. -/
theorem localComparisonCone_single_apply
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n) :
    localComparisonCone G s R (single i 1) j =
      ∑ r ∈ localComparisonRectangles G s i j,
        LaurentPolynomial.T
          (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℤ) := by
  classical
  rcases i with i | i <;> rcases j with j | j
  · rw [localComparisonCone, LinearMap.sumMappingCone_single_inl_apply_inl]
    simp only [localComparisonOffCenterDifferential, LinearMap.comp_apply,
      laurentOffCenterProjection_apply, laurentOffCenterInclusion_single,
      laurentXBlockedDifferential_apply_apply, Finsupp.sum_single_index, one_mul,
      zero_mul, CharTwo.neg_eq, Finset.mem_insert, Finset.mem_singleton,
      exists_eq_or_imp, exists_eq_left, not_or, localComparisonRectangles, comparisonConeState]
    rfl
  · rw [localComparisonCone, LinearMap.sumMappingCone_single_inl_apply_inr]
    simp only [localComparisonOffCenterToCenter, LinearMap.comp_apply,
      laurentStabilizationCenterProjection_apply, laurentOffCenterInclusion_single,
      localComparisonCrossing, xBlockedCrossingHomotopy_apply_apply,
      Finsupp.sum_single_index, one_mul, zero_mul, Finset.mem_singleton,
      exists_eq_left, localComparisonRectangles, comparisonConeState]
    rfl
  · simp [localComparisonCone, localComparisonRectangles]
  · rw [localComparisonCone, LinearMap.sumMappingCone_single_inr_apply_inr,
      ← laurentXBlocked_stabilization_center_eq_old G s R,
      laurentXBlocked_stabilization_center_coefficient, laurentCoefficient_eq]
    rfl

omit [CommRing R] [CharP R 2] in
/-- All previously X-avoiding comparison rectangles survive the partial unblocking. -/
theorem comparisonConeRectangles_subset_localComparisonRectangles
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n) :
    comparisonConeRectangles G s i j ⊆ localComparisonRectangles G s i j := by
  classical
  intro r hr
  rcases i with i | i <;> rcases j with j | j
  · refine Finset.mem_filter.mpr ⟨
      (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedRectangles_subset_emptyRectangles
        i.val j.val hr, ?_⟩
    let H := G.stabilizeX s.castSucc (G.X s).castSucc s
    exact ⟨H.X_notMem_toGridRectangle_coveredSquares_of_mem_unblockedRectangles hr s.castSucc,
      H.X_notMem_toGridRectangle_coveredSquares_of_mem_unblockedRectangles hr s.succ⟩
  · have h := ((G.stabilizeX s.castSucc (G.X s).castSucc s).mem_XHomotopyRectangles s.succ r).mp hr
    refine Finset.mem_filter.mpr ⟨(GridRectangleBetween.mem_emptyRectangles r).mpr h.1, ?_, ?_⟩
    · have hp : (s.succ, (G.stabilizeX s.castSucc (G.X s).castSucc s).X s.succ) ∈
          r.toGridRectangle.coveredSquares ∩
            (G.stabilizeX s.castSucc (G.X s).castSucc s).XSet := by
        rw [h.2]
        exact Finset.mem_singleton_self _
      exact (Finset.mem_inter.mp hp).1
    · intro hp
      have hp' := Finset.mem_inter.mpr ⟨hp,
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).mk_mem_XSet _ _).mpr rfl⟩
      rw [h.2, Finset.mem_singleton, Prod.mk.injEq] at hp'
      exact Fin.castSucc_lt_succ.ne hp'.1
  · exact False.elim (Finset.notMem_empty r hr)
  · exact (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedRectangles_subset_emptyRectangles
      _ _ hr


omit [CommRing R] [CharP R 2] in
/-- The cone Maslov grading is the stabilized-state Maslov grading in both summands. -/
theorem reducedConeMaslov_eq_comparisonConeState
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    reducedConeMaslov G s i =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ (comparisonConeState G s i) := by
  cases i with
  | inl i => rfl
  | inr i => exact (G.maslovOℤ_stabilizeX_insertPoint s i).symm

omit [CommRing R] [CharP R 2] in
/-- Every locally counted rectangle is empty, hence has the required Maslov degree. -/
theorem localComparisonRectangles_maslov
    {i j : G.StabilizeXOffCenterState s ⊕ GridState n}
    {r : GridRectangleBetween (comparisonConeState G s i) (comparisonConeState G s j)}
    (hr : r ∈ localComparisonRectangles G s i j) :
    reducedConeMaslov G s j -
        2 * (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℤ) =
      reducedConeMaslov G s i - 1 := by
  have he : r.IsEmpty := by
    rcases i with i | i <;> rcases j with j | j
    · exact (GridRectangleBetween.mem_emptyRectangles r).mp (Finset.mem_filter.mp hr).1
    · exact (GridRectangleBetween.mem_emptyRectangles r).mp (Finset.mem_filter.mp hr).1
    · exact False.elim (Finset.notMem_empty r hr)
    · exact (GridRectangleBetween.mem_emptyRectangles r).mp hr
  rw [reducedConeMaslov_eq_comparisonConeState, reducedConeMaslov_eq_comparisonConeState]
  exact (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ_sub_two_mul_card_OColumns he

omit [CommRing R] [CharP R 2] in
private theorem one_le_XCount_of_not_unblocked {m : ℕ} (H : GridDiagram m)
    {x y : GridState m} (r : GridRectangleBetween x y) (he : r.IsEmpty)
    (hn : r ∉ H.unblockedRectangles x y) :
    1 ≤ (r.toGridRectangle.coveredSquares ∩ H.XSet).card := by
  apply Finset.card_pos.mpr
  by_contra hz
  apply hn
  apply (H.mem_unblockedRectangles r).mpr
  exact ⟨he, Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hz)⟩

omit [CommRing R] [CharP R 2] in
/-- Every newly admitted comparison rectangle strictly lowers the shifted Alexander coordinate. -/
theorem localComparisonRectangles_extra_alexander
    {i j : G.StabilizeXOffCenterState s ⊕ GridState n}
    {r : GridRectangleBetween (comparisonConeState G s i) (comparisonConeState G s j)}
    (hr : r ∈ localComparisonRectangles G s i j)
    (hn : r ∉ comparisonConeRectangles G s i j) :
    reducedConeAlexander G s j -
        (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℚ) ≤
      reducedConeAlexander G s i - 1 := by
  let H := G.stabilizeX s.castSucc (G.X s).castSucc s
  have hA := H.alexander_sub_alexander_eq_card_sub_card r
  rw [← H.card_OColumns r.toGridRectangle, Finset.inter_comm H.XSet] at hA
  rcases i with i | i <;> rcases j with j | j
  · have he := (GridRectangleBetween.mem_emptyRectangles r).mp (Finset.mem_filter.mp hr).1
    have hcount : (1 : ℚ) ≤ (r.toGridRectangle.coveredSquares ∩ H.XSet).card := by
      exact_mod_cast one_le_XCount_of_not_unblocked H r he hn
    change H.alexander i.val - H.alexander j.val = _ at hA
    dsimp only [reducedConeAlexander]
    linarith only [hA, hcount]
  · obtain ⟨he, hb, _⟩ := Finset.mem_filter.mp hr
    have he' := (GridRectangleBetween.mem_emptyRectangles r).mp he
    have hb' : (s.succ, H.X s.succ) ∈ r.toGridRectangle.coveredSquares ∩ H.XSet :=
      Finset.mem_inter.mpr ⟨hb, (H.mk_mem_XSet _ _).mpr rfl⟩
    have hneq : r.toGridRectangle.coveredSquares ∩ H.XSet ≠ {(s.succ, H.X s.succ)} := by
      intro h
      exact hn ((H.mem_XHomotopyRectangles s.succ r).mpr ⟨he', h⟩)
    have hcountNat : 2 ≤ (r.toGridRectangle.coveredSquares ∩ H.XSet).card := by
      by_contra hsmall
      have hle : (r.toGridRectangle.coveredSquares ∩ H.XSet).card ≤ 1 := by omega
      have hsub := Finset.card_le_one.mp hle
      apply hneq
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hb', fun q hq => hsub q hq _ hb'⟩
    have hcount : (2 : ℚ) ≤ (r.toGridRectangle.coveredSquares ∩ H.XSet).card := by
      exact_mod_cast hcountNat
    change H.alexander i.val - H.alexander (j.insertPoint s.succ (G.X s).succ) = _ at hA
    rw [G.alexander_stabilizeX_insertPoint] at hA
    dsimp only [reducedConeAlexander]
    linarith only [hA, hcount]
  · exact False.elim (Finset.notMem_empty r hr)
  · have he := (GridRectangleBetween.mem_emptyRectangles r).mp hr
    have hcount : (1 : ℚ) ≤ (r.toGridRectangle.coveredSquares ∩ H.XSet).card := by
      exact_mod_cast one_le_XCount_of_not_unblocked H r he hn
    change H.alexander (i.insertPoint s.succ (G.X s).succ) -
      H.alexander (j.insertPoint s.succ (G.X s).succ) = _ at hA
    rw [G.alexander_stabilizeX_insertPoint, G.alexander_stabilizeX_insertPoint] at hA
    dsimp only [reducedConeAlexander]
    linarith only [hA, hcount]

end OnLeConjecture.KnotFloer.GridFull

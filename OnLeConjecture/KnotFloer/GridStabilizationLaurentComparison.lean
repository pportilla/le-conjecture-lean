/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationLaurentReduced
public import OnLeConjecture.External.TauCeti.Algebra.Homology.Contraction.Perturbation

/-!
# The Laurent stabilization comparison cone

The comparison cone counts X-avoiding rectangles within the two summands and
rectangles through the designated new X from the off-center to the center summand.
Its positive-O terms are a perturbation of the constructed reduced contraction.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The underlying stabilized state of a comparison-cone generator. -/
noncomputable def comparisonConeState : G.StabilizeXOffCenterState s ⊕ GridState n →
    GridState (n + 1)
  | .inl y => y.val
  | .inr x => x.insertPoint s.succ (G.X s).succ

/-- The rectangles counted by the comparison cone, before the O weights are applied. -/
noncomputable def comparisonConeRectangles :
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n) →
    Finset (GridRectangleBetween (comparisonConeState G s i) (comparisonConeState G s j))
  | .inl y, .inl z =>
      (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedRectangles y.val z.val
  | .inl y, .inr x =>
      (G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopyRectangles s.succ y.val
        (x.insertPoint s.succ (G.X s).succ)
  | .inr _, .inl _ => ∅
  | .inr x, .inr y =>
      (G.stabilizeX s.castSucc (G.X s).castSucc s).unblockedRectangles
        (x.insertPoint s.succ (G.X s).succ) (y.insertPoint s.succ (G.X s).succ)

variable (R : Type*) [CommRing R]

/-- The polynomial comparison cone supplied by the checked rectangle chain-map identity. -/
noncomputable def polynomialComparisonCone :
    Module.End (MvPolynomial (Fin (n + 1)) R)
      (G.StabilizeXOffCenterState s ⊕ GridState n →₀ MvPolynomial (Fin (n + 1)) R) :=
  LinearMap.sumMappingCone (G.stabilizeXOffCenterDifferential s R)
    (G.stabilizeXCenterDifferential s R) (G.stabilizeXOffCenterToCenter s R)

/-- Collapse its polynomial variables to the Laurent variable. -/
noncomputable def laurentComparisonCone : Module.End (LaurentPolynomial R)
    (ReducedConeLaurentChain G s R) :=
  coefficientExtension (laurentSpecialization R).toRingHom (polynomialComparisonCone G s R)

/-- The polynomial cone reduces to the previously constructed reduced differential. -/
theorem polynomialComparisonCone_constantCoeff :
    (polynomialComparisonCone G s R).constantCoeffReduction = G.stabilizeXReducedCone s R := by
  classical
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro j
  change (polynomialComparisonCone G s R).constantCoeffReduction (single i 1) j =
    G.stabilizeXReducedCone s R (single i 1) j
  rw [LinearMap.constantCoeffReduction_single_apply, one_mul]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [polynomialComparisonCone, GridDiagram.stabilizeXReducedCone]

variable [CharP R 2]

/-- The Laurent comparison differential is square zero by specialization of the proved cone. -/
theorem laurentComparisonCone_comp_self :
    laurentComparisonCone G s R ∘ₗ laurentComparisonCone G s R = 0 := by
  have hpoly : polynomialComparisonCone G s R ∘ₗ polynomialComparisonCone G s R = 0 :=
    LinearMap.sumMappingCone_comp_self
      (G.stabilizeXOffCenterDifferential_comp_self_eq_zero s R)
      (G.stabilizeXCenterDifferential_comp_self_eq_zero s R)
      (G.stabilizeXOffCenterToCenter_comp_offCenterDifferential s R)
  have h := congrArg (coefficientExtensionRingHom (laurentSpecialization R).toRingHom) hpoly
  simpa only [← Module.End.mul_eq_comp, map_mul, map_zero,
    coefficientExtensionRingHom_apply, laurentComparisonCone] using h

/-- Its polynomial matrix entries are the indicated rectangle weights in characteristic two. -/
theorem polynomialComparisonCone_single_apply
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n) :
    polynomialComparisonCone G s R (single i 1) j =
      ∑ r ∈ comparisonConeRectangles G s i j,
        (G.stabilizeX s.castSucc (G.X s).castSucc s).OMonomial R r.toGridRectangle := by
  rcases i with i | i <;> rcases j with j | j
  · rw [polynomialComparisonCone, LinearMap.sumMappingCone_single_inl_apply_inl,
      GridDiagram.stabilizeXOffCenterDifferential_single_apply]
    simp only [comparisonConeRectangles, comparisonConeState,
      GridDiagram.unblockedCoefficient_def, CharTwo.neg_eq]
  · rw [polynomialComparisonCone, LinearMap.sumMappingCone_single_inl_apply_inr,
      GridDiagram.stabilizeXOffCenterToCenter_single_apply]
    simp only [GridDiagram.XHomotopyCoefficient_def, comparisonConeRectangles,
      comparisonConeState]
  · simp [polynomialComparisonCone, comparisonConeRectangles]
  · rw [polynomialComparisonCone, LinearMap.sumMappingCone_single_inr_apply_inr,
      GridDiagram.stabilizeXCenterDifferential_single_apply,
      ← GridDiagram.unblockedCoefficient_stabilizeX_insertPoint]
    simp only [GridDiagram.unblockedCoefficient_def, comparisonConeRectangles,
      comparisonConeState]

/-- The Laurent matrix coefficient records the number of O markings in each counted rectangle. -/
theorem laurentComparisonCone_single_apply
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n) :
    laurentComparisonCone G s R (single i 1) j =
      ∑ r ∈ comparisonConeRectangles G s i j,
        LaurentPolynomial.T
          (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℤ) := by
  rw [laurentComparisonCone, coefficientExtension_single_apply, one_mul,
    polynomialComparisonCone_single_apply]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sum,
    laurentSpecialization_OMonomial]


omit [CommRing R] [CharP R 2] in
/-- The O-weighted comparison rectangles have the cone's stated Maslov and Alexander shifts. -/
theorem comparisonConeRectangles_grading
    {i j : G.StabilizeXOffCenterState s ⊕ GridState n}
    {r : GridRectangleBetween (comparisonConeState G s i) (comparisonConeState G s j)}
    (hr : r ∈ comparisonConeRectangles G s i j) :
    reducedConeMaslov G s j -
        2 * (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℤ) =
      reducedConeMaslov G s i - 1 ∧
    reducedConeAlexander G s j -
        (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℚ) =
      reducedConeAlexander G s i := by
  rcases i with i | i <;> rcases j with j | j
  · exact ⟨(G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ_sub_two_mul_card_OColumns
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).isEmpty_of_mem_unblockedRectangles hr),
      (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander_sub_card_OColumns_eq_alexander
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).disjoint_XSet_of_mem_unblockedRectangles hr)⟩
  · have hempty := ((G.stabilizeX s.castSucc (G.X s).castSucc s).mem_XHomotopyRectangles
      s.succ r).mp hr |>.1
    have hM := G.maslovOℤ_stabilizeX_eq_of_isEmpty s j hempty
    have hA := G.alexander_stabilizeX_eq_of_mem_XHomotopyRectangles s j hr
    dsimp only [reducedConeMaslov, reducedConeAlexander]
    refine ⟨?_, hA.symm⟩
    calc
      _ = (G.maslovOℤ j - 2 * (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
        r.toGridRectangle).card : ℤ)) - 1 := by omega
      _ = _ := congrArg (fun q : ℤ => q - 1) hM.symm
  · exact False.elim (Finset.notMem_empty r hr)
  · have hM := (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ_sub_two_mul_card_OColumns
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).isEmpty_of_mem_unblockedRectangles hr)
    have hA := (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander_sub_card_OColumns_eq_alexander
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).disjoint_XSet_of_mem_unblockedRectangles hr)
    rw [G.maslovOℤ_stabilizeX_insertPoint, G.maslovOℤ_stabilizeX_insertPoint] at hM
    rw [G.alexander_stabilizeX_insertPoint, G.alexander_stabilizeX_insertPoint] at hA
    dsimp only [reducedConeMaslov, reducedConeAlexander]
    have hA' : G.alexander j - 1 -
        (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℚ) =
        G.alexander i - 1 := hA
    exact ⟨hM, by linarith only [hA']⟩

/-- The reduced matrix counts exactly the comparison rectangles carrying no O markings. -/
theorem laurentReducedConeDifferential_single_apply
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n) :
    laurentReducedConeDifferential G s R (single i 1) j =
      (((comparisonConeRectangles G s i j).filter fun r =>
        (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle = ∅).card :
          LaurentPolynomial R) := by
  rw [laurentReducedConeDifferential, coefficientExtension_single_apply, one_mul,
    ← polynomialComparisonCone_constantCoeff G s R,
    LinearMap.constantCoeffReduction_single_apply, one_mul,
    polynomialComparisonCone_single_apply, GridDiagram.constantCoeff_sum_OMonomial, map_natCast]

/-- The terms with positive O count, as a difference of the two actual differentials. -/
noncomputable def positiveOComparisonPerturbation : Module.End (LaurentPolynomial R)
    (ReducedConeLaurentChain G s R) :=
  laurentComparisonCone G s R - laurentReducedConeDifferential G s R

/-- The difference contains precisely the positive-O rectangle terms. -/
theorem positiveOComparisonPerturbation_single_apply
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n) :
    positiveOComparisonPerturbation G s R (single i 1) j =
      ∑ r ∈ (comparisonConeRectangles G s i j).filter (fun r =>
        (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle ≠ ∅),
        LaurentPolynomial.T
          (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℤ) := by
  classical
  rw [positiveOComparisonPerturbation, LinearMap.sub_apply, Finsupp.sub_apply,
    laurentComparisonCone_single_apply, laurentReducedConeDifferential_single_apply]
  rw [← Finset.sum_filter_add_sum_filter_not (comparisonConeRectangles G s i j)
    (fun r => (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle = ∅)]
  have hzero :
      (∑ r ∈ (comparisonConeRectangles G s i j).filter (fun r =>
        (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle = ∅),
        (LaurentPolynomial.T
          (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℤ) :
            LaurentPolynomial R)) =
      (((comparisonConeRectangles G s i j).filter (fun r =>
        (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle = ∅)).card :
          LaurentPolynomial R) := by
    calc
      _ = ∑ r ∈ (comparisonConeRectangles G s i j).filter (fun r =>
        (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle = ∅),
          (1 : LaurentPolynomial R) := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [(Finset.mem_filter.mp hr).2]
      _ = _ := by simp
  rw [hzero, add_sub_cancel_left]

omit [CharP R 2] in
/-- Adding the positive-O part recovers the weighted comparison differential. -/
theorem reduced_add_positiveOComparisonPerturbation :
    laurentReducedConeDifferential G s R + positiveOComparisonPerturbation G s R =
      laurentComparisonCone G s R := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro i
  change laurentReducedConeDifferential G s R c i +
    (laurentComparisonCone G s R c i - laurentReducedConeDifferential G s R c i) = _
  exact add_sub_cancel _ _


/-- Every nonzero perturbation term comes from a rectangle with positive O count. -/
theorem positiveOComparisonPerturbation_support (c : ReducedConeLaurentChain G s R)
    {j : G.StabilizeXOffCenterState s ⊕ GridState n} {k : ℤ}
    (hk : k ∈ (positiveOComparisonPerturbation G s R c j).coeff.support) :
    ∃ i, ∃ t ∈ (c i).coeff.support,
      ∃ r ∈ comparisonConeRectangles G s i j,
        (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle ≠ ∅ ∧
        k = t + (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          r.toGridRectangle).card : ℤ) := by
  classical
  rw [finiteEnd_apply_apply, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨t, ht, d, hd, htd⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hi)
  rw [positiveOComparisonPerturbation_single_apply, AddMonoidAlgebra.coeff_sum] at hd
  obtain ⟨r, hr, hdr⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hd)
  obtain ⟨hr, hO⟩ := Finset.mem_filter.mp hr
  change d ∈ (single
    (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℤ)
    (1 : R)).support at hdr
  have hd0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hdr)
  exact ⟨i, t, ht, r, hr, hO, by rw [← hd0]; exact htd.symm⟩

/-- Restoring positive O weights lowers Maslov degree by one. -/
theorem positiveOComparisonPerturbation_mem_maslovPiece {m : ℤ}
    {c : ReducedConeLaurentChain G s R} (hc : c ∈ laurentReducedConeMaslovPiece G s R m) :
    positiveOComparisonPerturbation G s R c ∈ laurentReducedConeMaslovPiece G s R (m - 1) := by
  intro j k hk
  obtain ⟨i, t, ht, r, hr, _, hkt⟩ := positiveOComparisonPerturbation_support G s R c hk
  have hm := hc i t ht
  have hM := (comparisonConeRectangles_grading G s hr).1
  omega

/-- The positive-O perturbation strictly lowers the first coordinate and preserves Alexander. -/
theorem positiveOComparisonPerturbation_mem_bifiltrationLevel {u v : ℚ}
    {c : ReducedConeLaurentChain G s R}
    (hc : c ∈ laurentReducedConeBifiltrationLevel G s R u v) :
    positiveOComparisonPerturbation G s R c ∈
      laurentReducedConeBifiltrationLevel G s R (u - 1) v := by
  intro j k hk
  obtain ⟨i, t, ht, r, hr, hO, hkt⟩ := positiveOComparisonPerturbation_support G s R c hk
  obtain ⟨hfirst, hsecond⟩ := hc i t ht
  have hA := (comparisonConeRectangles_grading G s hr).2
  have hcount : (1 : ℚ) ≤
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hO)
  have hkt' : (k : ℚ) = t +
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card := by
    exact_mod_cast hkt
  constructor <;> linarith

omit [CharP R 2] in
/-- The Laurent generator with exponent zero has its basis Maslov degree. -/
theorem single_one_mem_laurentReducedConeMaslovPiece
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    (single i (1 : LaurentPolynomial R)) ∈
      laurentReducedConeMaslovPiece G s R (reducedConeMaslov G s i) := by
  classical
  intro j k hk
  by_cases hji : j = i
  · subst j
    rw [single_eq_same] at hk
    change k ∈ (single 0 (1 : R)).support at hk
    have hk0 := Finset.mem_singleton.mp (support_single_subset hk)
    subst k
    simp
  · rw [single_eq_of_ne hji] at hk
    simp at hk

omit [CharP R 2] in
/-- The exponent-zero generator has exactly the comparison cone's basis bounds. -/
theorem single_one_mem_laurentReducedConeBifiltrationLevel
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    (single i (1 : LaurentPolynomial R)) ∈
      laurentReducedConeBifiltrationLevel G s R 0 (reducedConeAlexander G s i) := by
  classical
  intro j k hk
  by_cases hji : j = i
  · subst j
    rw [single_eq_same] at hk
    change k ∈ (single 0 (1 : R)).support at hk
    have hk0 := Finset.mem_singleton.mp (support_single_subset hk)
    subst k
    simp
  · rw [single_eq_of_ne hji] at hk
    simp at hk

/-- The correction after the reduced homotopy strictly lowers a finite state weight. -/
theorem positiveOComparisonPerturbation_homotopy_support_lt
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n)
    (hj : j ∈ ((positiveOComparisonPerturbation G s R * laurentReducedConeHomotopy G s R)
      (single i 1)).support) :
    -reducedConeMaslov G s j < -reducedConeMaslov G s i := by
  have hjne := Finsupp.mem_support_iff.mp hj
  have hcne : (((positiveOComparisonPerturbation G s R * laurentReducedConeHomotopy G s R)
      (single i 1)) j).coeff ≠ 0 := by
    intro h
    apply hjne
    apply AddMonoidAlgebra.coeff_injective
    simpa only [AddMonoidAlgebra.coeff_zero] using h
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hcne
  have hM := (positiveOComparisonPerturbation_mem_maslovPiece G s R
    (laurentReducedConeHomotopy_mem_maslovPiece G s R
      (single_one_mem_laurentReducedConeMaslovPiece G s R i))) j k hk
  have hfirst := (positiveOComparisonPerturbation_mem_bifiltrationLevel G s R
    (laurentReducedConeHomotopy_mem_bifiltrationLevel G s R
      (single_one_mem_laurentReducedConeBifiltrationLevel G s R i))) j k hk |>.1
  have hkpos : 0 < k := by exact_mod_cast (show (0 : ℚ) < k by linarith)
  omega

/-- The O-weight perturbation has a pointwise finite geometric series on the actual cone. -/
theorem positiveOComparisonPerturbation_homotopy_locallyNilpotent
    (c : ReducedConeLaurentChain G s R) :
    ∃ k : ℕ,
      ((positiveOComparisonPerturbation G s R * laurentReducedConeHomotopy G s R) ^ k) c = 0 := by
  let w : G.StabilizeXOffCenterState s ⊕ GridState n → ℤ := fun i => -reducedConeMaslov G s i
  have hw : WellFounded (InvImage (· < ·) w) := Finite.wellFounded_of_trans_of_irrefl _
  exact Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt _ w hw
    (positiveOComparisonPerturbation_homotopy_support_lt G s R) c

/-- The concrete weighted comparison satisfies the invertibility hypothesis of HPL. -/
theorem positiveOComparisonPerturbation_homotopy_isUnit :
    IsUnit (1 + positiveOComparisonPerturbation G s R * laurentReducedConeHomotopy G s R) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _
    (positiveOComparisonPerturbation_homotopy_locallyNilpotent G s R)

/-- Restore the O weights in the constructed reduced contraction by the basic perturbation lemma. -/
noncomputable def laurentComparisonConeContraction :
    LinearSpecialContraction (laurentComparisonCone G s R)
      (0 : Module.End (LaurentPolynomial R) PUnit.{1}) := by
  let c := laurentReducedConeContraction G s R
  let δ := positiveOComparisonPerturbation G s R
  have hδ : (laurentReducedConeDifferential G s R + δ) ∘ₗ
      (laurentReducedConeDifferential G s R + δ) =
      laurentReducedConeDifferential G s R ∘ₗ laurentReducedConeDifferential G s R := by
    rw [reduced_add_positiveOComparisonPerturbation, laurentComparisonCone_comp_self,
      laurentReducedConeDifferential_comp_self]
  have hU : IsUnit (1 + δ * c.homotopy) :=
    positiveOComparisonPerturbation_homotopy_isUnit G s R
  let h := c.perturb δ hδ hU
  refine {
    incl := 0
    proj := 0
    homotopy := h.homotopy
    dM_comp_incl := by simp
    proj_comp_dM := by simp
    proj_comp_incl := Subsingleton.elim _ _
    dM_comp_homotopy_add_homotopy_comp_dM := ?_
    homotopy_comp_incl := by simp
    proj_comp_homotopy := by simp
    homotopy_comp_homotopy := h.homotopy_comp_homotopy }
  have hh := h.dM_comp_homotopy_add_homotopy_comp_dM
  have hi : h.incl = 0 := by
    change (c.perturb δ hδ hU).incl = 0
    rw [LinearSpecialContraction.perturb_incl]
    change 0 - _ ∘ₗ _ ∘ₗ (0 : PUnit.{1} →ₗ[LaurentPolynomial R] _) = 0
    simp only [LinearMap.comp_zero]
    apply LinearMap.ext
    intro z
    apply Finsupp.ext
    intro i
    change (0 : LaurentPolynomial R) - 0 = 0
    exact sub_zero _
  rw [hi, LinearMap.zero_comp] at hh
  dsimp only [δ] at hh
  simpa only [reduced_add_positiveOComparisonPerturbation, LinearMap.zero_comp] using hh


/-- The HPL homotopy is the finite correction of the constructed reduced homotopy. -/
theorem laurentComparisonConeContraction_homotopy :
    (laurentComparisonConeContraction G s R).homotopy =
      laurentReducedConeHomotopy G s R -
        laurentReducedConeHomotopy G s R ∘ₗ
          (laurentReducedConeContraction G s R).perturbationSeries
            (positiveOComparisonPerturbation G s R) ∘ₗ
          laurentReducedConeHomotopy G s R := by
  simp only [laurentComparisonConeContraction, LinearSpecialContraction.perturb_homotopy,
    laurentReducedConeContraction]


/-- The perturbed homotopy is the reduced homotopy followed by the finite geometric inverse. -/
theorem laurentComparisonConeContraction_homotopy_eq_inverse :
    (laurentComparisonConeContraction G s R).homotopy =
      laurentReducedConeHomotopy G s R * Ring.inverse
        (1 + positiveOComparisonPerturbation G s R * laurentReducedConeHomotopy G s R) := by
  rw [laurentComparisonConeContraction_homotopy]
  let H := laurentReducedConeHomotopy G s R
  let δ := positiveOComparisonPerturbation G s R
  let I := Ring.inverse (1 + δ * H)
  have hI : I * (1 + δ * H) = 1 :=
    Ring.inverse_mul_cancel _ (positiveOComparisonPerturbation_homotopy_isUnit G s R)
  have hI' : 1 - I * (δ * H) = I := by
    rw [mul_add, mul_one] at hI
    apply LinearMap.ext
    intro z
    apply Finsupp.ext
    intro i
    have hi := congrArg (fun f => f z i) hI
    change I z i + (I * (δ * H)) z i = z i at hi
    change z i - (I * (δ * H)) z i = I z i
    exact (eq_sub_of_add_eq hi).symm
  rw [LinearSpecialContraction.perturbationSeries_def]
  change H - H * (I * δ) * H = H * I
  calc
    _ = H * (1 - I * (δ * H)) := by
      apply LinearMap.ext
      intro z
      change H z - H (I (δ (H z))) = H (z - I (δ (H z)))
      exact (map_sub H z (I (δ (H z)))).symm
    _ = H * I := by rw [hI']

/-- The constructed O-weighted contracting homotopy raises Laurent Maslov degree by one. -/
theorem laurentComparisonConeContraction_homotopy_mem_maslovPiece {m : ℤ}
    {z : ReducedConeLaurentChain G s R} (hz : z ∈ laurentReducedConeMaslovPiece G s R m) :
    (laurentComparisonConeContraction G s R).homotopy z ∈
      laurentReducedConeMaslovPiece G s R (m + 1) := by
  rw [laurentComparisonConeContraction_homotopy_eq_inverse, Module.End.mul_apply]
  apply laurentReducedConeHomotopy_mem_maslovPiece
  apply MatchingContraction.ringInverse_one_add_mem _
    (positiveOComparisonPerturbation_homotopy_locallyNilpotent G s R)
    (laurentReducedConeMaslovPiece G s R m).toAddSubgroup _ hz
  intro c hc
  change c ∈ laurentReducedConeMaslovPiece G s R m at hc
  change _ ∈ laurentReducedConeMaslovPiece G s R m
  simpa only [Module.End.mul_apply, add_sub_cancel_right] using
    positiveOComparisonPerturbation_mem_maslovPiece G s R
      (laurentReducedConeHomotopy_mem_maslovPiece G s R hc)

/-- The constructed O-weighted contracting homotopy preserves both shifted cone levels. -/
theorem laurentComparisonConeContraction_homotopy_mem_bifiltrationLevel {u v : ℚ}
    {z : ReducedConeLaurentChain G s R}
    (hz : z ∈ laurentReducedConeBifiltrationLevel G s R u v) :
    (laurentComparisonConeContraction G s R).homotopy z ∈
      laurentReducedConeBifiltrationLevel G s R u v := by
  rw [laurentComparisonConeContraction_homotopy_eq_inverse, Module.End.mul_apply]
  apply laurentReducedConeHomotopy_mem_bifiltrationLevel
  apply MatchingContraction.ringInverse_one_add_mem _
    (positiveOComparisonPerturbation_homotopy_locallyNilpotent G s R)
    (laurentReducedConeBifiltrationLevel G s R u v).toAddSubgroup _ hz
  intro c hc j k hk
  obtain ⟨hfirst, hsecond⟩ := (positiveOComparisonPerturbation_mem_bifiltrationLevel G s R
    (laurentReducedConeHomotopy_mem_bifiltrationLevel G s R hc)) j k hk
  exact ⟨by linarith, hsecond⟩

end OnLeConjecture.KnotFloer.GridFull

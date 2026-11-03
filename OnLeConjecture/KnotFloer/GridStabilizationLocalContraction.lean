/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationLocalComparison

/-!
# Contracting the comparison with only the two new X markings blocked

Restoring the other X crossings strictly decreases the shifted Alexander coordinate.
Together with the actual Laurent Maslov grading this yields a finite correction series
for the previously constructed O-weighted contracting homotopy.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- Restore the X crossings away from the two new markings in the comparison cone. -/
noncomputable def extraXComparisonPerturbation : Module.End (LaurentPolynomial R)
    (ReducedConeLaurentChain G s R) :=
  localComparisonCone G s R - laurentComparisonCone G s R

/-- The perturbation consists exactly of the newly admitted rectangle terms. -/
theorem extraXComparisonPerturbation_single_apply
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n) :
    extraXComparisonPerturbation G s R (single i 1) j =
      ∑ r ∈ localComparisonRectangles G s i j \ comparisonConeRectangles G s i j,
        LaurentPolynomial.T
          (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℤ) := by
  classical
  rw [extraXComparisonPerturbation, LinearMap.sub_apply, Finsupp.sub_apply,
    localComparisonCone_single_apply, laurentComparisonCone_single_apply,
    ← Finset.sum_sdiff (comparisonConeRectangles_subset_localComparisonRectangles G s i j),
    add_sub_cancel_right]

omit [CharP R 2] in
/-- Adding the extra-X part gives the actual partially blocked comparison cone. -/
theorem laurentComparison_add_extraX :
    laurentComparisonCone G s R + extraXComparisonPerturbation G s R =
      localComparisonCone G s R := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro i
  change laurentComparisonCone G s R c i +
    (localComparisonCone G s R c i - laurentComparisonCone G s R c i) = _
  exact add_sub_cancel _ _

/-- Every surviving extra-X coefficient comes from a newly admitted comparison rectangle. -/
theorem extraXComparisonPerturbation_support (c : ReducedConeLaurentChain G s R)
    {j : G.StabilizeXOffCenterState s ⊕ GridState n} {k : ℤ}
    (hk : k ∈ (extraXComparisonPerturbation G s R c j).coeff.support) :
    ∃ i, ∃ t ∈ (c i).coeff.support,
      ∃ r ∈ localComparisonRectangles G s i j,
        r ∉ comparisonConeRectangles G s i j ∧
        k = t + (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          r.toGridRectangle).card : ℤ) := by
  classical
  rw [finiteEnd_apply_apply, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨t, ht, d, hd, htd⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hi)
  rw [extraXComparisonPerturbation_single_apply, AddMonoidAlgebra.coeff_sum] at hd
  obtain ⟨r, hr, hdr⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hd)
  obtain ⟨hr, hn⟩ := Finset.mem_sdiff.mp hr
  change d ∈ (single
    (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card : ℤ)
    (1 : R)).support at hdr
  have hd0 := Finset.mem_singleton.mp (support_single_subset hdr)
  exact ⟨i, t, ht, r, hr, hn, by rw [← hd0]; exact htd.symm⟩

/-- The extra-X perturbation has Laurent Maslov degree minus one. -/
theorem extraXComparisonPerturbation_mem_maslovPiece {m : ℤ}
    {c : ReducedConeLaurentChain G s R} (hc : c ∈ laurentReducedConeMaslovPiece G s R m) :
    extraXComparisonPerturbation G s R c ∈ laurentReducedConeMaslovPiece G s R (m - 1) := by
  intro j k hk
  obtain ⟨i, t, ht, r, hr, _, hkt⟩ := extraXComparisonPerturbation_support G s R c hk
  have hm := hc i t ht
  have hM := localComparisonRectangles_maslov G s hr
  omega

/-- The extra-X perturbation preserves the first coordinate and strictly lowers Alexander. -/
theorem extraXComparisonPerturbation_mem_bifiltrationLevel {u v : ℚ}
    {c : ReducedConeLaurentChain G s R}
    (hc : c ∈ laurentReducedConeBifiltrationLevel G s R u v) :
    extraXComparisonPerturbation G s R c ∈
      laurentReducedConeBifiltrationLevel G s R u (v - 1) := by
  intro j k hk
  obtain ⟨i, t, ht, r, hr, hn, hkt⟩ := extraXComparisonPerturbation_support G s R c hk
  obtain ⟨hfirst, hsecond⟩ := hc i t ht
  have hA := localComparisonRectangles_extra_alexander G s hr hn
  have hcount : (0 : ℚ) ≤
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card :=
    Nat.cast_nonneg _
  have hkt' : (k : ℚ) = t +
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card := by
    exact_mod_cast hkt
  constructor <;> linarith

/-- The correction after the O-weighted homotopy strictly lowers a finite rational state weight. -/
theorem extraXComparisonPerturbation_homotopy_support_lt
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n)
    (hj : j ∈ ((extraXComparisonPerturbation G s R *
      (laurentComparisonConeContraction G s R).homotopy) (single i 1)).support) :
    reducedConeAlexander G s j - (reducedConeMaslov G s j : ℚ) / 2 <
      reducedConeAlexander G s i - (reducedConeMaslov G s i : ℚ) / 2 := by
  have hjne := Finsupp.mem_support_iff.mp hj
  have hcne : (((extraXComparisonPerturbation G s R *
      (laurentComparisonConeContraction G s R).homotopy) (single i 1)) j).coeff ≠ 0 := by
    intro h
    apply hjne
    apply AddMonoidAlgebra.coeff_injective
    simpa only [AddMonoidAlgebra.coeff_zero] using h
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hcne
  have hM := (extraXComparisonPerturbation_mem_maslovPiece G s R
    (laurentComparisonConeContraction_homotopy_mem_maslovPiece G s R
      (single_one_mem_laurentReducedConeMaslovPiece G s R i))) j k hk
  have hA := (extraXComparisonPerturbation_mem_bifiltrationLevel G s R
    (laurentComparisonConeContraction_homotopy_mem_bifiltrationLevel G s R
      (single_one_mem_laurentReducedConeBifiltrationLevel G s R i))) j k hk |>.2
  have hM' : (reducedConeMaslov G s j : ℚ) - 2 * k = reducedConeMaslov G s i := by
    exact_mod_cast (show reducedConeMaslov G s j - 2 * k = reducedConeMaslov G s i by
      simpa only [add_sub_cancel_right] using hM)
  linarith

/-- The second geometric correction series terminates on every Laurent comparison chain. -/
theorem extraXComparisonPerturbation_homotopy_locallyNilpotent
    (c : ReducedConeLaurentChain G s R) :
    ∃ k : ℕ, ((extraXComparisonPerturbation G s R *
      (laurentComparisonConeContraction G s R).homotopy) ^ k) c = 0 := by
  let w : G.StabilizeXOffCenterState s ⊕ GridState n → ℚ := fun i =>
    reducedConeAlexander G s i - (reducedConeMaslov G s i : ℚ) / 2
  have hw : WellFounded (InvImage (· < ·) w) := Finite.wellFounded_of_trans_of_irrefl _
  exact Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt _ w hw
    (extraXComparisonPerturbation_homotopy_support_lt G s R) c

/-- The second concrete comparison perturbation satisfies the HPL unit hypothesis. -/
theorem extraXComparisonPerturbation_homotopy_isUnit :
    IsUnit (1 + extraXComparisonPerturbation G s R *
      (laurentComparisonConeContraction G s R).homotopy) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _
    (extraXComparisonPerturbation_homotopy_locallyNilpotent G s R)

/-- The actual comparison cone with only the two new X markings blocked is contractible. -/
noncomputable def localComparisonConeContraction :
    LinearSpecialContraction (localComparisonCone G s R)
      (0 : Module.End (LaurentPolynomial R) PUnit.{1}) := by
  let c := laurentComparisonConeContraction G s R
  let δ := extraXComparisonPerturbation G s R
  have hδ : (laurentComparisonCone G s R + δ) ∘ₗ (laurentComparisonCone G s R + δ) =
      laurentComparisonCone G s R ∘ₗ laurentComparisonCone G s R := by
    rw [laurentComparison_add_extraX, localComparisonCone_comp_self,
      laurentComparisonCone_comp_self]
  have hU : IsUnit (1 + δ * c.homotopy) := extraXComparisonPerturbation_homotopy_isUnit G s R
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
  simpa only [laurentComparison_add_extraX, LinearMap.zero_comp] using hh

/-- The HPL homotopy is the finite correction of the constructed O-weighted homotopy. -/
theorem localComparisonConeContraction_homotopy :
    (localComparisonConeContraction G s R).homotopy =
      (laurentComparisonConeContraction G s R).homotopy -
        (laurentComparisonConeContraction G s R).homotopy ∘ₗ
          (laurentComparisonConeContraction G s R).perturbationSeries
            (extraXComparisonPerturbation G s R) ∘ₗ
          (laurentComparisonConeContraction G s R).homotopy := by
  unfold localComparisonConeContraction
  exact LinearSpecialContraction.perturb_homotopy _ _ _ _


/-- The perturbed homotopy is the O-weighted homotopy followed by the finite geometric inverse. -/
theorem localComparisonConeContraction_homotopy_eq_inverse :
    (localComparisonConeContraction G s R).homotopy =
      (laurentComparisonConeContraction G s R).homotopy * Ring.inverse
        (1 + extraXComparisonPerturbation G s R *
          (laurentComparisonConeContraction G s R).homotopy) := by
  rw [localComparisonConeContraction_homotopy]
  let H := (laurentComparisonConeContraction G s R).homotopy
  let δ := extraXComparisonPerturbation G s R
  let I := Ring.inverse (1 + δ * H)
  have hI : I * (1 + δ * H) = 1 :=
    Ring.inverse_mul_cancel _ (extraXComparisonPerturbation_homotopy_isUnit G s R)
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

/-- The constructed partially blocked contracting homotopy raises Laurent Maslov degree by one. -/
theorem localComparisonConeContraction_homotopy_mem_maslovPiece {m : ℤ}
    {z : ReducedConeLaurentChain G s R} (hz : z ∈ laurentReducedConeMaslovPiece G s R m) :
    (localComparisonConeContraction G s R).homotopy z ∈
      laurentReducedConeMaslovPiece G s R (m + 1) := by
  rw [localComparisonConeContraction_homotopy_eq_inverse, Module.End.mul_apply]
  apply laurentComparisonConeContraction_homotopy_mem_maslovPiece
  apply MatchingContraction.ringInverse_one_add_mem _
    (extraXComparisonPerturbation_homotopy_locallyNilpotent G s R)
    (laurentReducedConeMaslovPiece G s R m).toAddSubgroup _ hz
  intro c hc
  change c ∈ laurentReducedConeMaslovPiece G s R m at hc
  change _ ∈ laurentReducedConeMaslovPiece G s R m
  simpa only [Module.End.mul_apply, add_sub_cancel_right] using
    extraXComparisonPerturbation_mem_maslovPiece G s R
      (laurentComparisonConeContraction_homotopy_mem_maslovPiece G s R hc)

/-- The constructed partially blocked contracting homotopy preserves both shifted cone levels. -/
theorem localComparisonConeContraction_homotopy_mem_bifiltrationLevel {u v : ℚ}
    {z : ReducedConeLaurentChain G s R}
    (hz : z ∈ laurentReducedConeBifiltrationLevel G s R u v) :
    (localComparisonConeContraction G s R).homotopy z ∈
      laurentReducedConeBifiltrationLevel G s R u v := by
  rw [localComparisonConeContraction_homotopy_eq_inverse, Module.End.mul_apply]
  apply laurentComparisonConeContraction_homotopy_mem_bifiltrationLevel
  apply MatchingContraction.ringInverse_one_add_mem _
    (extraXComparisonPerturbation_homotopy_locallyNilpotent G s R)
    (laurentReducedConeBifiltrationLevel G s R u v).toAddSubgroup _ hz
  intro c hc j k hk
  obtain ⟨hfirst, hsecond⟩ := (extraXComparisonPerturbation_mem_bifiltrationLevel G s R
    (laurentComparisonConeContraction_homotopy_mem_bifiltrationLevel G s R hc)) j k hk
  exact ⟨hfirst, by linarith⟩

end OnLeConjecture.KnotFloer.GridFull

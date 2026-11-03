/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationReducedContraction
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Stabilization.Grading

/-!
# The grading and Alexander filtration of the reduced stabilization contraction

The off-center summand has the gradings of the stabilized diagram. A center generator
coming from `x` has Maslov grading `M_G(x)-1` and Alexander grading `A_G(x)`.
Thus the center Alexander grading is one higher than its grading as an inserted
state in the stabilized diagram. These shifts are required by the comparison cone.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The Maslov grading on the reduced comparison cone. -/
noncomputable def reducedConeMaslov : G.StabilizeXOffCenterState s ⊕ GridState n → ℤ
  | .inl y => (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ y
  | .inr x => G.maslovOℤ x - 1

/-- The comparison cone uses the old Alexander grading on its center summand. -/
noncomputable def reducedConeAlexander : G.StabilizeXOffCenterState s ⊕ GridState n → ℚ
  | .inl y => (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander y
  | .inr x => G.alexander x

private theorem fullyBlocked_grading_change {m : ℕ} (H : GridDiagram m)
    {x y : GridState m} {r : GridRectangleBetween x y}
    (hr : r ∈ H.fullyBlockedRectangles x y) :
    H.maslovOℤ y = H.maslovOℤ x - 1 ∧ H.alexander y = H.alexander x := by
  have hempty := H.isEmpty_of_mem_fullyBlockedRectangles x y hr
  have havoid := H.avoidsMarkings_of_mem_fullyBlockedRectangles x y hr
  have hO := (H.OColumns_eq_empty_iff r.toGridRectangle).mpr
    (r.disjoint_coveredSquares_OSet_of_avoidsMarkings havoid)
  constructor
  · simpa [hO] using H.maslovOℤ_sub_two_mul_card_OColumns hempty
  · exact (H.alexander_eq_alexander_of_disjoint_coveredSquares r havoid).symm

variable (R : Type*) [CommRing R] [CharP R 2]

omit [CharP R 2] in
/-- Every nonzero reduced-cone matrix entry lowers Maslov degree and preserves the shifted A. -/
theorem reducedCone_grading_of_mem_support
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n)
    (hj : j ∈ (G.stabilizeXReducedCone s R (single i 1)).support) :
    reducedConeMaslov G s j = reducedConeMaslov G s i - 1 ∧
      reducedConeAlexander G s j = reducedConeAlexander G s i := by
  classical
  rw [Finsupp.mem_support_iff] at hj
  rcases i with y | x <;> rcases j with z | x'
  · rw [LinearMap.sumMappingCone_single_inl_apply_inl,
      GridDiagram.constantCoeffReduction_stabilizeXOffCenterDifferential_single_apply,
      one_mul, neg_ne_zero] at hj
    obtain ⟨r, hr⟩ := Finset.card_ne_zero.mp fun h => hj (by rw [h, Nat.cast_zero])
    exact fullyBlocked_grading_change _ hr
  · rw [LinearMap.sumMappingCone_single_inl_apply_inr,
      GridDiagram.constantCoeffReduction_stabilizeXOffCenterToCenter_single_apply,
      one_mul] at hj
    obtain ⟨r, hr⟩ := Finset.card_ne_zero.mp fun h => hj (by rw [h, Nat.cast_zero])
    obtain ⟨hr, hO⟩ := Finset.mem_filter.mp hr
    have hempty := ((G.stabilizeX s.castSucc (G.X s).castSucc s).mem_XHomotopyRectangles
      s.succ r).mp hr |>.1
    have hM := G.maslovOℤ_stabilizeX_eq_of_isEmpty s x' hempty
    have hA := G.alexander_stabilizeX_eq_of_mem_XHomotopyRectangles s x' hr
    simp only [hO, Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero] at hM hA
    dsimp only [reducedConeMaslov, reducedConeAlexander]
    exact ⟨congrArg (fun m : ℤ => m - 1) hM.symm, hA.symm⟩
  · exact False.elim (hj (LinearMap.sumMappingCone_single_inr_apply_inl ..))
  · rw [LinearMap.sumMappingCone_single_inr_apply_inr,
      GridDiagram.constantCoeffReduction_stabilizeXCenterDifferential_single_apply,
      one_mul] at hj
    obtain ⟨r, hr⟩ := Finset.card_ne_zero.mp fun h => hj (by rw [h, Nat.cast_zero])
    obtain ⟨hM, hA⟩ := fullyBlocked_grading_change G hr
    exact ⟨congrArg (fun m : ℤ => m - 1) hM, hA⟩

/-- The reverse matching occurring in the constructed contraction. -/
noncomputable def reducedConeReverseMatching :
    Module.End R (G.StabilizeXOffCenterState s ⊕ GridState n →₀ R) :=
  MatchingContraction.reverseHomotopy (G.stabilizeXReducedCone s R)
    (G.stabilizeXMatching s) (G.StabilizeXMatchingSource s)

/-- The reverse matching raises Maslov degree by one and preserves the shifted A grading. -/
theorem reducedCone_reverse_grading_of_mem_support
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n)
    (hj : j ∈ (reducedConeReverseMatching G s R (single i 1)).support) :
    reducedConeMaslov G s j = reducedConeMaslov G s i + 1 ∧
      reducedConeAlexander G s j = reducedConeAlexander G s i := by
  classical
  let : Nontrivial R := CharP.nontrivial_of_char_ne_one (R := R) (by decide : 2 ≠ 1)
  rw [reducedConeReverseMatching, MatchingContraction.reverseHomotopy_single] at hj
  by_cases hi : G.StabilizeXMatchingSource s i
  · simp [hi] at hj
  · rw [if_neg hi] at hj
    have hji := Finset.mem_singleton.mp (Finsupp.support_single_subset hj)
    subst j
    have hpi : G.StabilizeXMatchingSource s (G.stabilizeXMatching s i) :=
      (G.stabilizeXMatchingSource_stabilizeXMatching_iff s i).mpr hi
    have hd : i ∈ (G.stabilizeXReducedCone s R
        (single (G.stabilizeXMatching s i) 1)).support := by
      rw [Finsupp.mem_support_iff]
      have hcoef := G.stabilizeXReducedCone_single_apply_stabilizeXMatching s R _ hpi
      simp only [G.stabilizeXMatching_involutive] at hcoef
      rw [hcoef]
      exact one_ne_zero
    have hg := reducedCone_grading_of_mem_support G s R _ _ hd
    exact ⟨by omega, hg.2.symm⟩

omit [CharP R 2] in
private theorem map_mem_supported_of_basis {ι : Type*}
    (f : Module.End R (ι →₀ R)) (S T : Set ι)
    (hf : ∀ i ∈ S, ∀ j ∈ (f (single i 1)).support, j ∈ T)
    {c : ι →₀ R} (hc : c ∈ Finsupp.supported R R S) :
    f c ∈ Finsupp.supported R R T := by
  classical
  rw [← Finsupp.sum_single c, map_finsuppSum]
  refine Submodule.sum_mem _ fun i hi => ?_
  dsimp only
  rw [← Finsupp.smul_single_one, map_smul]
  apply Submodule.smul_mem
  exact (Finsupp.mem_supported R _).mpr
    (hf i ((Finsupp.mem_supported R c).mp hc hi))

/-- Homogeneous reduced-cone chains, with the coefficient ring assigned degree zero. -/
noncomputable def reducedConeMaslovPiece (m : ℤ) :
    Submodule R (G.StabilizeXOffCenterState s ⊕ GridState n →₀ R) :=
  Finsupp.supported R R {i | reducedConeMaslov G s i = m}

/-- The Alexander level with the comparison cone's center shift. -/
noncomputable def reducedConeAlexanderLevel (a : ℚ) :
    Submodule R (G.StabilizeXOffCenterState s ⊕ GridState n →₀ R) :=
  Finsupp.supported R R {i | reducedConeAlexander G s i ≤ a}

omit [CharP R 2] in
/-- The reduced differential lowers Maslov degree by one. -/
theorem reducedCone_d_mem_maslovPiece {m : ℤ}
    {c : G.StabilizeXOffCenterState s ⊕ GridState n →₀ R}
    (hc : c ∈ reducedConeMaslovPiece G s R m) :
    G.stabilizeXReducedCone s R c ∈ reducedConeMaslovPiece G s R (m - 1) := by
  classical
  apply map_mem_supported_of_basis R _ _ _ _ hc
  intro i hi j hj
  exact (reducedCone_grading_of_mem_support G s R i j hj).1.trans (congrArg (· - 1) hi)

/-- The reverse matching raises Maslov degree by one. -/
theorem reducedCone_reverse_mem_maslovPiece {m : ℤ}
    {c : G.StabilizeXOffCenterState s ⊕ GridState n →₀ R}
    (hc : c ∈ reducedConeMaslovPiece G s R m) :
    reducedConeReverseMatching G s R c ∈ reducedConeMaslovPiece G s R (m + 1) := by
  classical
  apply map_mem_supported_of_basis R _ _ _ _ hc
  intro i hi j hj
  exact (reducedCone_reverse_grading_of_mem_support G s R i j hj).1.trans
    (congrArg (· + 1) hi)

omit [CharP R 2] in
/-- The reduced differential preserves the shifted Alexander level. -/
theorem reducedCone_d_mem_alexanderLevel {a : ℚ}
    {c : G.StabilizeXOffCenterState s ⊕ GridState n →₀ R}
    (hc : c ∈ reducedConeAlexanderLevel G s R a) :
    G.stabilizeXReducedCone s R c ∈ reducedConeAlexanderLevel G s R a := by
  classical
  apply map_mem_supported_of_basis R _ _ _ _ hc
  intro i hi j hj
  exact ((reducedCone_grading_of_mem_support G s R i j hj).2).le.trans hi

/-- The reverse matching preserves the shifted Alexander level. -/
theorem reducedCone_reverse_mem_alexanderLevel {a : ℚ}
    {c : G.StabilizeXOffCenterState s ⊕ GridState n →₀ R}
    (hc : c ∈ reducedConeAlexanderLevel G s R a) :
    reducedConeReverseMatching G s R c ∈ reducedConeAlexanderLevel G s R a := by
  classical
  apply map_mem_supported_of_basis R _ _ _ _ hc
  intro i hi j hj
  exact ((reducedCone_reverse_grading_of_mem_support G s R i j hj).2).le.trans hi

/-- The normalization correction is locally nilpotent by the proved grid matching weight. -/
theorem reducedCone_remainder_locallyNilpotent
    (c : G.StabilizeXOffCenterState s ⊕ GridState n →₀ R) :
    ∃ k : ℕ, ((G.stabilizeXReducedCone s R * reducedConeReverseMatching G s R +
      reducedConeReverseMatching G s R * G.stabilizeXReducedCone s R - 1) ^ k) c = 0 := by
  apply Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt _
    (G.stabilizeXConeWeight s) (Finite.wellFounded_of_trans_of_irrefl _) _ c
  exact MatchingContraction.remainder_support_lt _ _ _ _
    (G.stabilizeXMatching_involutive s) (G.stabilizeXConeWeight_stabilizeXMatching s)
    (fun i => by rw [G.stabilizeXMatchingSource_stabilizeXMatching_iff, not_not])
    (fun i hi => by
      rw [G.stabilizeXReducedCone_single_apply_stabilizeXMatching s R i hi]
      exact isUnit_one)
    (G.stabilizeXConeWeight_lt_or_of_mem_support s R)

/-- The actual contracted homotopy is the inverse-normalized reverse row matching. -/
theorem reducedStabilizationHomotopy_eq_normalized :
    reducedStabilizationHomotopy G s R = MatchingContraction.normalizedHomotopy
      (G.stabilizeXReducedCone s R) (reducedConeReverseMatching G s R) := rfl

/-- The constructed reduced-cone homotopy raises Maslov degree by one. -/
theorem reducedStabilizationHomotopy_mem_maslovPiece {m : ℤ}
    {c : G.StabilizeXOffCenterState s ⊕ GridState n →₀ R}
    (hc : c ∈ reducedConeMaslovPiece G s R m) :
    reducedStabilizationHomotopy G s R c ∈ reducedConeMaslovPiece G s R (m + 1) := by
  rw [reducedStabilizationHomotopy_eq_normalized]
  apply MatchingContraction.normalizedHomotopy_mem _ _
    (reducedCone_remainder_locallyNilpotent G s R)
    (reducedConeMaslovPiece G s R m).toAddSubgroup
    (reducedConeMaslovPiece G s R (m + 1)).toAddSubgroup _ _ hc
  · intro z hz
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.one_apply]
    apply Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) hz
    · simpa only [add_sub_cancel_right] using reducedCone_d_mem_maslovPiece G s R
        (reducedCone_reverse_mem_maslovPiece G s R hz)
    · simpa only [sub_add_cancel] using reducedCone_reverse_mem_maslovPiece G s R
        (reducedCone_d_mem_maslovPiece G s R hz)
  · exact fun _ hz => reducedCone_reverse_mem_maslovPiece G s R hz

/-- The constructed reduced-cone homotopy preserves the correctly shifted Alexander filtration. -/
theorem reducedStabilizationHomotopy_mem_alexanderLevel {a : ℚ}
    {c : G.StabilizeXOffCenterState s ⊕ GridState n →₀ R}
    (hc : c ∈ reducedConeAlexanderLevel G s R a) :
    reducedStabilizationHomotopy G s R c ∈ reducedConeAlexanderLevel G s R a := by
  rw [reducedStabilizationHomotopy_eq_normalized]
  apply MatchingContraction.normalizedHomotopy_mem _ _
    (reducedCone_remainder_locallyNilpotent G s R)
    (reducedConeAlexanderLevel G s R a).toAddSubgroup
    (reducedConeAlexanderLevel G s R a).toAddSubgroup _ _ hc
  · intro z hz
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.one_apply]
    exact Submodule.sub_mem _ (Submodule.add_mem _
      (reducedCone_d_mem_alexanderLevel G s R
        (reducedCone_reverse_mem_alexanderLevel G s R hz))
      (reducedCone_reverse_mem_alexanderLevel G s R
        (reducedCone_d_mem_alexanderLevel G s R hz))) hz
  · exact fun _ hz => reducedCone_reverse_mem_alexanderLevel G s R hz

end OnLeConjecture.KnotFloer.GridFull

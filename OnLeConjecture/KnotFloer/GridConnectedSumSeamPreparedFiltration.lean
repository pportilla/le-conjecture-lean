/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamTransferred

/-!
# Filtration bounds for a seam with the last O in the shared row

The hypothesis H.O(last)=0 places the sole possible southwest O beyond
every selected matching rectangle. All matching coefficients are then
one. The finite inverse has nonnegative Laurent exponents, while its
X-Maslov order controls the Alexander filtration.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- An O in the final second-factor column cannot lie inside a selected matching rectangle. -/
theorem seamComplementOCount_eq_zero_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hO : H.O (Fin.last m) = 0) (x : SeamComplement n m) :
    seamComplementOCount G H x = 0 := by
  classical
  have hlast : H.O.toPerm.symm 0 = Fin.last m :=
    (H.O.toPerm.eq_symm_apply.mpr hO).symm
  unfold seamComplementOCount
  rw [hlast]
  apply if_neg
  intro hc
  have hh := (mem_toGridRectangle_coveredSquares _).mp hc
  rw [seamComplementRectangle_left, seamComplementRectangle_right,
    Grid.mem_cIco_iff_of_left_lt_right (seamComplementFirst_lt_second x)] at hh
  have hq := (seamComplementSecond x).isLt
  have hbound := hh.1.2
  change n + m < (seamComplementSecond x).val at hbound
  omega

/-- Prepared normalized transition coefficients contain no negative Laurent exponents. -/
theorem seamMatchingTransitionMatrix_support_nonneg_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] (x y : SeamMatchingSource n m) {j : ℤ}
    (hj : j ∈ (seamMatchingTransitionMatrix G H hG hH R y x).coeff.support) : 0 ≤ j := by
  by_cases hxy : x = y
  · subst y
    rw [seamMatchingTransitionMatrix_diag] at hj
    simp at hj
  · rw [seamMatchingTransitionMatrix_offDiag G H hG hH R x y hxy,
      seamMatchingMatrix, seamComplementOCount_eq_zero_of_last_O G H hO y.val,
      Nat.cast_zero, neg_zero, LaurentPolynomial.T_zero, one_mul] at hj
    obtain ⟨r, hr, rfl⟩ := exists_rectangle_of_mem_support_laurentCoefficient
      (connectedSumSeamGrid G H hG hH) R hj
    exact Nat.cast_nonneg _

/-- Nonnegative exponents persist through every power of the actual transition matrix. -/
theorem seamMatchingTransitionMatrix_pow_support_nonneg_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] (k : ℕ) (x y : SeamMatchingSource n m) {j : ℤ}
    (hj : j ∈ ((seamMatchingTransitionMatrix G H hG hH R ^ k) y x).coeff.support) : 0 ≤ j := by
  classical
  induction k generalizing x y j with
  | zero =>
    by_cases hxy : y = x
    · subst y
      simp only [pow_zero, Matrix.one_apply_eq] at hj
      have hh : j ∈ (Finsupp.single (0 : ℤ) (1 : R)).support := hj
      have hj0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hh)
      omega
    · simp [pow_zero, hxy] at hj
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply, AddMonoidAlgebra.coeff_sum] at hj
    obtain ⟨z, hz, hjz⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hj)
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hjz)
    exact add_nonneg (ih z y ha)
      (seamMatchingTransitionMatrix_support_nonneg_of_last_O G H hG hH hO R x z hb)

/-- The constructed finite matching inverse is polynomial-compatible for the prepared seam. -/
theorem seamMatchingMatrixInverse_support_nonneg_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] (x y : SeamMatchingSource n m) {j : ℤ}
    (hj : j ∈ (seamMatchingMatrixInverse G H hG hH R y x).coeff.support) : 0 ≤ j := by
  classical
  rw [seamMatchingMatrixInverse, Matrix.sum_apply, AddMonoidAlgebra.coeff_sum] at hj
  obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hj)
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_pow] at hjk
    exact seamMatchingTransitionMatrix_pow_support_nonneg_of_last_O G H hG hH hO R k x y hjk
  · rw [ho.neg_pow, Matrix.neg_apply, AddMonoidAlgebra.coeff_neg, Finsupp.support_neg] at hjk
    exact seamMatchingTransitionMatrix_pow_support_nonneg_of_last_O G H hG hH hO R k x y hjk

/-- Each nonzero matrix power respects the proved X-Maslov path order. -/
theorem seamMatchingTransitionMatrix_pow_maslovX_mono
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (k : ℕ) (x y : SeamMatchingSource n m)
    (h : (seamMatchingTransitionMatrix G H hG hH R ^ k) y x ≠ 0) :
    (connectedSumSeamGrid G H hG hH).maslovXℤ x.val.val ≤
      (connectedSumSeamGrid G H hG hH).maslovXℤ y.val.val := by
  classical
  induction k generalizing x y with
  | zero =>
    by_cases hxy : y = x
    · subst y
      exact le_rfl
    · exact False.elim (h (by simp [hxy]))
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨z, hz, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hk : (seamMatchingTransitionMatrix G H hG hH R ^ k) y z ≠ 0 := by
      intro he
      exact hprod (by rw [he, zero_mul])
    have he : seamMatchingTransitionMatrix G H hG hH R z x ≠ 0 := by
      intro he
      exact hprod (by rw [he, mul_zero])
    exact ((seamMatchingStep_of_transition_ne_zero G H hG hH R x z he).maslovX_mono
      G H hG hH).trans (ih z y hk)

/-- The full finite inverse respects the same X-Maslov order. -/
theorem seamMatchingMatrixInverse_maslovX_mono
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (x y : SeamMatchingSource n m)
    (h : seamMatchingMatrixInverse G H hG hH R y x ≠ 0) :
    (connectedSumSeamGrid G H hG hH).maslovXℤ x.val.val ≤
      (connectedSumSeamGrid G H hG hH).maslovXℤ y.val.val := by
  classical
  rw [seamMatchingMatrixInverse, Matrix.sum_apply] at h
  obtain ⟨k, hk, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hp : (seamMatchingTransitionMatrix G H hG hH R ^ k) y x ≠ 0 := by
    rcases Nat.even_or_odd k with he | ho
    · rwa [he.neg_pow] at hterm
    · simpa only [ho.neg_pow, Matrix.neg_apply, neg_ne_zero] using hterm
  exact seamMatchingTransitionMatrix_pow_maslovX_mono G H hG hH R k x y hp

/-- Prepared inverse coefficients do not increase the second filtration coordinate. -/
theorem seamMatchingMatrixInverse_support_alexander_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] (x y : SeamMatchingSource n m) {j : ℤ}
    (hj : j ∈ (seamMatchingMatrixInverse G H hG hH R x y).coeff.support) :
    ((connectedSumSeamGrid G H hG hH).alexander x.val.val : ℝ) - j ≤
      ((connectedSumSeamGrid G H hG hH).alexander (seamComplementPartner y.val).val : ℝ) := by
  let K := connectedSumSeamGrid G H hG hH
  have hn : seamMatchingMatrixInverse G H hG hH R x y ≠ 0 := by
    intro he
    rw [he] at hj
    simp at hj
  have hdi := seamMatchingMatrixInverse_support_maslov G H hG hH R y x hj
  have hmi := seamMatchingMatrixInverse_maslovX_mono G H hG hH R y x hn
  have hd : (2 : ℚ) * j = K.maslovO x.val.val - K.maslovO y.val.val := by
    rw [K.maslovO_eq_intCast, K.maslovO_eq_intCast]
    exact_mod_cast hdi
  have hm : K.maslovX y.val.val ≤ K.maslovX x.val.val := by
    rw [K.maslovX_eq_intCast, K.maslovX_eq_intCast]
    exact_mod_cast hmi
  have ha : K.alexander x.val.val - j ≤ K.alexander y.val.val := by
    rw [GridDiagram.alexander_def, GridDiagram.alexander_def]
    linarith
  have hy := connectedSumSeamGrid_complement_alexander G H hG hH y.val y.property
  rw [seamComplementOCount_eq_zero_of_last_O G H hO y.val, Nat.cast_zero, add_zero] at hy
  have hh : K.alexander x.val.val - j ≤ K.alexander (seamComplementPartner y.val).val :=
    ha.trans_eq hy
  exact_mod_cast hh

/-- The prepared inverse block has no reciprocal row factors. -/
theorem seamFullMatchingBlockEquiv_symm_apply_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] (c : SeamMatchingCoordinates R n m) (x : SeamMatchingSource n m) :
    (seamFullMatchingBlockEquiv G H hG hH R).symm c x =
      ∑ y : SeamMatchingSource n m, seamMatchingMatrixInverse G H hG hH R x y * c y := by
  rw [seamFullMatchingBlockEquiv_symm_apply]
  simp_rw [seamComplementOCount_eq_zero_of_last_O G H hO,
    Nat.cast_zero, neg_zero, LaurentPolynomial.T_zero, one_mul]

/-- The actual inverse block preserves both coefficient bounds in the prepared seam. -/
theorem seamFullMatchingBlockEquiv_symm_bound_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] (c : SeamMatchingCoordinates R n m) {u v : ℝ}
    (hc : ∀ y j, j ∈ (c y).coeff.support →
      -(j : ℝ) ≤ u ∧
        ((connectedSumSeamGrid G H hG hH).alexander (seamComplementPartner y.val).val : ℝ) - j ≤ v)
    (x : SeamMatchingSource n m) (k : ℤ)
    (hk : k ∈ ((seamFullMatchingBlockEquiv G H hG hH R).symm c x).coeff.support) :
    -(k : ℝ) ≤ u ∧ ((connectedSumSeamGrid G H hG hH).alexander x.val.val : ℝ) - k ≤ v := by
  classical
  rw [seamFullMatchingBlockEquiv_symm_apply_of_last_O G H hG hH hO,
    AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨y, hy, hky⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hky)
  have hn := seamMatchingMatrixInverse_support_nonneg_of_last_O G H hG hH hO R y x ha
  have hA := seamMatchingMatrixInverse_support_alexander_of_last_O G H hG hH hO R x y ha
  have hh := hc y b hb
  have hnR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hn
  push_cast
  constructor <;> linarith [hh.1, hh.2]



private theorem contraction_cast_homotopy {S M N : Type*} [CommRing S]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    {d d' : Module.End S M} {e : Module.End S N} (h : d = d')
    (c : LinearSpecialContraction d e) :
    (Eq.mp (congrArg (fun d => LinearSpecialContraction d e) h) c).homotopy = c.homotopy := by
  cases h
  rfl

private theorem contraction_cast_incl {S M N : Type*} [CommRing S]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    {d d' : Module.End S M} {e : Module.End S N} (h : d = d')
    (c : LinearSpecialContraction d e) :
    (Eq.mp (congrArg (fun d => LinearSpecialContraction d e) h) c).incl = c.incl := by
  cases h
  rfl

private theorem contraction_cast_proj {S M N : Type*} [CommRing S]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    {d d' : Module.End S M} {e : Module.End S N} (h : d = d')
    (c : LinearSpecialContraction d e) :
    (Eq.mp (congrArg (fun d => LinearSpecialContraction d e) h) c).proj = c.proj := by
  cases h
  rfl

/-- The cancellation homotopy uses the constructed inverse of the full matching block. -/
theorem seamFullContraction_homotopy_apply
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] [CharP R 2] (c : LaurentChain R (n + m + 1)) :
    (seamFullContraction G H hG hH R).homotopy c =
      (seamCoordinateEquiv R).symm (0,
        ((seamFullMatchingBlockEquiv G H hG hH R).symm
          (seamCoordinateEquiv R c).2.2, 0)) := by
  change (Eq.mp (congrArg (fun d => LinearSpecialContraction d
    (seamRetainedDifferential G H hG hH R))
    (seamCoordinateDifferential_conjugate G H hG hH R))
    (SpecialContraction.transportSource (seamCoordinateContraction G H hG hH R)
      (seamCoordinateEquiv R))).homotopy c = _
  rw [contraction_cast_homotopy (seamCoordinateDifferential_conjugate G H hG hH R)]
  rfl

/-- Include the pair-state coefficients before the inverse correction. -/
def seamRetainedInclusion (R : Type*) [CommRing R] :
    SeamRetainedCoordinates R n m →ₗ[LaurentPolynomial R] LaurentChain R (n + m + 1) :=
  (seamCoordinateEquiv R).symm.toLinearMap ∘ₗ FiniteBlockCancellation.retainedInclusion

/-- Read the pair-state coefficients. -/
def seamRetainedProjection (R : Type*) [CommRing R] :
    LaurentChain R (n + m + 1) →ₗ[LaurentPolynomial R] SeamRetainedCoordinates R n m :=
  FiniteBlockCancellation.retainedProjection ∘ₗ (seamCoordinateEquiv R).toLinearMap

@[simp] theorem seamRetainedInclusion_apply (R : Type*) [CommRing R]
    (c : SeamRetainedCoordinates R n m) :
    seamRetainedInclusion R c = (seamCoordinateEquiv R).symm (c, (0, 0)) := rfl

@[simp] theorem seamRetainedProjection_apply (R : Type*) [CommRing R]
    (c : LaurentChain R (n + m + 1)) (p : SeamRetainedIndex n m) :
    seamRetainedProjection R c p = c (seamState p.1 p.2) := rfl

/-- The actual corrected inclusion in the original state coordinates. -/
theorem seamFullContraction_incl_apply
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] [CharP R 2] (c : SeamRetainedCoordinates R n m) :
    (seamFullContraction G H hG hH R).incl c = seamRetainedInclusion R c -
      (seamFullContraction G H hG hH R).homotopy
        (laurentDifferential (connectedSumSeamGrid G H hG hH) R (seamRetainedInclusion R c)) := by
  rw [seamFullContraction_homotopy_apply]
  change (Eq.mp (congrArg (fun d => LinearSpecialContraction d
    (seamRetainedDifferential G H hG hH R))
    (seamCoordinateDifferential_conjugate G H hG hH R))
    (SpecialContraction.transportSource (seamCoordinateContraction G H hG hH R)
      (seamCoordinateEquiv R))).incl c = _
  rw [contraction_cast_incl (seamCoordinateDifferential_conjugate G H hG hH R)]
  dsimp only [SpecialContraction.transportSource, seamCoordinateContraction,
    FiniteBlockCancellation.toSpecialContraction]
  simp only [FiniteBlockCancellation.correctedInclusion, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
    FiniteBlockCancellation.homotopy_apply, FiniteBlockCancellation.retainedInclusion,
    LinearMap.coe_mk, AddHom.coe_mk]
  rfl

/-- The actual corrected projection in the original state coordinates. -/
theorem seamFullContraction_proj_apply
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] [CharP R 2] (c : LaurentChain R (n + m + 1)) :
    (seamFullContraction G H hG hH R).proj c = seamRetainedProjection R
      (c - laurentDifferential (connectedSumSeamGrid G H hG hH) R
        ((seamFullContraction G H hG hH R).homotopy c)) := by
  rw [seamFullContraction_homotopy_apply]
  change (Eq.mp (congrArg (fun d => LinearSpecialContraction d
    (seamRetainedDifferential G H hG hH R))
    (seamCoordinateDifferential_conjugate G H hG hH R))
    (SpecialContraction.transportSource (seamCoordinateContraction G H hG hH R)
      (seamCoordinateEquiv R))).proj c = _
  rw [contraction_cast_proj (seamCoordinateDifferential_conjugate G H hG hH R)]
  change ((seamCoordinateEquiv R c) - seamCoordinateDifferential G H hG hH R
    (0, ((seamFullMatchingBlockEquiv G H hG hH R).symm
      (seamCoordinateEquiv R c).2.2, 0))).1 = _
  simp only [seamRetainedProjection, seamCoordinateDifferential, LinearMap.comp_apply,
    LinearEquiv.coe_coe, map_sub, FiniteBlockCancellation.retainedProjection,
    LinearMap.fst_apply, Prod.fst_sub]

/-- The prepared cancellation homotopy preserves both grid filtrations. -/
theorem seamFullContraction_homotopy_mem_bifiltration_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] [CharP R 2] {u v : ℝ} {c : LaurentChain R (n + m + 1)}
    (hc : c ∈ laurentBifiltrationLevel (connectedSumSeamGrid G H hG hH) R u v) :
    (seamFullContraction G H hG hH R).homotopy c ∈
      laurentBifiltrationLevel (connectedSumSeamGrid G H hG hH) R u v := by
  rw [seamFullContraction_homotopy_apply]
  intro w k hk
  obtain ⟨a, rfl⟩ := seamThreeState_surjective w
  rcases a with p | x
  · change k ∈ ((seamCoordinateEquiv R).symm _ (seamState p.1 p.2)).coeff.support at hk
    rw [seamCoordinateEquiv_symm_retained] at hk
    simp at hk
  · rcases x with x | y
    · change k ∈ ((seamCoordinateEquiv R).symm _ x.val.val).coeff.support at hk
      rw [seamCoordinateEquiv_symm_source] at hk
      exact seamFullMatchingBlockEquiv_symm_bound_of_last_O G H hG hH hO R _
        (fun y j hj => hc (seamComplementPartner y.val).val j hj) x k hk
    · change k ∈ ((seamCoordinateEquiv R).symm _
        (seamComplementPartner y.val).val).coeff.support at hk
      rw [seamCoordinateEquiv_symm_target] at hk
      simp at hk

/-- The retained filtration uses the actual seam-state gradings, before tensor identification. -/
def seamRetainedBifiltrationLevel
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (u v : ℝ) : Submodule R (SeamRetainedCoordinates R n m) :=
  (laurentBifiltrationLevel (connectedSumSeamGrid G H hG hH) R u v).comap
    ((seamRetainedInclusion R).restrictScalars R)

/-- Reading pair-state coefficients preserves their two filtration bounds. -/
theorem seamRetainedProjection_mem_bifiltration
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] {u v : ℝ} {c : LaurentChain R (n + m + 1)}
    (hc : c ∈ laurentBifiltrationLevel (connectedSumSeamGrid G H hG hH) R u v) :
    seamRetainedProjection R c ∈ seamRetainedBifiltrationLevel G H hG hH R u v := by
  intro w k hk
  obtain ⟨a, rfl⟩ := seamThreeState_surjective w
  rcases a with p | x
  · change k ∈ ((seamCoordinateEquiv R).symm _ (seamState p.1 p.2)).coeff.support at hk
    rw [seamCoordinateEquiv_symm_retained] at hk
    exact hc (seamState p.1 p.2) k hk
  · rcases x with x | y
    · change k ∈ ((seamCoordinateEquiv R).symm _ x.val.val).coeff.support at hk
      rw [seamCoordinateEquiv_symm_source] at hk
      simp [FiniteBlockCancellation.retainedInclusion] at hk
    · change k ∈ ((seamCoordinateEquiv R).symm _
        (seamComplementPartner y.val).val).coeff.support at hk
      rw [seamCoordinateEquiv_symm_target] at hk
      simp [FiniteBlockCancellation.retainedInclusion] at hk

/-- The corrected inclusion has shift zero in both filtrations on prepared seams. -/
theorem seamFullContraction_incl_mem_bifiltration_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] [CharP R 2] {u v : ℝ} {c : SeamRetainedCoordinates R n m}
    (hc : c ∈ seamRetainedBifiltrationLevel G H hG hH R u v) :
    (seamFullContraction G H hG hH R).incl c ∈
      laurentBifiltrationLevel (connectedSumSeamGrid G H hG hH) R u v := by
  rw [seamFullContraction_incl_apply]
  exact Submodule.sub_mem _ hc
    (seamFullContraction_homotopy_mem_bifiltration_of_last_O G H hG hH hO R
      (laurentDifferential_mem_bifiltrationLevel _ _ _ _ _ hc))

/-- The corrected projection has shift zero in both filtrations on prepared seams. -/
theorem seamFullContraction_proj_mem_bifiltration_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] [CharP R 2] {u v : ℝ} {c : LaurentChain R (n + m + 1)}
    (hc : c ∈ laurentBifiltrationLevel (connectedSumSeamGrid G H hG hH) R u v) :
    (seamFullContraction G H hG hH R).proj c ∈
      seamRetainedBifiltrationLevel G H hG hH R u v := by
  rw [seamFullContraction_proj_apply]
  exact seamRetainedProjection_mem_bifiltration G H hG hH R (Submodule.sub_mem _ hc
    (laurentDifferential_mem_bifiltrationLevel _ _ _ _ _
      (seamFullContraction_homotopy_mem_bifiltration_of_last_O G H hG hH hO R hc)))

/-- The actual retained differential preserves both filtrations. -/
theorem seamRetainedDifferential_mem_bifiltration_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] [CharP R 2] {u v : ℝ} {c : SeamRetainedCoordinates R n m}
    (hc : c ∈ seamRetainedBifiltrationLevel G H hG hH R u v) :
    seamRetainedDifferential G H hG hH R c ∈
      seamRetainedBifiltrationLevel G H hG hH R u v := by
  have hi := seamFullContraction_incl_mem_bifiltration_of_last_O G H hG hH hO R hc
  have hp := seamFullContraction_proj_mem_bifiltration_of_last_O G H hG hH hO R
    (laurentDifferential_mem_bifiltrationLevel _ _ _ _ _ hi)
  rw [(seamFullContraction G H hG hH R).proj_dM_apply,
    (seamFullContraction G H hG hH R).proj_incl_apply] at hp
  exact hp

end OnLeConjecture.KnotFloer.GridFull

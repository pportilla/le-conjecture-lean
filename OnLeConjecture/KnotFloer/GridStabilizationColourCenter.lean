/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationColourGeometry
public import OnLeConjecture.KnotFloer.GridStabilizationColourClifford

/-!
# The center block of the transferred colour derivative of a stabilization

Let `A = G.stabilizeX s.castSucc (G.X s).castSucc s` and let `T` be the transfer of the colour
derivative `Ψ = oDerivative R A P` to `C(G) × C(G)` along `fullStabilizationTransferredRetraction`
(`stabilizationColourTransfer`). This file proves that the block of `T` from the second copy to the
second copy, the copy of the center states, is exactly the colour derivative of `G` for the column
set `P_G = {c | s.castSucc.succAbove c ∈ P}` (`stabilizationColourTransfer_center`). No condition
on `P` is needed: the new `O` marking never contributes to this block.

The proof has three steps.

* The inclusion of the second copy is the matching inclusion
  `z ↦ c(z) + S (1 + T_m)⁻¹ E_n(z)`, where `c` inserts the center, `S` includes the noncritical
  matching sources, `E_n` is the entry block and `T_m` the internal transition
  (`fullStabilizationTransferredRetraction_incl_second_eq_matching`). The proof reads the target
  coefficients of the chain equation of the inclusion, which vanish because the inclusion is
  supported on matching sources and centers.
* With the matching form of the second projection (`GridStabilizationMatchingSchur`), the block is
  a sum of four matching terms with one derivative factor. Every matching path with at least two
  internal steps ends at a node from which no empty rectangle reaches a center
  (`StabilizationLongMatchingPath.no_exit`), so only the direct, two-rectangle and
  three-rectangle paths survive (`stabilizationColourTransfer_center_single`).
* The colour weight satisfies the Leibniz rule, and the `O` columns of the pieces of a short path
  partition the `O` columns of the reconstructed rectangle with the new column removed
  (`GridStabilizationColourGeometry`). The bijections of `GridStabilizationMatchingTwoPath`,
  `GridStabilizationMatchingThreePathEquiv` and `GridStabilizationStandardDecomposition` then
  identify the sum with the derivative of the old grid.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R]

/-! ### Supports along matching steps -/

section Supports

/-- Every node in the support is reached from the center of `x` by an entry rectangle followed by
finitely many matching steps. -/
def StabilizationReachSupported (x : GridState n)
    (w : StabilizationMatchingNode G s →₀ LaurentPolynomial R) : Prop :=
  ∀ z ∈ w.support, ∃ a : StabilizationMatchingNode G s,
    (∃ r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a), r.IsEmpty) ∧
    Relation.ReflTransGen (StabilizationMatchingStep G s) a z

/-- Every node in the support is reached by an entry rectangle and at least one matching step. -/
def StabilizationStepSupported (x : GridState n)
    (w : StabilizationMatchingNode G s →₀ LaurentPolynomial R) : Prop :=
  ∀ z ∈ w.support, ∃ a b : StabilizationMatchingNode G s,
    (∃ r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a), r.IsEmpty) ∧
    StabilizationMatchingStep G s a b ∧ Relation.ReflTransGen (StabilizationMatchingStep G s) b z

/-- Every node in the support ends a matching path with at least two internal steps. -/
def StabilizationLongSupported (x : GridState n)
    (w : StabilizationMatchingNode G s →₀ LaurentPolynomial R) : Prop :=
  ∀ z ∈ w.support, StabilizationLongMatchingPath G s x z

/-- A node operator whose nonzero matrix entries are matching steps. -/
def IsStabilizationStepOperator
    (U : Module.End (LaurentPolynomial R) (StabilizationMatchingNode G s →₀ LaurentPolynomial R)) :
    Prop :=
  ∀ a b, U (single a 1) b ≠ 0 → StabilizationMatchingStep G s a b

variable {G s R}

theorem IsStabilizationStepOperator.support_predecessor
    {U : Module.End (LaurentPolynomial R) (StabilizationMatchingNode G s →₀ LaurentPolynomial R)}
    (hU : IsStabilizationStepOperator G s R U)
    (w : StabilizationMatchingNode G s →₀ LaurentPolynomial R) {z : StabilizationMatchingNode G s}
    (hz : z ∈ (U w).support) : ∃ a ∈ w.support, StabilizationMatchingStep G s a z := by
  classical
  let := Fintype.ofFinite (StabilizationMatchingNode G s)
  rw [Finsupp.mem_support_iff, finiteEnd_apply_apply] at hz
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  refine ⟨a, Finsupp.mem_support_iff.mpr ?_, hU a z ?_⟩
  · intro h
    exact ha (by rw [h, zero_mul])
  · intro h
    exact ha (by rw [h, mul_zero])

theorem StabilizationReachSupported.step {x : GridState n}
    {U : Module.End (LaurentPolynomial R) (StabilizationMatchingNode G s →₀ LaurentPolynomial R)}
    (hU : IsStabilizationStepOperator G s R U) {w : StabilizationMatchingNode G s →₀ _}
    (hw : StabilizationReachSupported G s R x w) : StabilizationStepSupported G s R x (U w) := by
  intro z hz
  obtain ⟨b, hb, hbz⟩ := hU.support_predecessor w hz
  obtain ⟨a, he, hab⟩ := hw b hb
  rcases Relation.ReflTransGen.cases_head hab with rfl | ⟨c, hac, hcb⟩
  · exact ⟨a, z, he, hbz, Relation.ReflTransGen.refl⟩
  · exact ⟨a, c, he, hac, hcb.tail hbz⟩

theorem StabilizationReachSupported.reach {x : GridState n}
    {U : Module.End (LaurentPolynomial R) (StabilizationMatchingNode G s →₀ LaurentPolynomial R)}
    (hU : IsStabilizationStepOperator G s R U) {w : StabilizationMatchingNode G s →₀ _}
    (hw : StabilizationReachSupported G s R x w) : StabilizationReachSupported G s R x (U w) := by
  intro z hz
  obtain ⟨b, hb, hbz⟩ := hU.support_predecessor w hz
  obtain ⟨a, he, hab⟩ := hw b hb
  exact ⟨a, he, hab.tail hbz⟩

theorem StabilizationStepSupported.long {x : GridState n}
    {U : Module.End (LaurentPolynomial R) (StabilizationMatchingNode G s →₀ LaurentPolynomial R)}
    (hU : IsStabilizationStepOperator G s R U) {w : StabilizationMatchingNode G s →₀ _}
    (hw : StabilizationStepSupported G s R x w) : StabilizationLongSupported G s R x (U w) := by
  intro z hz
  obtain ⟨b', hb', hbz⟩ := hU.support_predecessor w hz
  obtain ⟨a, b, he, hab, hbb'⟩ := hw b' hb'
  rcases Relation.ReflTransGen.cases_head hbb' with rfl | ⟨c, hbc, hcb'⟩
  · exact ⟨a, b, z, he, hab, hbz, Relation.ReflTransGen.refl⟩
  · exact ⟨a, b, c, he, hab, hbc, hcb'.tail hbz⟩

theorem StabilizationLongSupported.long {x : GridState n}
    {U : Module.End (LaurentPolynomial R) (StabilizationMatchingNode G s →₀ LaurentPolynomial R)}
    (hU : IsStabilizationStepOperator G s R U) {w : StabilizationMatchingNode G s →₀ _}
    (hw : StabilizationLongSupported G s R x w) : StabilizationLongSupported G s R x (U w) := by
  intro z hz
  obtain ⟨b, hb, hbz⟩ := hU.support_predecessor w hz
  exact (hw b hb).tail G s hbz

/-- A support predicate that is closed under sums, scalar multiples and a step operator is
preserved by the matching inverse. -/
theorem matchingInverse_preserves
    (Q : (StabilizationMatchingNode G s →₀ LaurentPolynomial R) → Prop)
    (hzero : Q 0) (hadd : ∀ v w, Q v → Q w → Q (v + w))
    (hsmul : ∀ (a : LaurentPolynomial R) v, Q v → Q (a • v))
    (hT : ∀ v, Q v → Q (stabilizationMatchingTransition G s R v))
    {w : StabilizationMatchingNode G s →₀ LaurentPolynomial R} (hw : Q w) :
    Q (stabilizationMatchingInverse G s R w) := by
  obtain ⟨k, hk⟩ := stabilizationMatchingTransition_locallyNilpotent G s R w
  have h := matchingInverse_apply_eq_geom_sum (stabilizationMatchingTransition G s R)
    (isUnit_one_add_stabilizationMatchingTransition G s R).unit
    (isUnit_one_add_stabilizationMatchingTransition G s R).unit_spec w k hk
  change stabilizationMatchingInverse G s R w = _ at h
  rw [h, LinearMap.sum_apply]
  have hpow (j : ℕ) : Q ((stabilizationMatchingTransition G s R ^ j) w) := by
    induction j with
    | zero => simpa using hw
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hT _ ih
  have hneg (j : ℕ) : Q (((-stabilizationMatchingTransition G s R) ^ j) w) := by
    rw [neg_pow, Module.End.mul_apply]
    rcases neg_one_pow_eq_or (Module.End (LaurentPolynomial R)
        (StabilizationMatchingNode G s →₀ LaurentPolynomial R)) j with h | h
    · rw [h, Module.End.one_apply]
      exact hpow j
    · rw [h, LinearMap.neg_apply, Module.End.one_apply, ← neg_one_smul (LaurentPolynomial R)]
      exact hsmul _ _ (hpow j)
  induction (Finset.range k) using Finset.induction_on with
  | empty => simpa using hzero
  | insert j t hj ih =>
    rw [Finset.sum_insert hj]
    exact hadd _ _ (hneg j) ih

theorem StabilizationReachSupported.zero {x : GridState n} :
    StabilizationReachSupported G s R x 0 := by
  intro z hz
  simp at hz

theorem StabilizationReachSupported.add {x : GridState n} {v w : StabilizationMatchingNode G s →₀ _}
    (hv : StabilizationReachSupported G s R x v) (hw : StabilizationReachSupported G s R x w) :
    StabilizationReachSupported G s R x (v + w) := by
  classical
  intro z hz
  rcases Finset.mem_union.mp (Finsupp.support_add hz) with h | h
  · exact hv z h
  · exact hw z h

theorem StabilizationReachSupported.smul {x : GridState n} (a : LaurentPolynomial R)
    {v : StabilizationMatchingNode G s →₀ _} (hv : StabilizationReachSupported G s R x v) :
    StabilizationReachSupported G s R x (a • v) :=
  fun z hz => hv z (Finsupp.support_smul hz)

theorem StabilizationLongSupported.zero {x : GridState n} :
    StabilizationLongSupported G s R x 0 := by
  intro z hz
  simp at hz

theorem StabilizationLongSupported.add {x : GridState n} {v w : StabilizationMatchingNode G s →₀ _}
    (hv : StabilizationLongSupported G s R x v) (hw : StabilizationLongSupported G s R x w) :
    StabilizationLongSupported G s R x (v + w) := by
  classical
  intro z hz
  rcases Finset.mem_union.mp (Finsupp.support_add hz) with h | h
  · exact hv z h
  · exact hw z h

theorem StabilizationLongSupported.smul {x : GridState n} (a : LaurentPolynomial R)
    {v : StabilizationMatchingNode G s →₀ _} (hv : StabilizationLongSupported G s R x v) :
    StabilizationLongSupported G s R x (a • v) :=
  fun z hz => hv z (Finsupp.support_smul hz)

variable (G s R)

theorem isStabilizationStepOperator_transition :
    IsStabilizationStepOperator G s R (stabilizationMatchingTransition G s R) :=
  stabilizationMatchingStep_of_transition_ne_zero G s R

theorem exists_isEmpty_of_colRectCoeff_ne_zero {m : ℕ} (H : GridDiagram m)
    (φ : Finset (Fin m) → LaurentPolynomial R) {a b : GridState m}
    (h : colRectCoeff H φ a b ≠ 0) : ∃ r : GridRectangleBetween a b, r.IsEmpty := by
  classical
  have hn : (GridRectangleBetween.emptyRectangles a b).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    exact h (by rw [colRectCoeff, hn, Finset.sum_empty])
  obtain ⟨r, hr⟩ := hn
  exact ⟨r, (GridRectangleBetween.mem_emptyRectangles r).mp hr⟩

theorem isStabilizationStepOperator_weightedTransition
    (φ : Finset (Fin (n + 1)) → LaurentPolynomial R) :
    IsStabilizationStepOperator G s R (stabilizationWeightedTransition G s φ) := by
  classical
  intro a b h
  rw [stabilizationWeightedTransition_single_apply] at h
  split_ifs at h with hab
  · exact False.elim (h rfl)
  · exact ⟨hab, exists_isEmpty_of_colRectCoeff_ne_zero R _ φ h⟩

theorem stabilizationReachSupported_weightedEntry
    (φ : Finset (Fin (n + 1)) → LaurentPolynomial R) (x : GridState n) :
    StabilizationReachSupported G s R x (stabilizationWeightedEntry G s φ (single x 1)) := by
  intro z hz
  rw [Finsupp.mem_support_iff, stabilizationWeightedEntry_single_apply] at hz
  exact ⟨z, exists_isEmpty_of_colRectCoeff_ne_zero R _ φ hz, Relation.ReflTransGen.refl⟩

theorem stabilizationWeightedExit_eq_zero_of_long (φ : Finset (Fin (n + 1)) → LaurentPolynomial R)
    {x : GridState n} {w : StabilizationMatchingNode G s →₀ LaurentPolynomial R}
    (hw : StabilizationLongSupported G s R x w) : stabilizationWeightedExit G s φ w = 0 := by
  classical
  apply Finsupp.ext
  intro y
  rw [laurentMap_apply_apply, Finsupp.zero_apply]
  apply Finset.sum_eq_zero
  intro z hz
  dsimp only
  rw [stabilizationWeightedExit_single_apply]
  have hcoeff : colRectCoeff (G.stabilizeX s.castSucc (G.X s).castSucc s) φ z.val
      (y.insertPoint s.succ (G.X s).succ) = 0 := by
    by_contra hne
    obtain ⟨r, hr⟩ := exists_isEmpty_of_colRectCoeff_ne_zero R _ φ hne
    exact (hw z hz).no_exit G s y r hr
  rw [hcoeff, mul_zero]

end Supports

/-! ### The matching form of the inclusion of the center copy -/

variable [CharP R 2]

omit [CharP R 2] in
theorem laurentModule_sub_eq_add [CharP R 2] {M : Type*} [AddCommGroup M]
    [Module (LaurentPolynomial R) M] (a b : M) : a - b = a + b := by
  rw [sub_eq_add_neg, ← neg_one_smul (LaurentPolynomial R) b, CharTwo.neg_eq, one_smul]

/-- The inclusion of the second copy is the matching inclusion. -/
theorem fullStabilizationTransferredRetraction_incl_second_eq_matching (z : LaurentChain R n) :
    (fullStabilizationTransferredRetraction G s R).incl (0, z) =
      laurentStabilizationCenterInclusion G s R z +
        stabilizationMatchingSourceInclusion G s R
          (stabilizationMatchingInverse G s R (stabilizationMatchingEntry G s R z)) := by
  classical
  have hι := fullStabilizationTransferredRetraction_incl_second G s R z
  have htarget (w : LaurentChain R n × LaurentChain R n) :
      stabilizationMatchingTargetProjection G s R
        ((fullStabilizationTransferredRetraction G s R).incl w) = 0 := by
    apply Finsupp.ext
    intro a
    rw [stabilizationMatchingTargetProjection_apply, Finsupp.zero_apply]
    have hk := fullStabilizationTransferredRetraction_incl_mem_kernelSupport G s R w
    apply (Finsupp.mem_supported' _ _).mp hk
    rintro (h | h)
    · exact (rowMatchingSource_swapRows G s a.val).mp h a.property.1
    · rw [stabilizationMatchingTargetState_newColumn] at h
      apply (stabilizationMatchingNode_row_columns_ne_newColumn G s a).2
      rw [← h, GridState.transpose_apply_apply]
  have hd : laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
      ((fullStabilizationTransferredRetraction G s R).incl (0, z)) =
      (fullStabilizationTransferredRetraction G s R).incl (0, laurentDifferential G R z) := by
    rw [(fullStabilizationTransferredRetraction G s R).dM_incl_apply,
      stabilizationTransferredDifferential_apply_eq_old_double, map_zero]
  have h0 := htarget (0, laurentDifferential G R z)
  rw [← hd, hι, map_sub, map_sub] at h0
  set v := (fullStabilizationTransferredRetraction G s R).homotopy
    (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
      (laurentStabilizationCenterInclusion G s R z)) with hvdef
  have hsupp (y : GridState (n + 1)) (hy : v y ≠ 0) :
      RowMatchingSource s (G.X s) y ∧ y s.succ ≠ (G.X s).castSucc := by
    refine ⟨?_, ?_⟩
    · by_contra hns
      exact hy (fullStabilizationTransferredRetraction_homotopy_apply_of_not_source G s R _ y hns)
    · intro hsw
      obtain ⟨x', hx'⟩ := exists_stabilizationPartnerState_of_southwest G s y hsw
      apply hy
      rw [← hx']
      exact fullStabilizationTransferredRetraction_homotopy_apply_partner G s R _ x'
  set v' : StabilizationMatchingNode G s →₀ LaurentPolynomial R :=
    Finsupp.comapDomain Subtype.val v Subtype.val_injective.injOn with hv'def
  have hv : v = stabilizationMatchingSourceInclusion G s R v' := by
    apply Finsupp.ext
    intro y
    rw [show stabilizationMatchingSourceInclusion G s R v' = Finsupp.mapDomain Subtype.val v'
      from rfl]
    by_cases hy : RowMatchingSource s (G.X s) y ∧ y s.succ ≠ (G.X s).castSucc
    · have h := Finsupp.mapDomain_apply Subtype.val_injective v'
        (⟨y, hy⟩ : StabilizationMatchingNode G s)
      rw [show y = (⟨y, hy⟩ : StabilizationMatchingNode G s).val from rfl, h]
      rfl
    · have h := Finsupp.mapDomain_of_notMem_range
        (f := (Subtype.val : StabilizationMatchingNode G s → GridState (n + 1))) v' y
        (by rintro ⟨y', rfl⟩; exact hy y'.property)
      rw [h]
      by_contra hne
      exact hy (hsupp y hne)
  rw [hv] at h0
  have hM : stabilizationMatchingTargetProjection G s R
      (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
        (stabilizationMatchingSourceInclusion G s R v')) =
      (1 + stabilizationMatchingTransition G s R) v' := by
    rw [one_add_stabilizationMatchingTransition_eq]
    rfl
  rw [hM, sub_eq_zero] at h0
  have hv' : v' = stabilizationMatchingInverse G s R (stabilizationMatchingEntry G s R z) := by
    change _ = stabilizationMatchingInverse G s R
      (stabilizationMatchingTargetProjection G s R
        (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
          (laurentStabilizationCenterInclusion G s R z)))
    rw [h0, ← LinearMap.comp_apply, stabilizationMatchingInverse_comp_internal,
      LinearMap.id_apply]
  rw [hι, hv, hv', laurentModule_sub_eq_add (R := R)]

/-! ### The center block as a sum of matching terms -/

variable (P : Finset (Fin (n + 1)))

/-- The center block of the transferred colour derivative, before truncation. -/
theorem stabilizationColourTransfer_center_matching (z : LaurentChain R n) :
    (stabilizationColourTransfer G s R P (0, z)).2 =
      stabilizationWeightedDirect G s (colourWeight P) z +
        stabilizationMatchingExit G s R (stabilizationMatchingInverse G s R
          (stabilizationWeightedEntry G s (colourWeight P) z)) +
        stabilizationWeightedExit G s (colourWeight P)
          (stabilizationMatchingInverse G s R (stabilizationMatchingEntry G s R z)) +
        stabilizationMatchingExit G s R (stabilizationMatchingInverse G s R
          (stabilizationWeightedTransition G s (colourWeight P)
            (stabilizationMatchingInverse G s R (stabilizationMatchingEntry G s R z)))) := by
  have hΨ := oDerivative_eq_colRectMap (R := R) (G.stabilizeX s.castSucc (G.X s).castSucc s) P
  have hπ := stabilizationSecondProjection_decomposition G s R
  rw [stabilizationMatchingSecondProjection_eq_exit_inverse] at hπ
  change stabilizationSecondProjection G s R
      (oDerivative R (G.stabilizeX s.castSucc (G.X s).castSucc s) P
        ((fullStabilizationTransferredRetraction G s R).incl (0, z))) = _
  rw [fullStabilizationTransferredRetraction_incl_second_eq_matching, hπ, hΨ,
    stabilizationWeightedTransition_eq_internal G s _ (colourWeight_empty P)]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, stabilizationWeightedDirect,
    stabilizationWeightedEntry, stabilizationWeightedExit, stabilizationWeightedInternal]
  abel

/-- After truncation, the center block on a generator is a sum over direct, two-rectangle and
three-rectangle matching terms with one derivative factor. -/
theorem stabilizationColourTransfer_center_single (x : GridState n) :
    (stabilizationColourTransfer G s R P (0, single x 1)).2 =
      stabilizationWeightedDirect G s (colourWeight P) (single x 1) +
        (stabilizationMatchingExit G s R (stabilizationWeightedEntry G s (colourWeight P)
            (single x 1)) +
          stabilizationWeightedExit G s (colourWeight P)
            (stabilizationMatchingEntry G s R (single x 1))) +
        (stabilizationMatchingExit G s R (stabilizationMatchingTransition G s R
            (stabilizationWeightedEntry G s (colourWeight P) (single x 1))) +
          stabilizationWeightedExit G s (colourWeight P)
            (stabilizationMatchingTransition G s R
              (stabilizationMatchingEntry G s R (single x 1))) +
          stabilizationMatchingExit G s R (stabilizationWeightedTransition G s (colourWeight P)
            (stabilizationMatchingEntry G s R (single x 1)))) := by
  set E := stabilizationMatchingExit G s R
  set F := stabilizationMatchingEntry G s R (single x 1)
  set Tr := stabilizationMatchingTransition G s R
  set Ec := stabilizationWeightedExit G s (colourWeight (R := R) P)
  set Fc := stabilizationWeightedEntry G s (colourWeight (R := R) P) (single x 1)
  set Ic := stabilizationWeightedTransition G s (colourWeight (R := R) P)
  set u := (isUnit_one_add_stabilizationMatchingTransition G s R).unit
  have hu : (u : Module.End (LaurentPolynomial R) _) = 1 + Tr :=
    (isUnit_one_add_stabilizationMatchingTransition G s R).unit_spec
  have hTr := isStabilizationStepOperator_transition G s R
  have hIc := isStabilizationStepOperator_weightedTransition G s R (colourWeight P)
  have hF : StabilizationReachSupported G s R x F := by
    have h := stabilizationReachSupported_weightedEntry G s R
      (fun Q => LaurentPolynomial.T (Q.card : ℤ)) x
    rwa [stabilizationWeightedEntry_laurent] at h
  have hFc : StabilizationReachSupported G s R x Fc :=
    stabilizationReachSupported_weightedEntry G s R (colourWeight P) x
  have hEkill {w} (hw : StabilizationLongSupported G s R x w) : E w = 0 := by
    have h := stabilizationWeightedExit_eq_zero_of_long G s R
      (fun Q => LaurentPolynomial.T (Q.card : ℤ)) hw
    rwa [stabilizationWeightedExit_laurent] at h
  have hEckill {w} (hw : StabilizationLongSupported G s R x w) : Ec w = 0 :=
    stabilizationWeightedExit_eq_zero_of_long G s R (colourWeight P) hw
  have hpowLong {w} (hw : StabilizationReachSupported G s R x w) (k : ℕ) :
      StabilizationLongSupported G s R x ((Tr ^ (k + 2)) w) := by
    induction k with
    | zero =>
      rw [pow_two, Module.End.mul_apply]
      exact (hw.step hTr).long hTr
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact ih.long hTr
  have hMinvLong {w} (hw : StabilizationLongSupported G s R x w) :
      StabilizationLongSupported G s R x (stabilizationMatchingInverse G s R w) :=
    matchingInverse_preserves (G := G) (s := s) (R := R) _ StabilizationLongSupported.zero
      (fun _ _ hv hw => hv.add hw) (fun a _ hv => hv.smul a) (fun _ hv => hv.long hTr) hw
  have hMinvReach {w} (hw : StabilizationReachSupported G s R x w) :
      StabilizationReachSupported G s R x (stabilizationMatchingInverse G s R w) :=
    matchingInverse_preserves (G := G) (s := s) (R := R) _ StabilizationReachSupported.zero
      (fun _ _ hv hw => hv.add hw) (fun a _ hv => hv.smul a) (fun _ hv => hv.reach hTr) hw
  -- the first truncation
  have h1 : E (stabilizationMatchingInverse G s R Fc) = E Fc - E (Tr Fc) :=
    matchingInverse_apply_truncate_two Tr u hu E Fc
      (stabilizationMatchingTransition_locallyNilpotent G s R Fc)
      (fun k => hEkill (hpowLong hFc k))
  -- the second truncation
  have h2 : Ec (stabilizationMatchingInverse G s R F) = Ec F - Ec (Tr F) :=
    matchingInverse_apply_truncate_two Tr u hu Ec F
      (stabilizationMatchingTransition_locallyNilpotent G s R F)
      (fun k => hEckill (hpowLong hF k))
  -- the third truncation
  have hrec : stabilizationMatchingInverse G s R F =
      F - Tr (stabilizationMatchingInverse G s R F) := by
    have h := LinearMap.congr_fun (stabilizationMatchingInternal_comp_inverse G s R) F
    rw [LinearMap.comp_apply, LinearMap.add_apply, Module.End.one_apply, LinearMap.id_apply] at h
    exact eq_sub_of_add_eq h
  have hlong1 : StabilizationLongSupported G s R x
      (Ic (Tr (stabilizationMatchingInverse G s R F))) :=
    ((hMinvReach hF).step hTr).long hIc
  have hstep2 : StabilizationStepSupported G s R x (Ic F) := hF.step hIc
  have hLongPow {w} (hw : StabilizationLongSupported G s R x w) (k : ℕ) :
      StabilizationLongSupported G s R x ((Tr ^ k) w) := by
    induction k with
    | zero =>
      rw [pow_zero, Module.End.one_apply]
      exact hw
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact ih.long hTr
  have h3' : E (stabilizationMatchingInverse G s R (Ic F)) = E (Ic F) - E (Tr (Ic F)) := by
    refine matchingInverse_apply_truncate_two Tr u hu E (Ic F)
      (stabilizationMatchingTransition_locallyNilpotent G s R _) fun k => hEkill ?_
    rw [pow_succ, Module.End.mul_apply]
    exact hLongPow (hstep2.long hTr) (k + 1)
  have h3 : E (stabilizationMatchingInverse G s R (Ic (stabilizationMatchingInverse G s R F))) =
      E (Ic F) := by
    conv_lhs => rw [hrec]
    rw [map_sub, map_sub, map_sub, hEkill (hMinvLong hlong1), sub_zero, h3',
      hEkill (hstep2.long hTr), sub_zero]
  rw [stabilizationColourTransfer_center_matching, h1, h2, h3]
  simp only [laurentModule_sub_eq_add (R := R)]
  abel

/-! ### Evaluation on the short matching paths -/

/-- The colour weight of the new-column deletion of a rectangle of the stabilized grid. -/
def stabilizationColourStandardWeight {x y : GridState n}
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ)) : LaurentPolynomial R :=
  colourWeight P (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
    r.toGridRectangle).erase s.castSucc)

omit [CharP R 2] in
theorem stabilizationColour_two_path_weight {x y : GridState n}
    (p : StabilizationMatchingTwoPath G s x y) :
    colourWeight P ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.1.val.toGridRectangle) *
        LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.2.val.toGridRectangle).card : ℤ) +
      LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.1.val.toGridRectangle).card : ℤ) *
        colourWeight P ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.2.val.toGridRectangle) =
      stabilizationColourStandardWeight G s R P (stabilizationMatchingTwoPathRectangle G s p) := by
  obtain ⟨hdisj, hunion⟩ := OColumns_stabilizationMatchingTwoPath G s p
  rw [stabilizationColourStandardWeight, ← hunion, colourWeight_union P hdisj]

omit [CharP R 2] in
theorem colourWeight_three {m : ℕ} (P' : Finset (Fin m)) {A B C : Finset (Fin m)}
    (h12 : Disjoint A B) (h3 : Disjoint (A ∪ B) C) :
    colourWeight P' A * LaurentPolynomial.T (B.card : ℤ) * LaurentPolynomial.T (C.card : ℤ) +
        LaurentPolynomial.T (A.card : ℤ) * LaurentPolynomial.T (B.card : ℤ) * colourWeight P' C +
        LaurentPolynomial.T (A.card : ℤ) * colourWeight P' B * LaurentPolynomial.T (C.card : ℤ) =
      colourWeight (R := R) P' (A ∪ B ∪ C) := by
  rw [colourWeight_union P' h3, colourWeight_union P' h12, Finset.card_union_of_disjoint h12,
    Nat.cast_add, LaurentPolynomial.T_add]
  ring

omit [CharP R 2] in
theorem stabilizationColour_three_path_weight {x y : GridState n}
    (p : StabilizationMatchingThreePath G s x y) :
    colourWeight P ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.2.1.val.toGridRectangle) *
        LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.2.2.1.val.toGridRectangle).card : ℤ) *
        LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.2.2.2.val.toGridRectangle).card : ℤ) +
      LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.2.1.val.toGridRectangle).card : ℤ) *
        LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.2.2.1.val.toGridRectangle).card : ℤ) *
        colourWeight P ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.2.2.2.val.toGridRectangle) +
      LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.2.1.val.toGridRectangle).card : ℤ) *
        colourWeight P ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.2.2.1.val.toGridRectangle) *
        LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
          p.2.2.2.2.val.toGridRectangle).card : ℤ) =
      stabilizationColourStandardWeight G s R P
        (stabilizationMatchingThreePathRectangle G s p) := by
  obtain ⟨h12, h3, hunion⟩ := OColumns_stabilizationMatchingThreePath G s p
  rw [stabilizationColourStandardWeight, ← hunion]
  exact colourWeight_three R P h12 h3

omit [CharP R 2] in
theorem sum_stabilizationColour_two_paths (x y : GridState n) :
    ∑ p ∈ stabilizationMatchingTwoPaths G s x y,
        (colourWeight P ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.1.val.toGridRectangle) *
          LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.val.toGridRectangle).card : ℤ) +
        LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.1.val.toGridRectangle).card : ℤ) *
          colourWeight P ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.val.toGridRectangle)) =
      ∑ r ∈ stabilizationMatchingTwoRectangles G s x y,
        stabilizationColourStandardWeight G s R P r := by
  classical
  apply Finset.sum_nbij (stabilizationMatchingTwoPathRectangle G s)
  · intro p _
    exact (mem_stabilizationMatchingTwoRectangles G s _).mpr
      (stabilizationMatchingTwoPathRectangle_properties G s p)
  · intro p _ q _ h
    exact stabilizationMatchingTwoPathRectangle_injective G s h
  · intro r hr
    change r ∈ stabilizationMatchingTwoRectangles G s x y at hr
    rw [mem_stabilizationMatchingTwoRectangles] at hr
    obtain ⟨p, hp⟩ := exists_matchingTwoPath_of_bottom G s r hr.1 hr.2.1 hr.2.2
    exact ⟨p, mem_stabilizationMatchingTwoPaths G s p, hp⟩
  · intro p _
    exact stabilizationColour_two_path_weight G s R P p

omit [CharP R 2] in
theorem sum_stabilizationColour_three_paths (x y : GridState n) :
    ∑ p ∈ stabilizationMatchingThreePaths G s x y,
        (colourWeight P ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.1.val.toGridRectangle) *
          LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.2.1.val.toGridRectangle).card : ℤ) *
          LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.2.2.val.toGridRectangle).card : ℤ) +
        LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.1.val.toGridRectangle).card : ℤ) *
          LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.2.1.val.toGridRectangle).card : ℤ) *
          colourWeight P ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.2.2.val.toGridRectangle) +
        LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.1.val.toGridRectangle).card : ℤ) *
          colourWeight P ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.2.1.val.toGridRectangle) *
          LaurentPolynomial.T (((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns
            p.2.2.2.2.val.toGridRectangle).card : ℤ)) =
      ∑ r ∈ stabilizationMatchingThreeRectangles G s x y,
        stabilizationColourStandardWeight G s R P r := by
  classical
  apply Finset.sum_nbij (stabilizationMatchingThreePathRectangle G s)
  · intro p _
    exact (mem_stabilizationMatchingThreeRectangles G s _).mpr
      (stabilizationMatchingThreePathRectangle_properties G s p)
  · intro p _ q _ h
    exact stabilizationMatchingThreePathRectangle_injective G s h
  · intro r hr
    change r ∈ stabilizationMatchingThreeRectangles G s x y at hr
    rw [mem_stabilizationMatchingThreeRectangles] at hr
    obtain ⟨p, hp⟩ := exists_matchingThreePath_of_bottom_ne G s r hr.1 hr.2.1 hr.2.2
    exact ⟨p, mem_stabilizationMatchingThreePaths G s p, hp⟩
  · intro p _
    exact stabilizationColour_three_path_weight G s R P p

omit [CharP R 2] in
open Classical in
/-- The direct term is the sum over the empty admissible rectangles. -/
theorem stabilizationWeightedDirect_colour_single_apply (x y : GridState n) :
    stabilizationWeightedDirect G s (colourWeight P) (single x 1) y =
      ∑ r ∈ (stabilizationAdmissibleRectangles G s x y).filter (fun r => r.IsEmpty),
        stabilizationColourStandardWeight G s R P r := by
  classical
  rw [stabilizationWeightedDirect_single_apply, colRectCoeff,
    stabilizationAdmissibleRectangles_filter_isEmpty]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have he := (GridRectangleBetween.mem_emptyRectangles ρ).mp hρ
  obtain ⟨r, rfl⟩ := GridRectangleBetween.exists_insertPoint_eq ρ
  have hXs := ((isEmpty_insertStabilizationCenter_iff G s r).mp he).2
  rw [stabilizationColourStandardWeight, G.OColumns_stabilizeX_insertPoint hXs,
    Finset.erase_eq_of_notMem]
  intro hmem
  obtain ⟨c, _, hc⟩ := Finset.mem_map.mp hmem
  exact Fin.succAbove_ne _ c hc

omit [CharP R 2] in
open Classical in
theorem sum_stabilizationColourStandardWeight_partition (x y : GridState n) :
    ∑ r ∈ stabilizationAdmissibleRectangles G s x y,
        stabilizationColourStandardWeight G s R P r =
      (∑ r ∈ (stabilizationAdmissibleRectangles G s x y).filter (fun r => r.IsEmpty),
        stabilizationColourStandardWeight G s R P r) +
      (∑ r ∈ stabilizationMatchingTwoRectangles G s x y,
        stabilizationColourStandardWeight G s R P r) +
      (∑ r ∈ stabilizationMatchingThreeRectangles G s x y,
        stabilizationColourStandardWeight G s R P r) := by
  classical
  rw [stabilizationMatchingTwoRectangles, stabilizationMatchingThreeRectangles]
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have ha := (mem_stabilizationAdmissibleRectangles G s r).mp hr
  by_cases he : r.IsEmpty
  · have hi := stabilizationCenter_not_mem_interior_of_isEmpty G s r he
    simp only [he, hi, false_and, ↓reduceIte, add_zero]
  · have hi := stabilizationAdmissibleRectangle_center_mem_of_not_isEmpty G s r ha he
    by_cases hb : r.bottom = (G.X s).castSucc <;> simp [he, hi, hb]

omit [CharP R 2] in
theorem sum_stabilizationColourStandardWeight_eq_oDerivative (x y : GridState n) :
    ∑ r ∈ stabilizationAdmissibleRectangles G s x y,
        stabilizationColourStandardWeight G s R P r =
      oDerivative R G (P.preimage s.castSucc.succAbove
        s.castSucc.succAbove_right_injective.injOn) (single x 1) y := by
  classical
  rw [oDerivative_eq_colRectMap, colRectMap_single_apply, colRectCoeff]
  symm
  apply Finset.sum_nbij (fun r => r.insertPoint s.succ (G.X s).succ)
  · intro r hr
    rw [mem_stabilizationAdmissibleRectangles, stabilizationAdmissibleRectangle_insertPoint_iff]
    exact (GridRectangleBetween.mem_emptyRectangles r).mp hr
  · intro r _ r' _ heq
    exact GridRectangleBetween.insertPoint_injective _ _ heq
  · intro r hr
    obtain ⟨r, rfl⟩ := GridRectangleBetween.exists_insertPoint_eq r
    exact ⟨r, (GridRectangleBetween.mem_emptyRectangles r).mpr
      ((stabilizationAdmissibleRectangle_insertPoint_iff G s r).mp
        ((mem_stabilizationAdmissibleRectangles G s _).mp hr)), rfl⟩
  · intro r _
    rw [stabilizationColourStandardWeight, erase_OColumns_stabilization_lift,
      colourWeight_map]
    rfl

omit [CharP R 2] in
theorem stabilizationColour_two_part [CharP R 2] (x y : GridState n) :
    stabilizationMatchingExit G s R
          (stabilizationWeightedEntry G s (colourWeight P) (single x 1)) y +
        stabilizationWeightedExit G s (colourWeight P)
          (stabilizationMatchingEntry G s R (single x 1)) y =
      ∑ r ∈ stabilizationMatchingTwoRectangles G s x y,
        stabilizationColourStandardWeight G s R P r := by
  rw [← sum_stabilizationColour_two_paths, Finset.sum_add_distrib,
    ← stabilizationWeightedExit_laurent, ← stabilizationWeightedEntry_laurent,
    stabilizationWeightedExit_entry_single_apply_eq_sum_paths,
    stabilizationWeightedExit_entry_single_apply_eq_sum_paths]

omit [CharP R 2] in
theorem stabilizationColour_three_part [CharP R 2] (x y : GridState n) :
    stabilizationMatchingExit G s R (stabilizationMatchingTransition G s R
          (stabilizationWeightedEntry G s (colourWeight P) (single x 1))) y +
        stabilizationWeightedExit G s (colourWeight P)
          (stabilizationMatchingTransition G s R
            (stabilizationMatchingEntry G s R (single x 1))) y +
        stabilizationMatchingExit G s R (stabilizationWeightedTransition G s (colourWeight P)
          (stabilizationMatchingEntry G s R (single x 1))) y =
      ∑ r ∈ stabilizationMatchingThreeRectangles G s x y,
        stabilizationColourStandardWeight G s R P r := by
  have hE := stabilizationWeightedExit_laurent (R := R) G s
  have hF := stabilizationWeightedEntry_laurent (R := R) G s
  have hT := stabilizationWeightedTransition_laurent (R := R) G s
  have e3 := stabilizationWeightedExit_transition_entry_single_apply_eq_sum_paths G s
    (colourWeight P) (fun Q => (LaurentPolynomial.T (Q.card : ℤ) : LaurentPolynomial R))
    (fun Q => (LaurentPolynomial.T (Q.card : ℤ) : LaurentPolynomial R)) x y
  have e4 := stabilizationWeightedExit_transition_entry_single_apply_eq_sum_paths G s
    (fun Q => (LaurentPolynomial.T (Q.card : ℤ) : LaurentPolynomial R))
    (fun Q => (LaurentPolynomial.T (Q.card : ℤ) : LaurentPolynomial R)) (colourWeight P) x y
  have e5 := stabilizationWeightedExit_transition_entry_single_apply_eq_sum_paths G s
    (fun Q => (LaurentPolynomial.T (Q.card : ℤ) : LaurentPolynomial R)) (colourWeight P)
    (fun Q => (LaurentPolynomial.T (Q.card : ℤ) : LaurentPolynomial R)) x y
  rw [hE, hT] at e3
  rw [hT, hF] at e4
  rw [hE, hF] at e5
  rw [← sum_stabilizationColour_three_paths, Finset.sum_add_distrib, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) e3 e4) e5

/-- **The center block of the transferred colour derivative.** The block of the transfer of the
colour derivative of `P` from the center copy to the center copy is the colour derivative of the
old grid for the columns `c` with `s.castSucc.succAbove c ∈ P`. -/
theorem stabilizationColourTransfer_center :
    LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
        stabilizationColourTransfer G s R P ∘ₗ
          LinearMap.inr (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) =
      oDerivative R G (P.preimage s.castSucc.succAbove
        s.castSucc.succAbove_right_injective.injOn) := by
  apply gridLinearMap_ext
  intro x y
  change (stabilizationColourTransfer G s R P (0, single x 1)).2 y = _
  rw [stabilizationColourTransfer_center_single]
  simp only [Finsupp.add_apply]
  rw [stabilizationColour_two_part, stabilizationColour_three_part,
    stabilizationWeightedDirect_colour_single_apply,
    ← sum_stabilizationColourStandardWeight_partition,
    sum_stabilizationColourStandardWeight_eq_oDerivative]

end OnLeConjecture.KnotFloer.GridFull

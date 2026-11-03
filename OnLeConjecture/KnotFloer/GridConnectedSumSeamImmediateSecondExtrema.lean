/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamImmediateFirstBijection
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondFactorShortLift

/-!
# Extremal rows of mixed immediate corrections

Entry and exit emptiness force the shared first-block pivot to carry
row n in one mixed orientation and row zero in the other. These
identities determine the pivot from the retained first-factor state.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- A low embedded second-factor row must be its zero row. -/
theorem seamSecondFactorRow_eq_zero_of_le (x : GridState (n + 1)) (a : Fin (m + 1))
    (h : (seamSecondFactorRow x a).val ≤ n) : a = 0 := by
  by_contra ha
  rw [seamSecondFactorRow_of_ne_zero x a ha, seamRight_val] at h
  have hv : a.val ≠ 0 := fun hh => ha (Fin.ext hh)
  omega

/-- A first-block point's row determines its column from the first state. -/
theorem seamImmediateSecond_pivot_of_value (x : GridState (n + 1)) (z : GridState (m + 1))
    (A : Fin (n + m + 1)) (hA : A.val < n) (a : Fin (n + 1))
    (hv : seamState x z A = seamLeft n m a) : A = seamLeft n m (x.toPerm.symm a) := by
  let c : Fin n := ⟨A.val, hA⟩
  have hc : A = seamLeft n m c.castSucc := Fin.ext rfl
  rw [hc, seamState_left_castSucc] at hv
  have hx : x c.castSucc = a := seamLeft_injective hv
  have hh : x.toPerm.symm a = c.castSucc := x.toPerm.symm_apply_eq.mpr hx.symm
  rw [hh]
  exact hc

section Mixed
variable (p q : SeamRetainedIndex n m) (s : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner s.val).val)
    (f : GridRectangleBetween s.val.val (seamState q.1 q.2)) (he : e.IsEmpty) (hf : f.IsEmpty)
include he hf

theorem seamImmediateSecond_bottom_sides (hle : e.left.val < n) (hrf : f.right.val < n) :
    e.left = f.right ∧ e.right = seamComplementFirst s.val ∧
      f.left = seamComplementSecond s.val := by
  rcases seamImmediateMixed_sides p q s e f he hf (Or.inl ⟨hle, hrf⟩) with h | h
  · exact h.2
  · exact False.elim (seamImmediate_entry_left_not_small p s e h.1 hle)

theorem seamImmediateSecond_top_sides (hre : e.right.val < n) (hlf : f.left.val < n) :
    e.right = f.left ∧ e.left = seamComplementSecond s.val ∧
      f.right = seamComplementFirst s.val := by
  rcases seamImmediateMixed_sides p q s e f he hf (Or.inr ⟨hre, hlf⟩) with h | h
  · exact False.elim (seamImmediate_entry_left_not_small p s e hre h.1)
  · exact h.2

omit hf in
theorem seamImmediateSecond_bottom_entry_rows (hle : e.left.val < n) :
    e.bottom = s.val.val (seamComplementSecond s.val) ∧
      e.top = s.val.val e.left ∧ n < (s.val.val e.left).val := by
  rcases seamMatchingEntry_endpoints p s e he with h | h
  · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.1 ▸ h.2.2.2.2⟩
  · exact False.elim (seamImmediate_entry_left_not_small p s e h.1 hle)

omit hf in
theorem seamImmediateSecond_top_entry_rows (hre : e.right.val < n) :
    e.top = s.val.val (seamComplementFirst s.val) ∧
      e.bottom = s.val.val e.right ∧ n < (s.val.val e.right).val := by
  rcases seamMatchingEntry_endpoints p s e he with h | h
  · exact False.elim (seamImmediate_entry_left_not_small p s e hre h.1)
  · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.1 ▸ h.2.2.2.2⟩

/-- In the entry-left/exit-right orientation, the higher southwest row is n. -/
theorem seamImmediateSecond_second_row_eq_last (hle : e.left.val < n)
    (hrf : f.right.val < n) :
    s.val.val (seamComplementSecond s.val) = seamLeft n m (Fin.last n) := by
  obtain ⟨hA, hP, hQ⟩ := seamImmediateSecond_bottom_sides p q s e f he hf hle hrf
  obtain ⟨heB, heT, hhigh⟩ := seamImmediateSecond_bottom_entry_rows p s e he hle
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem s.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem s.val)
  have hrows := s.property
  change (s.val.val (seamComplementFirst s.val)).val <
    (s.val.val (seamComplementSecond s.val)).val at hrows
  apply Fin.ext
  change (s.val.val (seamComplementSecond s.val)).val = n
  by_contra hn
  have hbn : (s.val.val (seamComplementSecond s.val)).val < n := by omega
  let c := s.val.val.toPerm.symm (seamLeft n m (Fin.last n))
  have hcv : s.val.val c = seamLeft n m (Fin.last n) := s.val.val.toPerm.apply_symm_apply _
  have hcP : c ≠ seamComplementFirst s.val := by
    intro hh
    have hv := congrArg Fin.val hcv
    rw [hh] at hv
    change (s.val.val (seamComplementFirst s.val)).val = n at hv
    omega
  have hcQ : c ≠ seamComplementSecond s.val := by
    intro hh
    have hv := congrArg Fin.val hcv
    rw [hh] at hv
    change (s.val.val (seamComplementSecond s.val)).val = n at hv
    omega
  have hcn : c.val < n := by
    by_contra hh
    have hcSW : c ∈ seamSouthwestColumns s.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨by omega, by rw [hcv]; exact le_rfl⟩
    rw [seamComplement_southwest_eq_pair_of_card_two s.val
      (seamMatchingEntry_southwest_card p s e)] at hcSW
    simp only [Finset.mem_insert, Finset.mem_singleton, hcP, hcQ, or_self] at hcSW
  have hcA : c ≠ e.left := by
    intro hh
    have hv := congrArg Fin.val hcv
    rw [hh] at hv
    change (s.val.val e.left).val = n at hv
    omega
  have hvSource : seamState p.1 p.2 c = s.val.val c := by
    have hh := e.map_of_ne c hcA (by rw [hP]; exact hcP)
    rw [seamComplementPartner_firstBlock_apply s.val c hcn] at hh
    exact hh.symm
  by_cases hac : e.left.val < c.val
  · apply (isEmpty_iff_forall_notMem_cIoo e).mp he c
    · rw [Grid.mem_cIoo, hP, if_pos (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hac, by omega⟩
    · rw [hvSource, hcv, heB, heT, Grid.mem_cIoo, if_pos (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hbn, hhigh⟩
  · have hca : c.val < e.left.val := by
      have hh : c.val ≠ e.left.val := fun h => hcA (Fin.ext h)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo f).mp hf c
    · rw [Grid.mem_cIoo, hQ, ← hA, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hca⟩
    · rw [hcv, bottom_def, top_def, hQ, ← hA, Grid.mem_cIoo, if_pos (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hbn, hhigh⟩

/-- In the entry-right/exit-left orientation, the lower southwest row is zero. -/
theorem seamImmediateSecond_first_row_eq_zero (hre : e.right.val < n)
    (hlf : f.left.val < n) :
    s.val.val (seamComplementFirst s.val) = seamLeft n m 0 := by
  obtain ⟨hA, hQ, hP⟩ := seamImmediateSecond_top_sides p q s e f he hf hre hlf
  obtain ⟨heT, heB, hhigh⟩ := seamImmediateSecond_top_entry_rows p s e he hre
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem s.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem s.val)
  have hrows := s.property
  change (s.val.val (seamComplementFirst s.val)).val <
    (s.val.val (seamComplementSecond s.val)).val at hrows
  apply Fin.ext
  change (s.val.val (seamComplementFirst s.val)).val = 0
  by_contra hn
  have hap : 0 < (s.val.val (seamComplementFirst s.val)).val := by omega
  let c := s.val.val.toPerm.symm (seamLeft n m 0)
  have hcv : s.val.val c = seamLeft n m 0 := s.val.val.toPerm.apply_symm_apply _
  have hcP : c ≠ seamComplementFirst s.val := by
    intro hh
    have hv := congrArg Fin.val hcv
    rw [hh] at hv
    change (s.val.val (seamComplementFirst s.val)).val = 0 at hv
    omega
  have hcQ : c ≠ seamComplementSecond s.val := by
    intro hh
    have hv := congrArg Fin.val hcv
    rw [hh] at hv
    change (s.val.val (seamComplementSecond s.val)).val = 0 at hv
    omega
  have hcn : c.val < n := by
    by_contra hh
    have hcSW : c ∈ seamSouthwestColumns s.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨by omega, by rw [hcv]; exact Nat.zero_le n⟩
    rw [seamComplement_southwest_eq_pair_of_card_two s.val
      (seamMatchingEntry_southwest_card p s e)] at hcSW
    simp only [Finset.mem_insert, Finset.mem_singleton, hcP, hcQ, or_self] at hcSW
  have hcA : c ≠ e.right := by
    intro hh
    have hv := congrArg Fin.val hcv
    rw [hh] at hv
    change (s.val.val e.right).val = 0 at hv
    omega
  have hvSource : seamState p.1 p.2 c = s.val.val c := by
    have hh := e.map_of_ne c (by rw [hQ]; exact hcQ) hcA
    rw [seamComplementPartner_firstBlock_apply s.val c hcn] at hh
    exact hh.symm
  by_cases hca : c.val < e.right.val
  · apply (isEmpty_iff_forall_notMem_cIoo e).mp he c
    · rw [Grid.mem_cIoo, hQ, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hca⟩
    · rw [hvSource, hcv, heB, heT, Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hap⟩
  · have hac : e.right.val < c.val := by
      have hh : c.val ≠ e.right.val := fun h => hcA (Fin.ext h)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo f).mp hf c
    · rw [Grid.mem_cIoo, hP, ← hA, if_pos (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, hac, by omega⟩
    · rw [hcv, bottom_def, top_def, hP, ← hA, Grid.mem_cIoo, if_neg (by omega)]
      exact ⟨by intro hh; have := congrArg Fin.val hh; omega, Or.inr hap⟩

/-- The upper mixed orientation recovers the preimage of the last first-factor row. -/
theorem seamImmediateSecond_bottom_pivot (hle : e.left.val < n) (hrf : f.right.val < n) :
    e.left = seamLeft n m (p.1.toPerm.symm (Fin.last n)) := by
  apply seamImmediateSecond_pivot_of_value p.1 p.2 e.left hle (Fin.last n)
  change e.bottom = _
  rw [(seamImmediateSecond_bottom_entry_rows p s e he hle).1,
    seamImmediateSecond_second_row_eq_last p q s e f he hf hle hrf]

/-- The lower mixed orientation recovers the preimage of the zero first-factor row. -/
theorem seamImmediateSecond_top_pivot (hre : e.right.val < n) (hlf : f.left.val < n) :
    e.right = seamLeft n m (p.1.toPerm.symm 0) := by
  apply seamImmediateSecond_pivot_of_value p.1 p.2 e.right hre 0
  change e.top = _
  rw [(seamImmediateSecond_top_entry_rows p s e he hre).1,
    seamImmediateSecond_first_row_eq_zero p q s e f he hf hre hlf]

theorem seamImmediateSecond_bottom_source_second (hle : e.left.val < n)
    (hrf : f.right.val < n) :
    seamState p.1 p.2 (seamComplementSecond s.val) = s.val.val (seamComplementFirst s.val) := by
  obtain ⟨hA, hP, hQ⟩ := seamImmediateSecond_bottom_sides p q s e f he hf hle hrf
  have hn := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem s.val)).1
  have hne : seamComplementSecond s.val ≠ e.left := by
    intro hh; have := congrArg Fin.val hh; omega
  have hh := e.map_of_ne (seamComplementSecond s.val) hne
    (by rw [hP]; exact (seamComplementFirst_ne_second s.val).symm)
  rw [seamComplementPartner_apply_second] at hh
  exact hh.symm

theorem seamImmediateSecond_top_source_first (hre : e.right.val < n)
    (hlf : f.left.val < n) :
    seamState p.1 p.2 (seamComplementFirst s.val) = s.val.val (seamComplementSecond s.val) := by
  obtain ⟨hA, hQ, hP⟩ := seamImmediateSecond_top_sides p q s e f he hf hre hlf
  have hn := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem s.val)).1
  have hne : seamComplementFirst s.val ≠ e.right := by
    intro hh; have := congrArg Fin.val hh; omega
  have hh := e.map_of_ne (seamComplementFirst s.val)
    (by rw [hQ]; exact seamComplementFirst_ne_second s.val) hne
  rw [seamComplementPartner_apply_first] at hh
  exact hh.symm

theorem seamImmediateSecond_bottom_recovery
    (hmix : (e.left.val < n ∧ f.right.val < n) ∨ (e.right.val < n ∧ f.left.val < n)) :
    seamSecondFactorRow p.1
      (seamImmediateMixedSecondRectangle p q s e f he hf hmix).bottom =
      seamState p.1 p.2 (seamComplementSecond s.val) := by
  rw [seamImmediateMixedSecondRectangle, seamRetainedSecondRectangle_bottom_recovery]
  simp only [seamImmediateMixedFullRectangle, ofSwapColumns_bottom]

theorem seamImmediateSecond_top_recovery
    (hmix : (e.left.val < n ∧ f.right.val < n) ∨ (e.right.val < n ∧ f.left.val < n)) :
    seamSecondFactorRow p.1
      (seamImmediateMixedSecondRectangle p q s e f he hf hmix).top =
      seamState p.1 p.2 (seamComplementFirst s.val) := by
  rw [seamImmediateMixedSecondRectangle, seamRetainedSecondRectangle_top_recovery]
  simp only [seamImmediateMixedFullRectangle, ofSwapColumns_top]

/-- The entry-left/exit-right projection has zero bottom row. -/
theorem seamImmediateSecond_bottom_zero (hle : e.left.val < n) (hrf : f.right.val < n) :
    (seamImmediateMixedSecondRectangle p q s e f he hf (Or.inl ⟨hle, hrf⟩)).bottom = 0 := by
  apply seamSecondFactorRow_eq_zero_of_le p.1
  rw [seamImmediateSecond_bottom_recovery,
    seamImmediateSecond_bottom_source_second p q s e f he hf hle hrf]
  exact ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem s.val)).2

/-- The entry-right/exit-left projection has zero top row. -/
theorem seamImmediateSecond_top_zero (hre : e.right.val < n) (hlf : f.left.val < n) :
    (seamImmediateMixedSecondRectangle p q s e f he hf (Or.inr ⟨hre, hlf⟩)).top = 0 := by
  apply seamSecondFactorRow_eq_zero_of_le p.1
  rw [seamImmediateSecond_top_recovery,
    seamImmediateSecond_top_source_first p q s e f he hf hre hlf]
  exact ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem s.val)).2

/-- The upper mixed projection is absent from the direct second-factor lift. -/
theorem seamImmediateSecond_bottom_lift_not_isEmpty (hle : e.left.val < n)
    (hrf : f.right.val < n) :
    ¬ (seamSecondFactorRectangle p.1
      (seamImmediateMixedSecondRectangle p q s e f he hf (Or.inl ⟨hle, hrf⟩))).IsEmpty := by
  let r := seamImmediateMixedSecondRectangle p q s e f he hf (Or.inl ⟨hle, hrf⟩)
  have hr := seamImmediateMixedSecondRectangle_isEmpty p q s e f he hf (Or.inl ⟨hle, hrf⟩)
  have hc := seamImmediateMixedSecondRectangle_wraps p q s e f he hf (Or.inl ⟨hle, hrf⟩)
  have hz := seamImmediateSecond_bottom_zero p q s e f he hf hle hrf
  apply (seamSecondFactorRectangle_blocked_bottom_zero_iff p.1 r hr hc hz).mpr
  have hrec := seamImmediateSecond_bottom_recovery p q s e f he hf (Or.inl ⟨hle, hrf⟩)
  rw [hz, seamSecondFactorRow_zero,
    seamImmediateSecond_bottom_source_second p q s e f he hf hle hrf] at hrec
  have hrow := s.property
  change (s.val.val (seamComplementFirst s.val)).val <
    (s.val.val (seamComplementSecond s.val)).val at hrow
  rw [seamImmediateSecond_second_row_eq_last p q s e f he hf hle hrf, ← hrec] at hrow
  exact hrow

/-- The lower mixed projection is absent from the direct second-factor lift. -/
theorem seamImmediateSecond_top_lift_not_isEmpty (hre : e.right.val < n)
    (hlf : f.left.val < n) :
    ¬ (seamSecondFactorRectangle p.1
      (seamImmediateMixedSecondRectangle p q s e f he hf (Or.inr ⟨hre, hlf⟩))).IsEmpty := by
  let r := seamImmediateMixedSecondRectangle p q s e f he hf (Or.inr ⟨hre, hlf⟩)
  have hr := seamImmediateMixedSecondRectangle_isEmpty p q s e f he hf (Or.inr ⟨hre, hlf⟩)
  have hc := seamImmediateMixedSecondRectangle_wraps p q s e f he hf (Or.inr ⟨hre, hlf⟩)
  have hz := seamImmediateSecond_top_zero p q s e f he hf hre hlf
  apply (seamSecondFactorRectangle_blocked_top_zero_iff p.1 r hr hc hz).mpr
  have hrec := seamImmediateSecond_top_recovery p q s e f he hf (Or.inr ⟨hre, hlf⟩)
  rw [hz, seamSecondFactorRow_zero,
    seamImmediateSecond_top_source_first p q s e f he hf hre hlf] at hrec
  have hrow := s.property
  change (s.val.val (seamComplementFirst s.val)).val <
    (s.val.val (seamComplementSecond s.val)).val at hrow
  rw [seamImmediateSecond_first_row_eq_zero p q s e f he hf hre hlf, ← hrec] at hrow
  exact hrow

end Mixed
end OnLeConjecture.KnotFloer.GridFull

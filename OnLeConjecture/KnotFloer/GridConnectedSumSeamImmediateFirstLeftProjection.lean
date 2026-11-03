/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamImmediateFirstProjection

/-!
# The other first-factor immediate correction

Entries and exits through the same second southwest column give the
first-factor rectangles whose left endpoint is its last column.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

theorem seamImmediate_right_ne_first (x : SeamMatchingSource n m)
    (a : Fin (n + m + 1)) (ha : a.val < n) : a ≠ seamComplementFirst x.val := by
  have hh := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  intro h
  have := congrArg Fin.val h
  omega

theorem seamImmediate_right_column_eq (p q : SeamRetainedIndex n m)
    (x : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (f : GridRectangleBetween x.val.val (seamState q.1 q.2))
    (he : e.right.val < n) (hf : f.right.val < n) : e.right = f.right := by
  have heL : ¬ e.left.val < n := by
    have hh := seamEnteringRectangle_ranges (seamState_mem_pairSector p.1 p.2)
      (seamComplementPartner x.val).property e
    rcases hh with h | h <;> omega
  have hfL : ¬ f.left.val < n := by
    have hh := seamLeavingRectangle_ranges (seamState_mem_pairSector q.1 q.2) x.val.property f
    rcases hh with h | h <;> omega
  have hh := (seamMatchingEntry_northeast_eq_singleton p x e).symm.trans
    (seamMatchingExit_northeast_eq_singleton q x f)
  simpa only [if_neg heL, if_neg hfL, Finset.singleton_inj] using hh

section FirstLeft
variable (p q : SeamRetainedIndex n m) (x : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (f : GridRectangleBetween x.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hf : f.IsEmpty) (hre : e.right.val < n) (hrf : f.right.val < n)
include he hf hre hrf

theorem seamImmediateFirstLeft_sides :
    e.left = seamComplementSecond x.val ∧ f.left = seamComplementSecond x.val := by
  exact ⟨seamMatchingEntry_left_eq_second_of_right_lt p x e he hre,
    seamMatchingExit_left_eq_second_of_right_lt q x f hf hrf⟩

theorem seamImmediateFirstLeft_source_first :
    seamState p.1 p.2 e.right = x.val.val (seamComplementFirst x.val) := by
  have hs := (seamImmediateFirstLeft_sides p q x e f he hf hre hrf).1
  have hh := e.map_left
  rw [hs, seamComplementPartner_apply_second] at hh
  exact hh.symm

theorem seamImmediateFirstLeft_source_second :
    seamState p.1 p.2 (seamComplementFirst x.val) = x.val.val (seamComplementSecond x.val) := by
  have hs := (seamImmediateFirstLeft_sides p q x e f he hf hre hrf).1
  have hh := e.map_of_ne (seamComplementFirst x.val)
    (by rw [hs]; exact seamComplementFirst_ne_second x.val)
    (Ne.symm (seamImmediate_right_ne_first x e.right hre))
  rw [seamComplementPartner_apply_first] at hh
  exact hh.symm

theorem seamImmediateFirstLeft_target_first :
    seamState q.1 q.2 e.right = x.val.val (seamComplementSecond x.val) := by
  have hs := (seamImmediateFirstLeft_sides p q x e f he hf hre hrf).2
  rw [seamImmediate_right_column_eq p q x e f hre hrf, f.map_right, hs]

theorem seamImmediateFirstLeft_target_second :
    seamState q.1 q.2 (seamComplementFirst x.val) = x.val.val (seamComplementFirst x.val) := by
  have hs := (seamImmediateFirstLeft_sides p q x e f he hf hre hrf).2
  exact f.map_of_ne _ (by rw [hs]; exact seamComplementFirst_ne_second x.val)
    (by rw [← seamImmediate_right_column_eq p q x e f hre hrf]
        exact (seamImmediate_right_ne_first x e.right hre).symm)

theorem seamImmediateFirstLeft_source_pivot :
    seamState p.1 p.2 (seamComplementSecond x.val) = x.val.val e.right := by
  have hs := (seamImmediateFirstLeft_sides p q x e f he hf hre hrf).1
  have hh := e.map_right
  rw [hs, seamComplementPartner_firstBlock_apply x.val e.right hre] at hh
  exact hh.symm

theorem seamImmediateFirstLeft_strip_empty (c : Fin (n + m + 1))
    (hc : c ∈ Grid.cIoo e.left e.right) :
    seamState p.1 p.2 c ∉ Grid.cIoo
      (x.val.val (seamComplementSecond x.val)) (x.val.val (seamComplementFirst x.val)) := by
  obtain ⟨hqE, hqF⟩ := seamImmediateFirstLeft_sides p q x e f he hf hre hrf
  have hA := seamImmediate_right_column_eq p q x e f hre hrf
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hPQ := seamComplementFirst_lt_second x.val
  have hab : ¬ e.left.val < e.right.val := by rw [hqE]; omega
  have hcs := (Grid.mem_cIoo _ _ _).mp hc
  rw [if_neg hab, hqE] at hcs
  have hca : c ≠ e.right := by intro hh; have := congrArg Fin.val hh; omega
  have hcp : c ≠ seamComplementFirst x.val := by
    intro hh
    have := congrArg Fin.val hh
    omega
  have hcq : c ≠ seamComplementSecond x.val := by
    intro hh
    have := congrArg Fin.val hh
    omega
  have hx := e.map_of_ne c (by simpa only [hqE] using hcq) hca
  change x.val.val.swapColumns (seamComplementFirst x.val)
    (seamComplementSecond x.val) c = _ at hx
  rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcp hcq] at hx
  have hNE : n < (x.val.val e.right).val := by
    have hh : e.right ∈ seamNortheastColumns x.val.val := by
      rw [seamMatchingEntry_northeast_eq_singleton p x e, if_neg (by rw [hqE]; omega)]
      exact Finset.mem_singleton_self _
    exact ((mem_seamNortheastColumns _ _).mp hh).2
  have hcut : x.val.val e.right ∈ Grid.cIoo
      (x.val.val (seamComplementSecond x.val)) (x.val.val (seamComplementFirst x.val)) := by
    rw [Grid.mem_cIoo, if_neg (not_lt_of_ge x.property.le)]
    exact ⟨fun hh => seamComplementFirst_ne_second x.val (x.val.val.toPerm.injective hh).symm,
      Or.inl (hQ.2.trans_lt hNE)⟩
  intro hr
  rw [← Grid.cIoo_union_insert_cIoo_eq_cIoo_of_mem_cIoo hcut] at hr
  rcases Finset.mem_union.mp hr with hr | hr
  · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf c (by
      simpa only [hqF, ← hqE, ← hA] using hc)
    rw [bottom_def, top_def, hqF, ← hA, hx]
    exact hr
  · rcases Finset.mem_insert.mp hr with hr | hr
    · exact hca (x.val.val.toPerm.injective (hx.trans hr))
    · apply (isEmpty_iff_forall_notMem_cIoo e).mp he c hc
      simpa only [bottom_def, top_def, hqE,
        seamImmediateFirstLeft_source_first p q x e f he hf hre hrf,
        seamImmediateFirstLeft_source_pivot p q x e f he hf hre hrf] using hr

def seamImmediateFirstLeftFullRectangle :
    GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2) where
  left := seamComplementFirst x.val
  right := e.right
  left_ne_right := (seamImmediate_right_ne_first x e.right hre).symm
  map_left := by
    rw [seamImmediateFirstLeft_target_second p q x e f he hf hre hrf,
      seamImmediateFirstLeft_source_first p q x e f he hf hre hrf]
  map_right := by
    rw [seamImmediateFirstLeft_target_first p q x e f he hf hre hrf,
      seamImmediateFirstLeft_source_second p q x e f he hf hre hrf]
  map_of_ne c hp hc := by
    obtain ⟨hqE, hqF⟩ := seamImmediateFirstLeft_sides p q x e f he hf hre hrf
    have hA := seamImmediate_right_column_eq p q x e f hre hrf
    by_cases hq : c = seamComplementSecond x.val
    · subst c
      have hh₁ := e.map_right
      rw [hqE, seamComplementPartner_firstBlock_apply x.val e.right hre] at hh₁
      have hh₂ := f.map_left
      rw [hqF, ← hA] at hh₂
      exact hh₂.trans hh₁
    · have hh₁ := e.map_of_ne c (by simpa only [hqE] using hq) hc
      have hh₂ := f.map_of_ne c (by simpa only [hqF] using hq)
        (by simpa only [← hA] using hc)
      change x.val.val.swapColumns (seamComplementFirst x.val)
        (seamComplementSecond x.val) c = _ at hh₁
      rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hp hq] at hh₁
      exact hh₂.trans hh₁

theorem seamImmediateFirstLeft_second_factor_eq : p.2 = q.2 :=
  seamRetainedRectangle_second_eq_of_side_lt p q
    (seamImmediateFirstLeftFullRectangle p q x e f he hf hre hrf) (Or.inr hre)

def seamImmediateFirstLeftRectangle : GridRectangleBetween p.1 q.1 :=
  seamRetainedFirstRectangle p q
    (seamImmediateFirstLeftFullRectangle p q x e f he hf hre hrf) (Or.inr hre)

@[simp] theorem seamImmediateFirstLeftRectangle_left :
    (seamImmediateFirstLeftRectangle p q x e f he hf hre hrf).left = Fin.last n := by
  have hn := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
  change seamFirstFactorIndex (seamComplementFirst x.val) = _
  simp only [seamFirstFactorIndex, dif_neg (not_lt_of_ge hn)]

@[simp] theorem seamImmediateFirstLeftRectangle_right :
    (seamImmediateFirstLeftRectangle p q x e f he hf hre hrf).right =
      seamFirstFactorIndex e.right := rfl

theorem seamImmediateFirstLeftRectangle_isEmpty :
    (seamImmediateFirstLeftRectangle p q x e f he hf hre hrf).IsEmpty := by
  let R := seamImmediateFirstLeftFullRectangle p q x e f he hf hre hrf
  let r := seamImmediateFirstLeftRectangle p q x e f he hf hre hrf
  apply (isEmpty_iff_forall_notMem_cIoo r).mpr
  intro c hc hr
  have hindex : (seamFirstFactorIndex e.right).val = e.right.val := by
    simp only [seamFirstFactorIndex, dif_pos hre]
  have hcols := (Grid.mem_cIoo _ _ _).mp hc
  have hleft : r.left = Fin.last n :=
    seamImmediateFirstLeftRectangle_left p q x e f he hf hre hrf
  have hright : r.right.val = e.right.val := by
    change (seamFirstFactorIndex e.right).val = _
    exact hindex
  rw [if_neg (by rw [hleft, hright]; simp only [Fin.val_last]; omega)] at hcols
  have hcr : c.val < e.right.val := by
    rcases hcols.2 with h | h
    · rw [hleft, Fin.val_last] at h
      exact False.elim (by omega)
    · rwa [hright] at h
  have hcn : c.val < n := hcr.trans hre
  let d : Fin n := ⟨c.val, hcn⟩
  have hdc : d.castSucc = c := Fin.ext rfl
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hqE := (seamImmediateFirstLeft_sides p q x e f he hf hre hrf).1
  have hdc_mem : seamLeft n m d.castSucc ∈ Grid.cIoo e.left e.right := by
    rw [Grid.mem_cIoo, if_neg (by rw [hqE]; omega)]
    exact ⟨e.left_ne_right, Or.inr hcr⟩
  apply seamImmediateFirstLeft_strip_empty p q x e f he hf hre hrf _ hdc_mem
  have hb := seamRetainedFirstRectangle_bottom_recovery p q R (Or.inr hre)
  have ht := seamRetainedFirstRectangle_top_recovery p q R (Or.inr hre)
  change seamLeft n m r.bottom = seamState p.1 p.2 (seamComplementFirst x.val) at hb
  change seamLeft n m r.top = seamState p.1 p.2 e.right at ht
  rw [seamImmediateFirstLeft_source_second p q x e f he hf hre hrf] at hb
  rw [seamImmediateFirstLeft_source_first p q x e f he hf hre hrf] at ht
  rw [seamState_left_castSucc, hdc, ← hb, ← ht, seamLeft_mem_cIoo_iff]
  exact hr

theorem seamImmediateFirstLeftFullRectangle_not_isEmpty :
    ¬ (seamImmediateFirstLeftFullRectangle p q x e f he hf hre hrf).IsEmpty := by
  let R := seamImmediateFirstLeftFullRectangle p q x e f he hf hre hrf
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hPQ := seamComplementFirst_lt_second x.val
  have hhigh : n < (x.val.val e.right).val := by
    have hh : e.right ∈ seamNortheastColumns x.val.val := by
      rw [seamMatchingEntry_northeast_eq_singleton p x e,
        if_neg (by rw [(seamImmediateFirstLeft_sides p q x e f he hf hre hrf).1]; omega)]
      exact Finset.mem_singleton_self _
    exact ((mem_seamNortheastColumns _ _).mp hh).2
  intro heR
  apply (isEmpty_iff_forall_notMem_cIoo R).mp heR (seamComplementSecond x.val)
  · change seamComplementSecond x.val ∈ Grid.cIoo (seamComplementFirst x.val) e.right
    rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨(seamImmediate_right_ne_first x e.right hre).symm, Or.inl hPQ⟩
  · change seamState p.1 p.2 (seamComplementSecond x.val) ∈
      Grid.cIoo (seamState p.1 p.2 (seamComplementFirst x.val)) (seamState p.1 p.2 e.right)
    rw [seamImmediateFirstLeft_source_pivot p q x e f he hf hre hrf,
      seamImmediateFirstLeft_source_second p q x e f he hf hre hrf,
      seamImmediateFirstLeft_source_first p q x e f he hf hre hrf,
      Grid.mem_cIoo, if_neg (not_lt_of_ge x.property.le)]
    exact ⟨fun hh => seamComplementFirst_ne_second x.val (x.val.val.toPerm.injective hh).symm,
      Or.inl (hQ.2.trans_lt hhigh)⟩

theorem seamImmediateFirstLeftRectangle_lift_not_isEmpty :
    ¬ (seamFirstFactorRectangle
      (seamImmediateFirstLeftRectangle p q x e f he hf hre hrf) p.2).IsEmpty := by
  have hz := seamImmediateFirstLeft_second_factor_eq p q x e f he hf hre hrf
  rcases q with ⟨q₁, q₂⟩
  change p.2 = q₂ at hz
  subst q₂
  change ¬ (seamFirstFactorRectangle
    (seamRetainedFirstRectangle p (q₁, p.2)
      (seamImmediateFirstLeftFullRectangle p (q₁, p.2) x e f he hf hre hrf)
        (Or.inr hre)) p.2).IsEmpty
  rw [seamFirstFactorRectangle_lift_project]
  exact seamImmediateFirstLeftFullRectangle_not_isEmpty p (q₁, p.2) x e f he hf hre hrf

/-- A simultaneous entry and exit of this orientation forces the other pivot to the end. -/
theorem seamImmediateFirstLeft_pivot_eq_last :
    (seamComplementSecond x.val).val = n + m := by
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hPQ := seamComplementFirst_lt_second x.val
  have hqE := (seamImmediateFirstLeft_sides p q x e f he hf hre hrf).1
  by_contra hn
  have hnQ : (seamComplementSecond x.val).val < n + m := by
    have := (seamComplementSecond x.val).isLt
    omega
  let c := Fin.last (n + m)
  have hcv : c.val = n + m := rfl
  have hc : c ∈ Grid.cIoo e.left e.right := by
    rw [Grid.mem_cIoo, if_neg (by rw [hqE]; omega)]
    exact ⟨e.left_ne_right, Or.inl (by rw [hqE]; omega)⟩
  have hca : c ≠ e.right := by intro hh; have := congrArg Fin.val hh; omega
  have hcp : c ≠ seamComplementFirst x.val := by
    intro hh
    have := congrArg Fin.val hh
    omega
  have hcq : c ≠ seamComplementSecond x.val := by
    intro hh
    have := congrArg Fin.val hh
    omega
  have hhigh : n < (x.val.val c).val := by
    by_contra h
    have hcSW : c ∈ seamSouthwestColumns x.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨by omega, by omega⟩
    rw [seamComplement_southwest_eq_pair_of_card_two x.val
      (seamMatchingEntry_southwest_card p x e)] at hcSW
    rcases Finset.mem_insert.mp hcSW with hh | hh
    · exact hcp hh
    · exact hcq (Finset.mem_singleton.mp hh)
  have hx := e.map_of_ne c (by simpa only [hqE] using hcq) hca
  change x.val.val.swapColumns (seamComplementFirst x.val)
    (seamComplementSecond x.val) c = _ at hx
  rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcp hcq] at hx
  apply seamImmediateFirstLeft_strip_empty p q x e f he hf hre hrf c hc
  rw [← hx, Grid.mem_cIoo, if_neg (not_lt_of_ge x.property.le)]
  exact ⟨fun hh => seamComplementFirst_ne_second x.val (x.val.val.toPerm.injective hh).symm,
    Or.inl (hQ.2.trans_lt hhigh)⟩

end FirstLeft
end OnLeConjecture.KnotFloer.GridFull

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamUnweightedPaths
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamRetainedSecondProjection

/-! # Second-factor rectangles from mixed immediate seam corrections

The two mixed entry/exit alternatives exchange the two southwest columns
of the retained states. The factor rectangle wraps from the second column
to the first. Its emptiness is checked in the second factor, since the
corresponding full rectangle can contain the first-block northeast column.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

private theorem immediate_firstBlock_ne_sw (x : SeamMatchingSource n m)
    (a : Fin (n + m + 1)) (ha : a.val < n) :
    a ≠ seamComplementFirst x.val ∧ a ≠ seamComplementSecond x.val := by
  have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  constructor <;> intro h <;> have := congrArg Fin.val h <;> omega

section Mixed
variable (p q : SeamRetainedIndex n m) (x : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (f : GridRectangleBetween x.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hf : f.IsEmpty)
    (hmix : (e.left.val < n ∧ f.right.val < n) ∨
      (e.right.val < n ∧ f.left.val < n))
include he hf hmix

/-- The shared first-block endpoint and the two southwest endpoints in the mixed cases. -/
theorem seamImmediateMixed_sides :
    (e.left.val < n ∧ e.left = f.right ∧
      e.right = seamComplementFirst x.val ∧ f.left = seamComplementSecond x.val) ∨
    (e.right.val < n ∧ e.right = f.left ∧
      e.left = seamComplementSecond x.val ∧ f.right = seamComplementFirst x.val) := by
  have hh := (seamMatchingEntry_northeast_eq_singleton p x e).symm.trans
    (seamMatchingExit_northeast_eq_singleton q x f)
  rcases hmix with ⟨hle, hrf⟩ | ⟨hre, hlf⟩
  · have hq := seamMatchingExit_left_eq_second_of_right_lt q x f hf hrf
    have hn := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
    have hnf : ¬ f.left.val < n := by rw [hq]; omega
    simp only [if_pos hle, if_neg hnf, Finset.singleton_inj] at hh
    exact Or.inl ⟨hle, hh, seamMatchingEntry_right_eq_first_of_left_lt p x e he hle, hq⟩
  · have hq := seamMatchingEntry_left_eq_second_of_right_lt p x e he hre
    have hn := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
    have hne : ¬ e.left.val < n := by rw [hq]; omega
    simp only [if_neg hne, if_pos hlf, Finset.singleton_inj] at hh
    exact Or.inr ⟨hre, hh, hq, seamMatchingExit_right_eq_first_of_left_lt q x f hf hlf⟩

/-- Composing entry, inverse matching and exit exchanges the retained southwest columns. -/
theorem seamImmediateMixed_target_eq_swap :
    seamState q.1 q.2 = (seamState p.1 p.2).swapColumns
      (seamComplementSecond x.val) (seamComplementFirst x.val) := by
  have hpq := seamComplementFirst_ne_second x.val
  have hqp := hpq.symm
  have hs := seamMatchingEntry_source_eq_swaps p x e
  have ht := seamMatchingExit_target_eq_swap q x f
  rcases seamImmediateMixed_sides p q x e f he hf hmix with
      ⟨ha, hA, hP, hQ⟩ | ⟨ha, hA, hQ, hP⟩
  · have hn := immediate_firstBlock_ne_sw x e.left ha
    have hnP := hn.1.symm
    have hnQ := hn.2.symm
    rw [hP] at hs
    rw [hQ, ← hA] at ht
    simp only [ht, hs]
    apply GridState.ext
    intro c
    by_cases hcA : c = e.left
    · subst c; simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
    by_cases hcP : c = seamComplementFirst x.val
    · subst c; simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
    by_cases hcQ : c = seamComplementSecond x.val
    · subst c; simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
    simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
  · have hn := immediate_firstBlock_ne_sw x e.right ha
    have hnP := hn.1.symm
    have hnQ := hn.2.symm
    rw [hQ] at hs
    rw [hP, ← hA] at ht
    simp only [ht, hs]
    apply GridState.ext
    intro c
    by_cases hcA : c = e.right
    · subst c; simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
    by_cases hcP : c = seamComplementFirst x.val
    · subst c; simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
    by_cases hcQ : c = seamComplementSecond x.val
    · subst c; simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
    simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]

/-- The retained rectangle determined by a mixed immediate correction. -/
def seamImmediateMixedFullRectangle :
    GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2) :=
  ofSwapColumns _ _ (seamComplementSecond x.val) (seamComplementFirst x.val)
    (seamComplementFirst_ne_second x.val).symm
    (seamImmediateMixed_target_eq_swap p q x e f he hf hmix)

/-- The first factor is unchanged in either mixed case. -/
theorem seamImmediateMixed_first_factor_eq : p.1 = q.1 :=
  seamRetainedRectangle_first_eq_of_sides_ge p q
    (seamImmediateMixedFullRectangle p q x e f he hf hmix)
    (by simpa [seamImmediateMixedFullRectangle] using
      ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1)
    (by simpa [seamImmediateMixedFullRectangle] using
      ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1)

/-- The second-factor rectangle, with second-to-first southwest column orientation. -/
def seamImmediateMixedSecondRectangle : GridRectangleBetween p.2 q.2 :=
  seamRetainedSecondRectangle p q
    (seamImmediateMixedFullRectangle p q x e f he hf hmix)
    (by simpa [seamImmediateMixedFullRectangle] using
      ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1)
    (by simpa [seamImmediateMixedFullRectangle] using
      ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1)

omit he hf hmix in
include e in
/-- Away from its two southwest columns, a second-block point has a high row. -/
private theorem seamImmediateMixed_high_row (c : Fin (n + m + 1))
    (hc : n ≤ c.val) (hP : c ≠ seamComplementFirst x.val)
    (hQ : c ≠ seamComplementSecond x.val) : n < (x.val.val c).val := by
  by_contra h
  have hh := (mem_seamSouthwestColumns x.val.val c).mpr ⟨hc, by omega⟩
  rw [seamComplement_southwest_eq_pair_of_card_two x.val
    (seamMatchingEntry_southwest_card p x e)] at hh
  simp only [Finset.mem_insert, Finset.mem_singleton, hP, hQ, or_self] at hh

/-- The retained rectangle is empty when tested only on second-block columns. -/
theorem seamImmediateMixedFullRectangle_secondBlock_empty
    (c : Fin (n + m + 1)) (hcn : n ≤ c.val)
    (hc : c ∈ Grid.cIoo (seamComplementSecond x.val) (seamComplementFirst x.val)) :
    seamState p.1 p.2 c ∉ Grid.cIoo
      (seamState p.1 p.2 (seamComplementSecond x.val))
      (seamState p.1 p.2 (seamComplementFirst x.val)) := by
  have hpq := seamComplementFirst_lt_second x.val
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hcols : (seamComplementSecond x.val).val < c.val ∨
      c.val < (seamComplementFirst x.val).val := by
    have hh := (Grid.mem_cIoo _ _ _).mp hc
    simpa only [if_neg (by omega : ¬
      (seamComplementSecond x.val).val < (seamComplementFirst x.val).val)] using hh.2
  have hcP : c ≠ seamComplementFirst x.val := by
    intro h; have := congrArg Fin.val h; omega
  have hcQ : c ≠ seamComplementSecond x.val := by
    intro h; have := congrArg Fin.val h; omega
  have hhigh := seamImmediateMixed_high_row p x e c hcn hcP hcQ
  have hsw : (seamComplementPartner x.val).val c = x.val.val c := by
    change x.val.val.swapColumns _ _ c = _
    simp only [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcP hcQ]
  rcases seamImmediateMixed_sides p q x e f he hf hmix with
      ⟨ha, hA, hP, hQ⟩ | ⟨ha, hA, hQ, hP⟩
  · have hne := immediate_firstBlock_ne_sw x e.left ha
    have hcA : c ≠ e.left := by intro h; have := congrArg Fin.val h; omega
    have hvc : seamState p.1 p.2 c = x.val.val c := by
      exact (e.map_of_ne c hcA (by simpa only [hP] using hcP)).symm.trans hsw
    have hvP : seamState p.1 p.2 (seamComplementFirst x.val) = x.val.val e.left := by
      have hh := e.map_left
      rw [hP, seamComplementPartner_firstBlock_apply x.val e.left ha] at hh
      exact hh.symm
    have hvQ : seamState p.1 p.2 (seamComplementSecond x.val) =
        x.val.val (seamComplementFirst x.val) := by
      have hh := e.map_of_ne (seamComplementSecond x.val) hne.2.symm
        (by rw [hP]; exact (seamComplementFirst_ne_second x.val).symm)
      rw [seamComplementPartner_apply_second] at hh
      exact hh.symm
    have heBot : e.bottom = x.val.val (seamComplementSecond x.val) := by
      have hh := e.map_right
      rw [hP, seamComplementPartner_apply_first] at hh
      exact hh.symm
    have heTop : e.top = x.val.val e.left := by simpa only [top_def, hP] using hvP
    have hfBot : f.bottom = x.val.val (seamComplementSecond x.val) := by rw [bottom_def, hQ]
    have hfTop : f.top = x.val.val e.left := by rw [top_def, ← hA]
    have hnA : n < (x.val.val e.left).val := by
      have hh := seamMatchingEntry_northeast_eq_singleton p x e
      rw [if_pos ha] at hh
      have hh' : e.left ∈ seamNortheastColumns x.val.val := by rw [hh]; simp
      exact ((mem_seamNortheastColumns _ _).mp hh').2
    intro hr
    rw [hvc, hvQ, hvP, Grid.mem_cIoo, if_pos (by omega)] at hr
    rcases hcols with hright | hleft
    · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf c
      · rw [Grid.mem_cIoo, hQ, ← hA, if_neg (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hright⟩
      · rw [Grid.mem_cIoo, hfBot, hfTop, if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hr.2.2⟩
    · apply (isEmpty_iff_forall_notMem_cIoo e).mp he c
      · rw [Grid.mem_cIoo, hP, if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hleft⟩
      · rw [hvc, Grid.mem_cIoo, heBot, heTop, if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hr.2.2⟩
  · have hne := immediate_firstBlock_ne_sw x e.right ha
    have hcA : c ≠ e.right := by intro h; have := congrArg Fin.val h; omega
    have hvc : seamState p.1 p.2 c = x.val.val c := by
      exact (e.map_of_ne c (by simpa only [hQ] using hcQ) hcA).symm.trans hsw
    have hvQ : seamState p.1 p.2 (seamComplementSecond x.val) = x.val.val e.right := by
      have hh := e.map_right
      rw [hQ, seamComplementPartner_firstBlock_apply x.val e.right ha] at hh
      exact hh.symm
    have hvP : seamState p.1 p.2 (seamComplementFirst x.val) =
        x.val.val (seamComplementSecond x.val) := by
      have hh := e.map_of_ne (seamComplementFirst x.val)
        (by rw [hQ]; exact seamComplementFirst_ne_second x.val) hne.1.symm
      rw [seamComplementPartner_apply_first] at hh
      exact hh.symm
    have heBot : e.bottom = x.val.val e.right := by simpa only [bottom_def, hQ] using hvQ
    have heTop : e.top = x.val.val (seamComplementFirst x.val) := by
      have hh := e.map_left
      rw [hQ, seamComplementPartner_apply_second] at hh
      exact hh.symm
    have hfBot : f.bottom = x.val.val e.right := by rw [bottom_def, ← hA]
    have hfTop : f.top = x.val.val (seamComplementFirst x.val) := by rw [top_def, hP]
    have hnA : n < (x.val.val e.right).val := by
      have hh := seamMatchingEntry_northeast_eq_singleton p x e
      have hneg : ¬ e.left.val < n := by rw [hQ]; omega
      rw [if_neg hneg] at hh
      have hh' : e.right ∈ seamNortheastColumns x.val.val := by rw [hh]; simp
      exact ((mem_seamNortheastColumns _ _).mp hh').2
    intro hr
    rw [hvc, hvQ, hvP, Grid.mem_cIoo, if_neg (by omega)] at hr
    have hrow : (x.val.val e.right).val < (x.val.val c).val := by omega
    rcases hcols with hright | hleft
    · apply (isEmpty_iff_forall_notMem_cIoo e).mp he c
      · rw [Grid.mem_cIoo, hQ, if_neg (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hright⟩
      · rw [hvc, Grid.mem_cIoo, heBot, heTop, if_neg (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hrow⟩
    · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf c
      · rw [Grid.mem_cIoo, hP, ← hA, if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, by omega, hleft⟩
      · rw [Grid.mem_cIoo, hfBot, hfTop, if_neg (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hrow⟩

/-- Both actual empty rectangles imply emptiness of the projected second-factor rectangle. -/
theorem seamImmediateMixedSecondRectangle_isEmpty :
    (seamImmediateMixedSecondRectangle p q x e f he hf hmix).IsEmpty := by
  apply (isEmpty_iff_forall_notMem_cIoo _).mpr
  intro a ha hr
  let r := seamImmediateMixedFullRectangle p q x e f he hf hmix
  have hL : n ≤ r.left.val := by
    simpa [r, seamImmediateMixedFullRectangle] using
      ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  have hR : n ≤ r.right.val := by
    simpa [r, seamImmediateMixedFullRectangle] using
      ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)).1
  have hc : seamRight n m a ∈ Grid.cIoo r.left r.right := by
    rw [← seamRight_secondFactorIndex r.left hL, ← seamRight_secondFactorIndex r.right hR,
      seamRight_mem_cIoo_iff]
    exact ha
  have hv : seamState p.1 p.2 (seamRight n m a) ∈ Grid.cIoo r.bottom r.top := by
    rw [seamState_secondFactorRow,
      ← seamRetainedSecondRectangle_bottom_recovery p q r hL hR,
      ← seamRetainedSecondRectangle_top_recovery p q r hL hR,
      seamSecondFactorRow_mem_cIoo_iff]
    exact hr
  have hh := seamImmediateMixedFullRectangle_secondBlock_empty p q x e f he hf hmix
    (seamRight n m a) (by simp only [seamRight_val]; omega)
    (by simpa only [r, seamImmediateMixedFullRectangle, ofSwapColumns_left,
      ofSwapColumns_right] using hc)
  apply hh
  simpa only [r, seamImmediateMixedFullRectangle, ofSwapColumns_bottom,
    ofSwapColumns_top] using hv

/-- The factor sides recover exactly the second and first southwest columns. -/
@[simp] theorem seamImmediateMixedSecondRectangle_sides :
    seamRight n m (seamImmediateMixedSecondRectangle p q x e f he hf hmix).left =
      seamComplementSecond x.val ∧
    seamRight n m (seamImmediateMixedSecondRectangle p q x e f he hf hmix).right =
      seamComplementFirst x.val := by
  simp only [seamImmediateMixedSecondRectangle, seamRetainedSecondRectangle_left,
    seamRetainedSecondRectangle_right, seamRight_secondFactorIndex,
    seamImmediateMixedFullRectangle, ofSwapColumns_left, ofSwapColumns_right, and_self]

/-- Every projected mixed immediate rectangle wraps in the factor's column order. -/
theorem seamImmediateMixedSecondRectangle_wraps :
    (seamImmediateMixedSecondRectangle p q x e f he hf hmix).right.val <
      (seamImmediateMixedSecondRectangle p q x e f he hf hmix).left.val := by
  obtain ⟨hl, hr⟩ := seamImmediateMixedSecondRectangle_sides p q x e f he hf hmix
  have hh := seamComplementFirst_lt_second x.val
  have hlv := congrArg Fin.val hl
  have hrv := congrArg Fin.val hr
  simp only [seamRight_val] at hlv hrv
  omega

/-- An actual mixed immediate correction determines a second-factor rectangle path. -/
def seamImmediateMixedFactorPath : SeamFactorRectanglePath p q :=
  Sum.inr (⟨(), seamImmediateMixed_first_factor_eq p q x e f he hf hmix⟩,
    ⟨seamImmediateMixedSecondRectangle p q x e f he hf hmix,
      seamImmediateMixedSecondRectangle_isEmpty p q x e f he hf hmix⟩)

end Mixed
end OnLeConjecture.KnotFloer.GridFull

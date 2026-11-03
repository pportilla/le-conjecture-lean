/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamUnweightedPaths
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFactorLift

/-!
# First-factor rectangles from immediate seam corrections

The entry and exit through the same first southwest column determine a
first-factor rectangle. Its emptiness follows from the two actual empty
rectangles. Its direct lift is obstructed by the exchanged high point.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

theorem seamImmediate_left_ne_second (x : SeamMatchingSource n m)
    (a : Fin (n + m + 1)) (ha : a.val < n) : a ≠ seamComplementSecond x.val := by
  have hh := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  intro h
  have := congrArg Fin.val h
  omega

/-- The entry and exit read the same unique northeast column. -/
theorem seamImmediate_left_column_eq (p q : SeamRetainedIndex n m)
    (x : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (f : GridRectangleBetween x.val.val (seamState q.1 q.2))
    (he : e.left.val < n) (hf : f.left.val < n) : e.left = f.left := by
  have hh := (seamMatchingEntry_northeast_eq_singleton p x e).symm.trans
    (seamMatchingExit_northeast_eq_singleton q x f)
  simpa only [if_pos he, if_pos hf, Finset.singleton_inj] using hh

section FirstRight
variable (p q : SeamRetainedIndex n m) (x : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (f : GridRectangleBetween x.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hf : f.IsEmpty) (hle : e.left.val < n) (hlf : f.left.val < n)
include he hf hle hlf

theorem seamImmediateFirstRight_sides :
    e.right = seamComplementFirst x.val ∧ f.right = seamComplementFirst x.val := by
  exact ⟨seamMatchingEntry_right_eq_first_of_left_lt p x e he hle,
    seamMatchingExit_right_eq_first_of_left_lt q x f hf hlf⟩

theorem seamImmediateFirstRight_source_first :
    seamState p.1 p.2 e.left = x.val.val (seamComplementSecond x.val) := by
  have hs := (seamImmediateFirstRight_sides p q x e f he hf hle hlf).1
  have hh := e.map_right
  rw [hs, seamComplementPartner_apply_first] at hh
  exact hh.symm

theorem seamImmediateFirstRight_source_second :
    seamState p.1 p.2 (seamComplementSecond x.val) = x.val.val (seamComplementFirst x.val) := by
  have hs := (seamImmediateFirstRight_sides p q x e f he hf hle hlf).1
  have hh := e.map_of_ne (seamComplementSecond x.val)
    (Ne.symm (seamImmediate_left_ne_second x e.left hle))
    (by rw [hs]; exact (seamComplementFirst_ne_second x.val).symm)
  rw [seamComplementPartner_apply_second] at hh
  exact hh.symm

theorem seamImmediateFirstRight_target_first :
    seamState q.1 q.2 e.left = x.val.val (seamComplementFirst x.val) := by
  have hs := (seamImmediateFirstRight_sides p q x e f he hf hle hlf).2
  rw [seamImmediate_left_column_eq p q x e f hle hlf, f.map_left, hs]

theorem seamImmediateFirstRight_target_second :
    seamState q.1 q.2 (seamComplementSecond x.val) = x.val.val (seamComplementSecond x.val) := by
  have hs := (seamImmediateFirstRight_sides p q x e f he hf hle hlf).2
  exact f.map_of_ne _
    (by rw [← seamImmediate_left_column_eq p q x e f hle hlf]
        exact (seamImmediate_left_ne_second x e.left hle).symm)
    (by rw [hs]; exact (seamComplementFirst_ne_second x.val).symm)

theorem seamImmediateFirstRight_source_pivot :
    seamState p.1 p.2 (seamComplementFirst x.val) = x.val.val e.left := by
  have hs := (seamImmediateFirstRight_sides p q x e f he hf hle hlf).1
  have hh := e.map_left
  rw [hs, seamComplementPartner_firstBlock_apply x.val e.left hle] at hh
  exact hh.symm

/-- The two empty row pieces exclude every point on their common column strip. -/
theorem seamImmediateFirstRight_strip_empty (c : Fin (n + m + 1))
    (hc : c ∈ Grid.cIoo e.left e.right) :
    seamState p.1 p.2 c ∉ Grid.cIoo
      (x.val.val (seamComplementSecond x.val)) (x.val.val (seamComplementFirst x.val)) := by
  obtain ⟨hpE, hpF⟩ := seamImmediateFirstRight_sides p q x e f he hf hle hlf
  have hA := seamImmediate_left_column_eq p q x e f hle hlf
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hPQ := seamComplementFirst_lt_second x.val
  have hab : e.left.val < e.right.val := by rw [hpE]; omega
  have hcs := (Grid.mem_cIoo _ _ _).mp hc
  rw [if_pos hab] at hcs
  have hca : c ≠ e.left := by intro hh; have := congrArg Fin.val hh; omega
  have hcp : c ≠ seamComplementFirst x.val := by
    intro hh
    have := congrArg Fin.val hh
    rw [hpE] at hcs
    omega
  have hcq : c ≠ seamComplementSecond x.val := by
    intro hh
    have := congrArg Fin.val hh
    rw [hpE] at hcs
    omega
  have hx := e.map_of_ne c hca (by simpa only [hpE] using hcp)
  change x.val.val.swapColumns (seamComplementFirst x.val)
    (seamComplementSecond x.val) c = _ at hx
  rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcp hcq] at hx
  have hNE : n < (x.val.val e.left).val := by
    have hh : e.left ∈ seamNortheastColumns x.val.val := by
      rw [seamMatchingEntry_northeast_eq_singleton p x e, if_pos hle]
      exact Finset.mem_singleton_self _
    exact ((mem_seamNortheastColumns _ _).mp hh).2
  have hcut : x.val.val e.left ∈ Grid.cIoo
      (x.val.val (seamComplementSecond x.val)) (x.val.val (seamComplementFirst x.val)) := by
    rw [Grid.mem_cIoo, if_neg (not_lt_of_ge x.property.le)]
    exact ⟨fun hh => seamComplementFirst_ne_second x.val (x.val.val.toPerm.injective hh).symm,
      Or.inl (hQ.2.trans_lt hNE)⟩
  intro hr
  rw [← Grid.cIoo_union_insert_cIoo_eq_cIoo_of_mem_cIoo hcut] at hr
  rcases Finset.mem_union.mp hr with hr | hr
  · apply (isEmpty_iff_forall_notMem_cIoo e).mp he c hc
    simpa only [bottom_def, top_def, hpE,
      seamImmediateFirstRight_source_first p q x e f he hf hle hlf,
      seamImmediateFirstRight_source_pivot p q x e f he hf hle hlf] using hr
  · rcases Finset.mem_insert.mp hr with hr | hr
    · exact hca (x.val.val.toPerm.injective (hx.trans hr))
    · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf c (by simpa only [← hA, hpF, ← hpE] using hc)
      rw [bottom_def, top_def, ← hA, hpF, hx]
      exact hr

/-- The three exchanges yield the retained transposition on the low rows. -/
def seamImmediateFirstRightFullRectangle :
    GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2) where
  left := e.left
  right := seamComplementSecond x.val
  left_ne_right := seamImmediate_left_ne_second x e.left hle
  map_left := by
    rw [seamImmediateFirstRight_target_first p q x e f he hf hle hlf,
      seamImmediateFirstRight_source_second p q x e f he hf hle hlf]
  map_right := by
    rw [seamImmediateFirstRight_target_second p q x e f he hf hle hlf,
      seamImmediateFirstRight_source_first p q x e f he hf hle hlf]
  map_of_ne c hc hq := by
    obtain ⟨hpE, hpF⟩ := seamImmediateFirstRight_sides p q x e f he hf hle hlf
    have hA := seamImmediate_left_column_eq p q x e f hle hlf
    by_cases hp : c = seamComplementFirst x.val
    · subst c
      have hh₁ := e.map_left
      rw [hpE, seamComplementPartner_firstBlock_apply x.val e.left hle] at hh₁
      have hh₂ := f.map_right
      rw [hpF, ← hA] at hh₂
      exact hh₂.trans hh₁
    · have hh₁ := e.map_of_ne c hc (by simpa only [hpE] using hp)
      have hh₂ := f.map_of_ne c (by simpa only [← hA] using hc)
        (by simpa only [hpF] using hp)
      change x.val.val.swapColumns (seamComplementFirst x.val)
        (seamComplementSecond x.val) c = _ at hh₁
      rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hp hq] at hh₁
      exact hh₂.trans hh₁

theorem seamImmediateFirstRight_second_factor_eq : p.2 = q.2 :=
  seamRetainedRectangle_second_eq_of_side_lt p q
    (seamImmediateFirstRightFullRectangle p q x e f he hf hle hlf) (Or.inl hle)

/-- The actual first-factor rectangle associated with this immediate correction. -/
def seamImmediateFirstRightRectangle : GridRectangleBetween p.1 q.1 :=
  seamRetainedFirstRectangle p q
    (seamImmediateFirstRightFullRectangle p q x e f he hf hle hlf) (Or.inl hle)

@[simp] theorem seamImmediateFirstRightRectangle_left :
    (seamImmediateFirstRightRectangle p q x e f he hf hle hlf).left =
      seamFirstFactorIndex e.left := rfl

@[simp] theorem seamImmediateFirstRightRectangle_right :
    (seamImmediateFirstRightRectangle p q x e f he hf hle hlf).right = Fin.last n := by
  have hn := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)).1
  change seamFirstFactorIndex (seamComplementSecond x.val) = _
  simp only [seamFirstFactorIndex, dif_neg (not_lt_of_ge hn)]

/-- The projected first-factor rectangle is empty even though its full lift need not be. -/
theorem seamImmediateFirstRightRectangle_isEmpty :
    (seamImmediateFirstRightRectangle p q x e f he hf hle hlf).IsEmpty := by
  let R := seamImmediateFirstRightFullRectangle p q x e f he hf hle hlf
  let r := seamImmediateFirstRightRectangle p q x e f he hf hle hlf
  apply (isEmpty_iff_forall_notMem_cIoo r).mpr
  intro c hc hr
  have hindex : (seamFirstFactorIndex e.left).val = e.left.val := by
    simp only [seamFirstFactorIndex, dif_pos hle]
  have hcols := (Grid.mem_cIoo _ _ _).mp hc
  change r.left ≠ r.right ∧ _ at hcols
  have hleft : r.left.val = e.left.val := by
    change (seamFirstFactorIndex e.left).val = _
    exact hindex
  have hright : r.right = Fin.last n :=
    seamImmediateFirstRightRectangle_right p q x e f he hf hle hlf
  rw [if_pos (by rw [hleft, hright]; exact hle)] at hcols
  have hcl : e.left.val < c.val := by rw [← hleft]; exact hcols.2.1
  have hcn : c.val < n := by simpa only [hright, Fin.val_last] using hcols.2.2
  let d : Fin n := ⟨c.val, hcn⟩
  have hdc : d.castSucc = c := Fin.ext rfl
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hpE := (seamImmediateFirstRight_sides p q x e f he hf hle hlf).1
  have hdc_mem : seamLeft n m d.castSucc ∈ Grid.cIoo e.left e.right := by
    rw [Grid.mem_cIoo, if_pos (by rw [hpE]; omega)]
    exact ⟨e.left_ne_right,
      hcl, by rw [hpE]; change d.val < (seamComplementFirst x.val).val; omega⟩
  apply seamImmediateFirstRight_strip_empty p q x e f he hf hle hlf _ hdc_mem
  have hb := seamRetainedFirstRectangle_bottom_recovery p q R (Or.inl hle)
  have ht := seamRetainedFirstRectangle_top_recovery p q R (Or.inl hle)
  change seamLeft n m r.bottom = seamState p.1 p.2 e.left at hb
  change seamLeft n m r.top = seamState p.1 p.2 (seamComplementSecond x.val) at ht
  rw [seamImmediateFirstRight_source_first p q x e f he hf hle hlf] at hb
  rw [seamImmediateFirstRight_source_second p q x e f he hf hle hlf] at ht
  rw [seamState_left_castSucc, hdc, ← hb, ← ht, seamLeft_mem_cIoo_iff]
  exact hr

/-- A simultaneous entry and exit of this orientation forces the first pivot to the seam. -/
theorem seamImmediateFirstRight_pivot_eq_cut : (seamComplementFirst x.val).val = n := by
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hPQ := seamComplementFirst_lt_second x.val
  have hpE := (seamImmediateFirstRight_sides p q x e f he hf hle hlf).1
  by_contra hn
  have hnP : n < (seamComplementFirst x.val).val := by omega
  let c := seamLeft n m (Fin.last n)
  have hcv : c.val = n := rfl
  have hc : c ∈ Grid.cIoo e.left e.right := by
    rw [Grid.mem_cIoo, if_pos (by rw [hpE]; omega)]
    exact ⟨e.left_ne_right, by omega, by rw [hpE]; omega⟩
  have hca : c ≠ e.left := by intro hh; have := congrArg Fin.val hh; omega
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
    have hmin : seamComplementFirst x.val ≤ c := Finset.min'_le _ _ hcSW
    omega
  have hx := e.map_of_ne c hca (by simpa only [hpE] using hcp)
  change x.val.val.swapColumns (seamComplementFirst x.val)
    (seamComplementSecond x.val) c = _ at hx
  rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcp hcq] at hx
  apply seamImmediateFirstRight_strip_empty p q x e f he hf hle hlf c hc
  rw [← hx, Grid.mem_cIoo, if_neg (not_lt_of_ge x.property.le)]
  exact ⟨fun hh => seamComplementFirst_ne_second x.val (x.val.val.toPerm.injective hh).symm,
    Or.inl (hQ.2.trans_lt hhigh)⟩

/-- The full retained transposition is obstructed by the actual exchanged high point. -/
theorem seamImmediateFirstRightFullRectangle_not_isEmpty :
    ¬ (seamImmediateFirstRightFullRectangle p q x e f he hf hle hlf).IsEmpty := by
  let R := seamImmediateFirstRightFullRectangle p q x e f he hf hle hlf
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hPQ := seamComplementFirst_lt_second x.val
  have hhigh : n < (x.val.val e.left).val := by
    have hh : e.left ∈ seamNortheastColumns x.val.val := by
      rw [seamMatchingEntry_northeast_eq_singleton p x e, if_pos hle]
      exact Finset.mem_singleton_self _
    exact ((mem_seamNortheastColumns _ _).mp hh).2
  intro heR
  apply (isEmpty_iff_forall_notMem_cIoo R).mp heR (seamComplementFirst x.val)
  · change seamComplementFirst x.val ∈ Grid.cIoo e.left (seamComplementSecond x.val)
    rw [Grid.mem_cIoo, if_pos (by omega)]
    exact ⟨seamImmediate_left_ne_second x e.left hle, by omega, hPQ⟩
  · change seamState p.1 p.2 (seamComplementFirst x.val) ∈
      Grid.cIoo (seamState p.1 p.2 e.left)
        (seamState p.1 p.2 (seamComplementSecond x.val))
    rw [seamImmediateFirstRight_source_pivot p q x e f he hf hle hlf,
      seamImmediateFirstRight_source_first p q x e f he hf hle hlf,
      seamImmediateFirstRight_source_second p q x e f he hf hle hlf,
      Grid.mem_cIoo, if_neg (not_lt_of_ge x.property.le)]
    exact ⟨fun hh => seamComplementFirst_ne_second x.val (x.val.val.toPerm.injective hh).symm,
      Or.inl (hQ.2.trans_lt hhigh)⟩

/-- This empty factor rectangle is absent from the direct projection's image. -/
theorem seamImmediateFirstRightRectangle_lift_not_isEmpty :
    ¬ (seamFirstFactorRectangle
      (seamImmediateFirstRightRectangle p q x e f he hf hle hlf) p.2).IsEmpty := by
  have hz := seamImmediateFirstRight_second_factor_eq p q x e f he hf hle hlf
  rcases q with ⟨q₁, q₂⟩
  change p.2 = q₂ at hz
  subst q₂
  change ¬ (seamFirstFactorRectangle
    (seamRetainedFirstRectangle p (q₁, p.2)
      (seamImmediateFirstRightFullRectangle p (q₁, p.2) x e f he hf hle hlf)
        (Or.inl hle)) p.2).IsEmpty
  rw [seamFirstFactorRectangle_lift_project]
  exact seamImmediateFirstRightFullRectangle_not_isEmpty p (q₁, p.2) x e f he hf hle hlf

end FirstRight
end OnLeConjecture.KnotFloer.GridFull

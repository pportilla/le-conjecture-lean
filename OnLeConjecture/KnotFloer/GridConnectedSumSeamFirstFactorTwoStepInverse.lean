/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorTwoStepMetadata
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorTwoStepLift

/-!
# Uniqueness of the two-transition first-factor correction

A complete correction with fixed second factor and two intermediate
northeast points is determined by its projected first-factor rectangle.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable

/-- Four empty rectangles through three matching sources, with two middle northeast points. -/
abbrev SeamTwoStepFirstData (p q : SeamRetainedIndex n m) :=
  Σ x : SeamMatchingSource n m, Σ y : SeamMatchingSource n m, Σ z : SeamMatchingSource n m,
    {e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val // e.IsEmpty} ×
    {r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val // r.IsEmpty} ×
    {t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val // t.IsEmpty} ×
    {f : GridRectangleBetween z.val.val (seamState q.1 q.2) // f.IsEmpty} ×
    {_u : Unit // (seamNortheastColumns y.val.val).card = 2}

instance seamTwoStepFirstDataFintype (p q : SeamRetainedIndex n m) :
    Fintype (SeamTwoStepFirstData p q) := inferInstance

def seamTwoStepFirstProjection (p q : SeamRetainedIndex n m) (hpq : p.2 = q.2)
    (d : SeamTwoStepFirstData p q) : GridRectangleBetween p.1 q.1 :=
  match d with
  | ⟨x, y, z, e, r, t, f, h⟩ => seamTwoStepFirstRectangle p q x y z
      e.val r.val t.val f.val e.property r.property t.property f.property h.property hpq

theorem seamTwoStepFirstProjection_injective
    (p q : SeamRetainedIndex n m) (hpq : p.2 = q.2) :
    Function.Injective (seamTwoStepFirstProjection p q hpq) := by
  rintro ⟨x, y, z, e, r, t, f, h⟩ ⟨x', y', z', e', r', t', f', h'⟩ hh
  have hm := h.property
  have hm' := h'.property
  have hc := seamTwoStepFirstRectangle_columns p q x y z e.val r.val t.val f.val
    e.property r.property t.property f.property hm hpq
  have hc' := seamTwoStepFirstRectangle_columns p q x' y' z' e'.val r'.val t'.val f'.val
    e'.property r'.property t'.property f'.property hm' hpq
  have hA : r.val.left = r'.val.left := by
    apply Fin.ext
    have hval := congrArg (fun R => R.left.val) hh
    exact hc.1.symm.trans (hval.trans hc'.1)
  have hB : e.val.right = e'.val.right := by
    apply Fin.ext
    have hval := congrArg (fun R => R.right.val) hh
    exact hc.2.1.symm.trans (hval.trans hc'.2.1)
  have ho := seamTwoStep_complete_outer_right p q x y z e.val r.val t.val f.val
    e.property r.property t.property f.property hm hpq
  have ho' := seamTwoStep_complete_outer_right p q x' y' z' e'.val r'.val t'.val f'.val
    e'.property r'.property t'.property f'.property hm' hpq
  have hQ : seamComplementSecond x.val = seamComplementSecond x'.val := by
    apply Fin.ext
    exact (seamTwoStep_complete_outer_last p q x y z e.val r.val t.val f.val
      e.property r.property t.property f.property hm hpq).trans
      (seamTwoStep_complete_outer_last p q x' y' z' e'.val r'.val t'.val f'.val
        e'.property r'.property t'.property f'.property hm' hpq).symm
  have hE := seamMatchingEntry_left_eq_second_of_right_lt p x e.val e.property ho.1
  have hE' := seamMatchingEntry_left_eq_second_of_right_lt p x' e'.val e'.property ho'.1
  have hEL : e.val.left = e'.val.left := hE.trans (hQ.trans hE'.symm)
  have hxx : x = x' := by
    apply Subtype.ext
    apply seamComplementPartner_involutive.injective
    apply Subtype.ext
    rw [e.val.target_eq_swapColumns, e'.val.target_eq_swapColumns, hEL, hB]
  subst x'
  have hee : e = e' := Subtype.ext (GridRectangleBetween.ext hEL hB)
  subst e'
  have hcut := seamTwoStep_complete_inner_cut p q x y z e.val r.val t.val f.val
    e.property r.property t.property f.property hm hpq
  have hcut' := seamTwoStep_complete_inner_cut p q x y' z' e.val r'.val t'.val f'.val
    e.property r'.property t'.property f'.property hm' hpq
  have hC : r.val.right = r'.val.right := Fin.ext (hcut.1.trans hcut'.1.symm)
  have hyy : y = y' := by
    apply Subtype.ext
    apply seamComplementPartner_involutive.injective
    apply Subtype.ext
    rw [r.val.target_eq_swapColumns, r'.val.target_eq_swapColumns, hA, hC]
  subst y'
  have hrr : r = r' := Subtype.ext (GridRectangleBetween.ext hA hC)
  subst r'
  have hsame := seamTwoStep_complete_inner_left_eq p q x y z e.val r.val t.val f.val
    e.property r.property t.property f.property hm hpq
  have hsame' := seamTwoStep_complete_inner_left_eq p q x y z' e.val r.val t'.val f'.val
    e.property r.property t'.property f'.property hm' hpq
  have htA : t.val.left = t'.val.left := hsame.symm.trans hsame'
  have htC : t.val.right = t'.val.right := Fin.ext (hcut.2.trans hcut'.2.symm)
  have hzz : z = z' := by
    apply Subtype.ext
    apply seamComplementPartner_involutive.injective
    apply Subtype.ext
    rw [t.val.target_eq_swapColumns, t'.val.target_eq_swapColumns, htA, htC]
  subst z'
  have htt : t = t' := Subtype.ext (GridRectangleBetween.ext htA htC)
  subst t'
  have houter := seamTwoStep_complete_outer_right_eq p q x y z e.val r.val t.val f.val
    e.property r.property t.property f.property hm hpq
  have houter' := seamTwoStep_complete_outer_right_eq p q x y z e.val r.val t.val f'.val
    e.property r.property t.property f'.property hm' hpq
  have hF := seamMatchingExit_left_eq_second_of_right_lt q z f.val f.property ho.2
  have hF' := seamMatchingExit_left_eq_second_of_right_lt q z f'.val f'.property ho'.2
  have hff : f = f' := Subtype.ext (GridRectangleBetween.ext (hF.trans hF'.symm)
    (houter.symm.trans houter'))
  subst f'
  have hhh : h = h' := Subsingleton.elim _ _
  subst h'
  rfl

/-- The specified two-transition correction paths with two middle northeast points. -/
abbrev SeamFirstBirthDeathCorrection (p q : SeamRetainedIndex n m) :=
  {d : SeamCorrectionPath 2 p q //
    (seamNortheastColumns d.2.2.2.1.1.val.val).card = 2}

instance seamFirstBirthDeathCorrectionFintype (p q : SeamRetainedIndex n m) :
    Fintype (SeamFirstBirthDeathCorrection p q) := inferInstance

def seamTwoStepFirstData_of_correction (p q : SeamRetainedIndex n m)
    (d : SeamFirstBirthDeathCorrection p q) : SeamTwoStepFirstData p q := by
  rcases d with ⟨⟨x, z, e, ⟨y, r, ⟨z', t, tail⟩⟩, f⟩, hm⟩
  have hz : z' = z := tail.property
  subst z'
  exact ⟨x, y, z, e, ⟨r.val, r.property.2⟩, ⟨t.val, t.property.2⟩, f, ⟨(), hm⟩⟩

def seamTwoStepFirstData_to_correction (p q : SeamRetainedIndex n m)
    (d : SeamTwoStepFirstData p q) : SeamFirstBirthDeathCorrection p q := by
  rcases d with ⟨x, y, z, e, r, t, f, hm⟩
  have hxy : x ≠ y := by
    intro hh
    have hc := seamMatchingEntry_northeast_card p x e.val
    rw [hh, hm.property] at hc
    omega
  have hyz : y ≠ z := by
    intro hh
    have hc := seamMatchingExit_northeast_card q z f.val
    rw [← hh, hm.property] at hc
    omega
  exact ⟨⟨x, z, e, ⟨y, ⟨r.val, hxy, r.property⟩,
    ⟨z, ⟨t.val, hyz, t.property⟩, ⟨(), rfl⟩⟩⟩, f⟩, hm.property⟩

/-- The finite four-rectangle description and the existing correction-path description agree. -/
def seamTwoStepFirstDataEquivCorrection (p q : SeamRetainedIndex n m) :
    SeamTwoStepFirstData p q ≃ SeamFirstBirthDeathCorrection p q where
  toFun := seamTwoStepFirstData_to_correction p q
  invFun := seamTwoStepFirstData_of_correction p q
  left_inv := by
    rintro ⟨x, y, z, e, r, t, f, ⟨⟨⟩, hm⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨x, z, e, ⟨y, r, ⟨z', t, tail⟩⟩, f⟩, hm⟩
    have hz : z' = z := tail.property
    subst z'
    rfl

theorem seamTwoStepFirstProjection_of_correction_columns
    (p q : SeamRetainedIndex n m) (hpq : p.2 = q.2)
    (d : SeamFirstBirthDeathCorrection p q) :
    let R := seamTwoStepFirstProjection p q hpq (seamTwoStepFirstData_of_correction p q d)
    R.left = seamFirstFactorIndex d.val.2.2.2.1.2.1.val.left ∧
      R.right = seamFirstFactorIndex d.val.2.2.1.val.right := by
  rcases d with ⟨⟨x, z, e, ⟨y, r, ⟨z', t, tail⟩⟩, f⟩, hm⟩
  have hz : z' = z := tail.property
  subst z'
  simp only [seamTwoStepFirstData_of_correction, seamTwoStepFirstProjection,
    seamTwoStepFirstRectangle, seamRetainedFirstRectangle_left,
    seamRetainedFirstRectangle_right, seamTwoStepFirstFullRectangle,
    ofSwapColumns_left, ofSwapColumns_right, and_self]

section Forward
variable {u v : GridState (n + 1)} (R : GridRectangleBetween u v) (w : GridState (m + 1))
    (hR : R.IsEmpty) (hblock : ¬ (seamFirstFactorRectangle R w).IsEmpty)
    (hleft : R.left ≠ Fin.last n) (hright : R.right ≠ Fin.last n)
    (hzero : 0 < (w.toPerm.symm 0).val) (hlast : (w.toPerm.symm 0).val < m)

set_option backward.isDefEq.respectTransparency false in
theorem seamFirstFactorTwoStepLift_interior_sides :
    let d := seamFirstFactorTwoStepLift_interior R w hR hblock hleft hright hzero hlast
    d.2.2.1.val.right = seamLeft n m R.right ∧
    d.2.2.2.1.2.1.val.left = seamLeft n m R.left ∧
    d.2.2.2.1.2.1.val.right = seamRight n m 0 := by
  unfold seamFirstFactorTwoStepLift_interior
  generalize hspec : seamFirstFactor_blocked_nonlast_ranges R w hR hblock hleft hright = spec
  rcases spec with ⟨hm, hcols, hln, hrn, hlo, hhi⟩
  simp only [ofSwapColumns_right, ofSwapColumns_left, and_self]

set_option backward.isDefEq.respectTransparency false in
theorem seamFirstFactorTwoStepLift_interior_first_rows :
    let d := seamFirstFactorTwoStepLift_interior R w hR hblock hleft hright hzero hlast
    d.2.2.2.1.2.1.val.bottom = seamLeft n m R.bottom ∧
      d.2.2.2.1.2.1.val.top = seamRight n m (w 0) := by
  have hnL : R.left.val < n := by
    have hn := R.left.isLt
    have hh : R.left.val ≠ n := fun hh => hleft (Fin.ext hh)
    omega
  have hnR : R.right.val < n := by
    have hn := R.right.isLt
    have hh : R.right.val ≠ n := fun hh => hright (Fin.ext hh)
    omega
  have hz : w 0 ≠ 0 := by
    intro hh
    have hp : w.toPerm.symm 0 = 0 := w.toPerm.symm_apply_eq.mpr hh.symm
    rw [hp] at hzero
    exact Nat.lt_irrefl 0 hzero
  have hAD : seamLeft n m R.left ≠ seamRight n m (w.toPerm.symm 0) := by
    intro hh; have hv := congrArg Fin.val hh; simp only [seamLeft_val, seamRight_val] at hv; omega
  have hAE : seamLeft n m R.left ≠ seamRight n m (Fin.last m) := by
    intro hh; have hv := congrArg Fin.val hh
    simp only [seamLeft_val, seamRight_val, Fin.val_last] at hv; omega
  have hAB : seamLeft n m R.left ≠ seamLeft n m R.right :=
    fun hh => R.left_ne_right (seamLeft_injective hh)
  have hCD : seamRight n m 0 ≠ seamRight n m (w.toPerm.symm 0) := by
    intro hh; have hv := congrArg Fin.val hh
    simp only [seamRight_val, Fin.val_zero] at hv; omega
  have hCE : seamRight n m 0 ≠ seamRight n m (Fin.last m) := by
    intro hh; have hv := congrArg Fin.val hh
    simp only [seamRight_val, Fin.val_zero, Fin.val_last] at hv; omega
  have hCB : seamRight n m 0 ≠ seamLeft n m R.right := by
    intro hh; have hv := congrArg Fin.val hh
    simp only [seamRight_val, seamLeft_val, Fin.val_zero] at hv; omega
  unfold seamFirstFactorTwoStepLift_interior
  generalize hspec : seamFirstFactor_blocked_nonlast_ranges R w hR hblock hleft hright = spec
  rcases spec with ⟨hm, hcols, hln, hrn, hlo, hhi⟩
  simp only [bottom_def, top_def, ofSwapColumns_left, ofSwapColumns_right,
    seamShortLift_matchingSourceOfPair, GridState.swapColumns_apply,
    Equiv.swap_apply_of_ne_of_ne hAD hAE, Equiv.swap_apply_of_ne_of_ne hAE hAB,
    Equiv.swap_apply_of_ne_of_ne hCD hCE, Equiv.swap_apply_of_ne_of_ne hCE hCB]
  exact ⟨seamShortLift_seamState_left_ne_last u w R.left hleft,
    seamState_right_of_ne_zero u w 0 hz⟩

theorem seamFirstFactorTwoStepLift_interior_middle_card :
    let d := seamFirstFactorTwoStepLift_interior R w hR hblock hleft hright hzero hlast
    (seamNortheastColumns d.2.2.2.1.1.val.val).card = 2 := by
  let d := seamFirstFactorTwoStepLift_interior R w hR hblock hleft hright hzero hlast
  have hs := seamFirstFactorTwoStepLift_interior_sides R w hR hblock hleft hright hzero hlast
  have hv := seamFirstFactorTwoStepLift_interior_first_rows R w hR hblock hleft hright hzero hlast
  have hz : w 0 ≠ 0 := by
    intro hh
    have hp : w.toPerm.symm 0 = 0 := w.toPerm.symm_apply_eq.mpr hh.symm
    rw [hp] at hzero
    exact Nat.lt_irrefl 0 hzero
  have hhigh : n < (seamRight n m (w 0)).val := by
    have hh : (w 0).val ≠ 0 := fun hh => hz (Fin.ext hh)
    simp only [seamRight_val]
    omega
  have hL : d.2.2.2.1.2.1.val.left.val < n := by
    rw [hs.2.1, seamLeft_val]
    have hn := R.left.isLt
    have hh : R.left.val ≠ n := fun hh => hleft (Fin.ext hh)
    omega
  have hR' : n ≤ d.2.2.2.1.2.1.val.right.val := by
    rw [hs.2.2, seamRight_val, Fin.val_zero]; omega
  have hbottom : d.2.2.2.1.2.1.val.bottom.val ≤ n := by
    rw [hv.1, seamLeft_val]
    exact Nat.le_of_lt_succ R.bottom.isLt
  have htop : n < d.2.2.2.1.2.1.val.top.val := by rw [hv.2]; exact hhigh
  have hsw := seamRectangle_birth_southwest_insert_right d.2.2.2.1.2.1.val hL hR' hbottom htop
  rw [seamComplementPartner_southwestColumns] at hsw
  have hnot : d.2.2.2.1.2.1.val.right ∉ seamSouthwestColumns d.1.val.val := by
    intro hh
    have hh := ((mem_seamSouthwestColumns _ _).mp hh).2
    change (d.1.val.val d.2.2.2.1.2.1.val.right).val ≤ n at hh
    change n < (d.1.val.val d.2.2.2.1.2.1.val.right).val at htop
    omega
  have hcard := congrArg Finset.card hsw
  rw [Finset.card_insert_of_notMem hnot,
    seamMatchingEntry_southwest_card (u, w) d.1 d.2.2.1.val,
    seamSouthwestColumns_card] at hcard
  change (seamNortheastColumns d.2.2.2.1.1.val.val).card = 2
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Projecting the constructed two-transition lift recovers the original factor rectangle. -/
theorem seamTwoStepFirstProjection_lift_interior :
    seamTwoStepFirstProjection (u, w) (v, w) rfl
      (seamTwoStepFirstData_of_correction (u, w) (v, w)
        ⟨seamFirstFactorTwoStepLift_interior R w hR hblock hleft hright hzero hlast,
          seamFirstFactorTwoStepLift_interior_middle_card R w hR hblock hleft hright hzero hlast⟩) =
      R := by
  let d : SeamFirstBirthDeathCorrection (u, w) (v, w) :=
    ⟨seamFirstFactorTwoStepLift_interior R w hR hblock hleft hright hzero hlast,
      seamFirstFactorTwoStepLift_interior_middle_card R w hR hblock hleft hright hzero hlast⟩
  have hc := seamTwoStepFirstProjection_of_correction_columns (u, w) (v, w) rfl d
  have hs := seamFirstFactorTwoStepLift_interior_sides R w hR hblock hleft hright hzero hlast
  have hnL : R.left.val < n := by
    have hn := R.left.isLt
    have hh : R.left.val ≠ n := fun hh => hleft (Fin.ext hh)
    omega
  have hnR : R.right.val < n := by
    have hn := R.right.isLt
    have hh : R.right.val ≠ n := fun hh => hright (Fin.ext hh)
    omega
  apply GridRectangleBetween.ext
  · change (seamTwoStepFirstProjection (u, w) (v, w) rfl
      (seamTwoStepFirstData_of_correction (u, w) (v, w) d)).left = _
    rw [hc.1, hs.2.1]
    apply Fin.ext
    simp only [seamFirstFactorIndex, seamLeft_val]
    rw [dif_pos hnL]
  · change (seamTwoStepFirstProjection (u, w) (v, w) rfl
      (seamTwoStepFirstData_of_correction (u, w) (v, w) d)).right = _
    rw [hc.2, hs.1]
    apply Fin.ext
    simp only [seamFirstFactorIndex, seamLeft_val]
    rw [dif_pos hnR]

end Forward

/-- The missing nonlast first-factor rectangles with an interior second-factor zero preimage. -/
abbrev SeamObstructedFirstInteriorRectangle
    (u v : GridState (n + 1)) (w : GridState (m + 1)) :=
  {R : GridRectangleBetween u v // R.IsEmpty ∧ ¬ (seamFirstFactorRectangle R w).IsEmpty ∧
    R.left ≠ Fin.last n ∧ R.right ≠ Fin.last n ∧
      0 < (w.toPerm.symm 0).val ∧ (w.toPerm.symm 0).val < m}

instance seamObstructedFirstInteriorRectangleFintype
    (u v : GridState (n + 1)) (w : GridState (m + 1)) :
    Fintype (SeamObstructedFirstInteriorRectangle u v w) := inferInstance

/-- All obstruction and boundary conditions are derived from the specified path. -/
def seamTwoStepFirstMissingProjection
    (u v : GridState (n + 1)) (w : GridState (m + 1))
    (d : SeamTwoStepFirstData (u, w) (v, w)) : SeamObstructedFirstInteriorRectangle u v w := by
  rcases d with ⟨x, y, z, e, r, t, f, h⟩
  refine ⟨seamTwoStepFirstRectangle (u, w) (v, w) x y z e.val r.val t.val f.val
      e.property r.property t.property f.property h.property rfl,
    seamTwoStepFirstRectangle_isEmpty (u, w) (v, w) x y z e.val r.val t.val f.val
      e.property r.property t.property f.property h.property rfl,
    seamTwoStepFirstRectangle_lift_not_isEmpty (u, w) (v, w) x y z e.val r.val t.val f.val
      e.property r.property t.property f.property h.property rfl, ?_⟩
  have hc := seamTwoStepFirstRectangle_columns (u, w) (v, w) x y z e.val r.val t.val f.val
    e.property r.property t.property f.property h.property rfl
  exact ⟨hc.2.2.1, hc.2.2.2,
    seamTwoStep_zero_preimage_interior (u, w) (v, w) x y z e.val r.val t.val f.val
      e.property r.property t.property f.property h.property rfl⟩

@[simp] theorem seamTwoStepFirstMissingProjection_val
    (u v : GridState (n + 1)) (w : GridState (m + 1))
    (d : SeamTwoStepFirstData (u, w) (v, w)) :
    (seamTwoStepFirstMissingProjection u v w d).val =
      seamTwoStepFirstProjection (u, w) (v, w) rfl d := by
  rcases d with ⟨x, y, z, e, r, t, f, h⟩
  rfl

theorem seamTwoStepFirstMissingProjection_bijective
    (u v : GridState (n + 1)) (w : GridState (m + 1)) :
    Function.Bijective (seamTwoStepFirstMissingProjection u v w) := by
  constructor
  · intro a b hh
    apply seamTwoStepFirstProjection_injective (u, w) (v, w) rfl
    simpa only [seamTwoStepFirstMissingProjection_val] using congrArg Subtype.val hh
  · rintro ⟨R, he, hb, hl, hr, hzero, hlast⟩
    refine ⟨seamTwoStepFirstData_of_correction (u, w) (v, w)
      ⟨seamFirstFactorTwoStepLift_interior R w he hb hl hr hzero hlast,
        seamFirstFactorTwoStepLift_interior_middle_card R w he hb hl hr hzero hlast⟩, ?_⟩
    apply Subtype.ext
    rw [seamTwoStepFirstMissingProjection_val]
    exact seamTwoStepFirstProjection_lift_interior R w he hb hl hr hzero hlast

/-- Exact finite bijection for the specified two-transition birth-death corrections. -/
def seamFirstFactorTwoStepEquiv
    (u v : GridState (n + 1)) (w : GridState (m + 1)) :
    SeamFirstBirthDeathCorrection (u, w) (v, w) ≃
      SeamObstructedFirstInteriorRectangle u v w :=
  (seamTwoStepFirstDataEquivCorrection (u, w) (v, w)).symm.trans
    (Equiv.ofBijective (seamTwoStepFirstMissingProjection u v w)
      (seamTwoStepFirstMissingProjection_bijective u v w))

/-- The inverse is precisely the previously constructed two-transition lift. -/
theorem seamFirstFactorTwoStepEquiv_symm
    (u v : GridState (n + 1)) (w : GridState (m + 1))
    (R : SeamObstructedFirstInteriorRectangle u v w) :
    ((seamFirstFactorTwoStepEquiv u v w).symm R).val =
      seamFirstFactorTwoStepLift_interior R.val w R.property.1 R.property.2.1
        R.property.2.2.1 R.property.2.2.2.1 R.property.2.2.2.2.1 R.property.2.2.2.2.2 := by
  let d : SeamFirstBirthDeathCorrection (u, w) (v, w) :=
    ⟨seamFirstFactorTwoStepLift_interior R.val w R.property.1 R.property.2.1
        R.property.2.2.1 R.property.2.2.2.1 R.property.2.2.2.2.1 R.property.2.2.2.2.2,
      seamFirstFactorTwoStepLift_interior_middle_card R.val w R.property.1 R.property.2.1
        R.property.2.2.1 R.property.2.2.2.1 R.property.2.2.2.2.1 R.property.2.2.2.2.2⟩
  have hh : seamFirstFactorTwoStepEquiv u v w d = R := by
    apply Subtype.ext
    change (seamTwoStepFirstMissingProjection u v w
      (seamTwoStepFirstData_of_correction (u, w) (v, w) d)).val = R.val
    rw [seamTwoStepFirstMissingProjection_val]
    exact seamTwoStepFirstProjection_lift_interior R.val w R.property.1 R.property.2.1
      R.property.2.2.1 R.property.2.2.2.1 R.property.2.2.2.2.1 R.property.2.2.2.2.2
  exact congrArg Subtype.val ((seamFirstFactorTwoStepEquiv u v w).symm_apply_eq.mpr hh.symm)

/-- Recovering the rectangle and applying its explicit lift reproduces the original path. -/
theorem seamFirstFactorTwoStep_reconstruct
    (u v : GridState (n + 1)) (w : GridState (m + 1))
    (d : SeamFirstBirthDeathCorrection (u, w) (v, w)) :
    let R := seamFirstFactorTwoStepEquiv u v w d
    seamFirstFactorTwoStepLift_interior R.val w R.property.1 R.property.2.1
      R.property.2.2.1 R.property.2.2.2.1 R.property.2.2.2.2.1 R.property.2.2.2.2.2 = d.val := by
  exact (seamFirstFactorTwoStepEquiv_symm u v w
    (seamFirstFactorTwoStepEquiv u v w d)).symm.trans
      (congrArg Subtype.val ((seamFirstFactorTwoStepEquiv u v w).symm_apply_apply d))

/-- This correspondence is an integer cardinality identity,
before reducing coefficients modulo two. -/
theorem seamFirstFactorTwoStep_card
    (u v : GridState (n + 1)) (w : GridState (m + 1)) :
    Fintype.card (SeamFirstBirthDeathCorrection (u, w) (v, w)) =
      Fintype.card (SeamObstructedFirstInteriorRectangle u v w) :=
  Fintype.card_congr (seamFirstFactorTwoStepEquiv u v w)

end OnLeConjecture.KnotFloer.GridFull

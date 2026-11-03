/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondFactorLift
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorShortLift

/-!
# Short corrections for second-factor rectangles with a zero row endpoint

For a wrapping second-factor rectangle with one zero row endpoint, a
nonempty retained lift has an immediate correction through a matching
source. The first-block pivot has row n in the bottom-zero case and row
zero in the top-zero case. Both correction rectangles exclude every
first-block point from their row interiors.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

theorem seamSecondShort_inverse_lt (x : GridState (n + 1)) (a : Fin (n + 1))
    (ha : x (Fin.last n) ≠ a) : (x.toPerm.symm a).val < n := by
  have hle := (x.toPerm.symm a).isLt
  have hne : (x.toPerm.symm a).val ≠ n := by
    intro hh
    have h : x.toPerm.symm a = Fin.last n := Fin.ext hh
    have hv := x.toPerm.apply_symm_apply a
    rw [h] at hv
    exact ha hv
  omega

/-- Every first-block column is inside a wrapping interval of second-block columns. -/
theorem seamSecondShort_firstColumn_mem (a : Fin n) (l r : Fin (m + 1)) (hrl : r < l) :
    seamLeft n m a.castSucc ∈ Grid.cIoo (seamRight n m l) (seamRight n m r) := by
  rw [Grid.mem_cIoo, if_neg (by simp only [seamRight_val]; omega)]
  refine ⟨fun hh => (ne_of_gt hrl) (seamRight_injective hh), Or.inr ?_⟩
  change a.val < n + r.val
  have hh := a.isLt
  omega

/-- Bottom-zero obstruction is equivalent to the last first-state row being below n. -/
theorem seamSecondFactorRectangle_blocked_bottom_zero_iff (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hcol : r.right < r.left) (hzero : r.bottom = 0) :
    ¬ (seamSecondFactorRectangle x r).IsEmpty ↔ (x (Fin.last n)).val < n := by
  have ht : r.top ≠ 0 := fun hh => r.bottom_ne_top (hzero.trans hh.symm)
  have htv : 0 < r.top.val := by
    have hh : r.top.val ≠ 0 := fun h => ht (Fin.ext h)
    omega
  rw [seamSecondFactorRectangle_not_isEmpty_iff x r he]
  constructor
  · rintro ⟨a, _, hv⟩
    rw [hzero, seamSecondFactorRow_zero, seamSecondFactorRow_of_ne_zero x _ ht,
      Grid.mem_cIoo, if_pos (by
        have hh := (x (Fin.last n)).isLt
        simp only [seamLeft_val, seamRight_val]
        omega)] at hv
    have ha := (x a.castSucc).isLt
    have hh := hv.2.1
    simp only [seamLeft_val] at hh
    omega
  · intro hh
    have hne : x (Fin.last n) ≠ Fin.last n := by intro h; rw [h] at hh; exact (lt_irrefl n) hh
    have ha := seamSecondShort_inverse_lt x (Fin.last n) hne
    let a : Fin n := ⟨(x.toPerm.symm (Fin.last n)).val, ha⟩
    have hv : x a.castSucc = Fin.last n := x.toPerm.apply_symm_apply (Fin.last n)
    refine ⟨a, seamSecondShort_firstColumn_mem a r.left r.right hcol, ?_⟩
    rw [hv, hzero, seamSecondFactorRow_zero, seamSecondFactorRow_of_ne_zero x _ ht,
      Grid.mem_cIoo, if_pos (by simp only [seamLeft_val, seamRight_val]; omega)]
    exact ⟨fun h => by
      have := congrArg Fin.val h
      simp only [seamLeft_val, seamRight_val] at this
      omega,
      hh, by change n < n + r.top.val; omega⟩

/-- The top-zero retained lift is obstructed precisely when the last first-state row is positive. -/
theorem seamSecondFactorRectangle_blocked_top_zero_iff (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hcol : r.right < r.left) (hzero : r.top = 0) :
    ¬ (seamSecondFactorRectangle x r).IsEmpty ↔ 0 < (x (Fin.last n)).val := by
  have hb : r.bottom ≠ 0 := fun hh => r.bottom_ne_top (hh.trans hzero.symm)
  have hbv : 0 < r.bottom.val := by
    have hh : r.bottom.val ≠ 0 := fun h => hb (Fin.ext h)
    omega
  rw [seamSecondFactorRectangle_not_isEmpty_iff x r he]
  constructor
  · rintro ⟨a, _, hv⟩
    rw [hzero, seamSecondFactorRow_zero, seamSecondFactorRow_of_ne_zero x _ hb,
      Grid.mem_cIoo, if_neg (by
        have hh := (x (Fin.last n)).isLt
        simp only [seamLeft_val, seamRight_val]
        omega)] at hv
    have ha := (x a.castSucc).isLt
    have hh := hv.2
    simp only [seamLeft_val, seamRight_val] at hh
    omega
  · intro hh
    have hne : x (Fin.last n) ≠ 0 := by intro h; rw [h] at hh; exact (lt_irrefl 0) hh
    have ha := seamSecondShort_inverse_lt x 0 hne
    let a : Fin n := ⟨(x.toPerm.symm 0).val, ha⟩
    have hv : x a.castSucc = 0 := x.toPerm.apply_symm_apply 0
    refine ⟨a, seamSecondShort_firstColumn_mem a r.left r.right hcol, ?_⟩
    rw [hv, hzero, seamSecondFactorRow_zero, seamSecondFactorRow_of_ne_zero x _ hb,
      Grid.mem_cIoo, if_neg (by
        have hv := (x (Fin.last n)).isLt
        simp only [seamLeft_val, seamRight_val]
        omega)]
    exact ⟨fun h => by
      have := congrArg Fin.val h
      simp only [seamLeft_val, seamRight_val] at this
      have hv := (x (Fin.last n)).isLt
      omega, Or.inr hh⟩

/-- The two distinct second-block endpoints contain exactly the required zero preimage. -/
theorem seamSecondShort_inverse_zero_of_bottom {z w : GridState (m + 1)}
    (r : GridRectangleBetween z w) (hzero : r.bottom = 0) :
    w.toPerm.symm 0 = r.right := by
  apply w.toPerm.injective
  rw [w.toPerm.apply_symm_apply, r.map_right]
  exact hzero.symm

theorem seamSecondShort_inverse_zero_of_top {z w : GridState (m + 1)}
    (r : GridRectangleBetween z w) (hzero : r.top = 0) :
    w.toPerm.symm 0 = r.left := by
  apply w.toPerm.injective
  rw [w.toPerm.apply_symm_apply, r.map_left]
  exact hzero.symm

/-- The triangle of swaps for the bottom-zero correction. -/
theorem seamSecondShort_swap_bottom (v : GridState (n + m + 1))
    (A P Q : Fin (n + m + 1)) (hAP : A ≠ P) (hAQ : A ≠ Q) (hPQ : P ≠ Q) :
    ((v.swapColumns Q P).swapColumns A Q).swapColumns P Q = v.swapColumns A P := by
  have hPA := hAP.symm
  have hQA := hAQ.symm
  have hQP := hPQ.symm
  apply GridState.ext
  intro c
  by_cases hA : c = A
  · subst c; simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
  by_cases hP : c = P
  · subst c; simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
  by_cases hQ : c = Q
  · subst c; simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
  simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]

/-- The triangle of swaps for the top-zero correction. -/
theorem seamSecondShort_swap_top (v : GridState (n + m + 1))
    (A P Q : Fin (n + m + 1)) (hAP : A ≠ P) (hAQ : A ≠ Q) (hPQ : P ≠ Q) :
    ((v.swapColumns Q P).swapColumns A P).swapColumns P Q = v.swapColumns Q A := by
  have hPA := hAP.symm
  have hQA := hAQ.symm
  have hQP := hPQ.symm
  apply GridState.ext
  intro c
  by_cases hA : c = A
  · subst c; simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
  by_cases hP : c = P
  · subst c; simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
  by_cases hQ : c = Q
  · subst c; simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]
  simp_all [GridState.swapColumns_apply, Equiv.swap_apply_def]

/-- Either part of the wrapping second-block interval projects into the factor interval. -/
theorem seamSecondShort_secondColumn_mem (l r : Fin (m + 1)) (hrl : r < l)
    (A : Fin (n + m + 1)) (hA : A.val < n) (d : Fin (m + 1))
    (hc : seamRight n m d ∈ Grid.cIoo A (seamRight n m r) ∨
      seamRight n m d ∈ Grid.cIoo (seamRight n m l) A) : d ∈ Grid.cIoo l r := by
  rw [Grid.mem_cIoo, if_neg (show ¬ l.val < r.val from not_lt_of_gt hrl)]
  refine ⟨ne_of_gt hrl, ?_⟩
  rcases hc with hc | hc
  · rw [Grid.mem_cIoo, if_pos (by simp only [seamRight_val]; omega)] at hc
    have hh := hc.2.2
    simp only [seamRight_val] at hh
    exact Or.inr (by omega)
  · rw [Grid.mem_cIoo, if_neg (by simp only [seamRight_val]; omega)] at hc
    have hh := hc.2
    simp only [seamRight_val] at hh
    exact Or.inl (by omega)

/-- Factor emptiness controls the high rows above n for the bottom-zero construction. -/
theorem seamSecondShort_bottom_empty (x : GridState (n + 1)) (v : GridState (m + 1))
    (l r t : Fin (m + 1)) (ht : t ≠ 0)
    (hf : ∀ d ∈ Grid.cIoo l r, v d ∉ Grid.cIoo 0 t)
    (C D : Fin (n + m + 1))
    (hc : ∀ d, seamRight n m d ∈ Grid.cIoo C D → d ∈ Grid.cIoo l r) :
    ∀ c ∈ Grid.cIoo C D, seamState x v c ∉
      Grid.cIoo (seamLeft n m (Fin.last n)) (seamRight n m t) := by
  have htv : 0 < t.val := by have hh : t.val ≠ 0 := fun h => ht (Fin.ext h); omega
  intro c hcol hv
  rw [Grid.mem_cIoo, if_pos (by simp only [seamLeft_val, seamRight_val]; omega)] at hv
  have hrow := hv.2
  rcases seamColumn_cases_strict c with ⟨a, rfl⟩ | ⟨d, rfl⟩
  · rw [seamState_left_castSucc] at hrow
    have hh := (x a.castSucc).isLt
    simp only [seamLeft_val, seamRight_val, Fin.val_last] at hrow
    omega
  · by_cases hz : v d = 0
    · rw [seamState_right_of_zero x v d hz] at hrow
      have hh := (x (Fin.last n)).isLt
      simp only [seamLeft_val, seamRight_val, Fin.val_last] at hrow
      omega
    · rw [seamState_right_of_ne_zero x v d hz] at hrow
      simp only [seamLeft_val, seamRight_val, Fin.val_last] at hrow
      apply hf d (hc d hcol)
      rw [Grid.mem_cIoo, Fin.val_zero, if_pos htv]
      exact ⟨ht.symm, by omega⟩

/-- Factor emptiness controls the high rows wrapping to zero for the top-zero construction. -/
theorem seamSecondShort_top_empty (x : GridState (n + 1)) (v : GridState (m + 1))
    (l r b : Fin (m + 1)) (hb : b ≠ 0)
    (hf : ∀ d ∈ Grid.cIoo l r, v d ∉ Grid.cIoo b 0)
    (C D : Fin (n + m + 1))
    (hc : ∀ d, seamRight n m d ∈ Grid.cIoo C D → d ∈ Grid.cIoo l r) :
    ∀ c ∈ Grid.cIoo C D, seamState x v c ∉
      Grid.cIoo (seamRight n m b) (seamLeft n m 0) := by
  have hbv : 0 < b.val := by have hh : b.val ≠ 0 := fun h => hb (Fin.ext h); omega
  intro c hcol hv
  rw [Grid.mem_cIoo, if_neg (by simp only [seamLeft_val, seamRight_val]; omega)] at hv
  have hrow := hv.2
  rcases seamColumn_cases_strict c with ⟨a, rfl⟩ | ⟨d, rfl⟩
  · rw [seamState_left_castSucc] at hrow
    have hh := (x a.castSucc).isLt
    simp only [seamLeft_val, seamRight_val, Fin.val_zero] at hrow
    omega
  · by_cases hz : v d = 0
    · rw [seamState_right_of_zero x v d hz] at hrow
      have hh := (x (Fin.last n)).isLt
      simp only [seamLeft_val, seamRight_val, Fin.val_zero] at hrow
      omega
    · rw [seamState_right_of_ne_zero x v d hz] at hrow
      simp only [seamLeft_val, seamRight_val, Fin.val_zero] at hrow
      apply hf d (hc d hcol)
      rw [Grid.mem_cIoo, if_neg (by change ¬ b.val < 0; omega)]
      exact ⟨hb, Or.inl (by omega)⟩

set_option backward.isDefEq.respectTransparency false in
/-- A blocked wrapping bottom-zero rectangle has an immediate mixed correction. -/
def seamSecondFactorShortLift_bottom_zero (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hblocked : ¬ (seamSecondFactorRectangle x r).IsEmpty)
    (hcol : r.right < r.left) (hzero : r.bottom = 0) :
    SeamCorrectionPath 0 (x, z) (x, w) := by
  classical
  have hx := (seamSecondFactorRectangle_blocked_bottom_zero_iff x r he hcol hzero).mp hblocked
  have hxn : x (Fin.last n) ≠ Fin.last n := by
    intro hh; rw [hh] at hx; exact (lt_irrefl n) hx
  let a := x.toPerm.symm (Fin.last n)
  let A := seamLeft n m a
  let P := seamRight n m r.right
  let Q := seamRight n m r.left
  let v := (seamState x w).swapColumns A Q
  have ha : a.val < n := seamSecondShort_inverse_lt x (Fin.last n) hxn
  have halast : a ≠ Fin.last n := by intro hh; rw [hh] at ha; exact (lt_irrefl n) ha
  have hA : A.val < n := ha
  have hP : n ≤ P.val := by change n ≤ n + r.right.val; omega
  have hQ : n ≤ Q.val := by change n ≤ n + r.left.val; omega
  have hPQ : P < Q := Nat.add_lt_add_left hcol n
  have hAP : A ≠ P := by intro hh; have := congrArg Fin.val hh; omega
  have hAQ : A ≠ Q := by intro hh; have := congrArg Fin.val hh; omega
  have ht : r.top ≠ 0 := fun hh => r.bottom_ne_top (hzero.trans hh.symm)
  have htv : n < (seamRight n m r.top).val := by
    have hh : r.top.val ≠ 0 := fun h => ht (Fin.ext h)
    simp only [seamRight_val]
    omega
  have hpA : seamState x z A = seamLeft n m (Fin.last n) := by
    rw [seamShortLift_seamState_left_ne_last x z a halast]
    exact congrArg (seamLeft n m) (x.toPerm.apply_symm_apply (Fin.last n))
  have hqA : seamState x w A = seamLeft n m (Fin.last n) := by
    rw [seamShortLift_seamState_left_ne_last x w a halast]
    exact congrArg (seamLeft n m) (x.toPerm.apply_symm_apply (Fin.last n))
  have hpP : seamState x z P = seamRight n m r.top :=
    seamState_right_of_ne_zero x z r.right ht
  have hqP : seamState x w P = seamLeft n m (x (Fin.last n)) :=
    seamState_right_of_zero x w r.right (r.map_right.trans hzero)
  have hqQ : seamState x w Q = seamRight n m r.top := by
    rw [seamState_secondFactorRow, r.map_left, ← top_def,
      seamSecondFactorRow_of_ne_zero x _ ht]
  have hvP : v P = seamLeft n m (x (Fin.last n)) := by
    rw [GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hAP.symm hPQ.ne, hqP]
  have hvQ : v Q = seamLeft n m (Fin.last n) := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_right, hqA]
  have hsw : seamSouthwestColumns v = {P, Q} := by
    let s := ofSwapColumns (seamState x w) v A Q hAQ rfl
    have hh := seamRectangle_birth_southwest_insert_right s
      (by simpa only [s, ofSwapColumns_left] using hA)
      (by simpa only [s, ofSwapColumns_right] using hQ)
      (by simp only [s, ofSwapColumns_bottom, hqA, seamLeft_val, Fin.val_last]; exact le_rfl)
      (by simpa only [s, ofSwapColumns_top, hqQ] using htv)
    simpa only [s, ofSwapColumns_right, seamState_southwest_singleton,
      seamSecondShort_inverse_zero_of_bottom r hzero, Finset.pair_comm] using hh
  have hrows : (v P).val < (v Q).val := by
    rw [hvP, hvQ, seamLeft_val, seamLeft_val]
    exact hx
  have hswap : seamState x w = (seamState x z).swapColumns Q P :=
    (seamSecondFactorRectangle x r).target_eq_swapColumns
  have hentry : v.swapColumns P Q = (seamState x z).swapColumns A P := by
    change ((seamState x w).swapColumns A Q).swapColumns P Q = _
    rw [hswap, seamSecondShort_swap_bottom _ A P Q hAP hAQ hPQ.ne]
  have hexit : seamState x w = v.swapColumns Q A := by
    change seamState x w = ((seamState x w).swapColumns A Q).swapColumns Q A
    rw [GridState.swapColumns_comm Q A, GridState.swapColumns_swapColumns]
  let entry := ofSwapColumns (seamState x z) (v.swapColumns P Q) A P hAP hentry
  let exit := ofSwapColumns v (seamState x w) Q A hAQ.symm hexit
  have hfSource : ∀ d ∈ Grid.cIoo r.left r.right, z d ∉ Grid.cIoo 0 r.top := by
    simpa only [hzero] using (isEmpty_iff_forall_notMem_cIoo r).mp he
  have hfTarget : ∀ d ∈ Grid.cIoo r.left r.right, w d ∉ Grid.cIoo 0 r.top := by
    simpa only [hzero] using seamShortLift_target_empty r he
  have heEntry : entry.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo entry).mpr
    simpa only [entry, ofSwapColumns_left, ofSwapColumns_right,
      ofSwapColumns_bottom, ofSwapColumns_top, hpA, hpP] using
      seamSecondShort_bottom_empty x z r.left r.right r.top ht hfSource A P
        (fun d hd => seamSecondShort_secondColumn_mem r.left r.right hcol A hA d (Or.inl hd))
  have heExit : exit.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo_target exit).mpr
    simpa only [exit, ofSwapColumns_left, ofSwapColumns_right, hqA, hqQ] using
      seamSecondShort_bottom_empty x w r.left r.right r.top ht hfTarget Q A
        (fun d hd => seamSecondShort_secondColumn_mem r.left r.right hcol A hA d (Or.inr hd))
  exact seamShortLift_correctionOfPair (x, z) (x, w) v P Q hsw hPQ hrows entry heEntry exit heExit

set_option backward.isDefEq.respectTransparency false in
/-- A blocked wrapping top-zero rectangle has an immediate mixed correction. -/
def seamSecondFactorShortLift_top_zero (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hblocked : ¬ (seamSecondFactorRectangle x r).IsEmpty)
    (hcol : r.right < r.left) (hzero : r.top = 0) :
    SeamCorrectionPath 0 (x, z) (x, w) := by
  classical
  have hx := (seamSecondFactorRectangle_blocked_top_zero_iff x r he hcol hzero).mp hblocked
  have hx0 : x (Fin.last n) ≠ 0 := by
    intro hh; rw [hh] at hx; exact (lt_irrefl 0) hx
  let a := x.toPerm.symm 0
  let A := seamLeft n m a
  let P := seamRight n m r.right
  let Q := seamRight n m r.left
  let v := (seamState x w).swapColumns A P
  have ha : a.val < n := seamSecondShort_inverse_lt x 0 hx0
  have halast : a ≠ Fin.last n := by intro hh; rw [hh] at ha; exact (lt_irrefl n) ha
  have hA : A.val < n := ha
  have hP : n ≤ P.val := by change n ≤ n + r.right.val; omega
  have hQ : n ≤ Q.val := by change n ≤ n + r.left.val; omega
  have hPQ : P < Q := Nat.add_lt_add_left hcol n
  have hAP : A ≠ P := by intro hh; have := congrArg Fin.val hh; omega
  have hAQ : A ≠ Q := by intro hh; have := congrArg Fin.val hh; omega
  have hb : r.bottom ≠ 0 := fun hh => r.bottom_ne_top (hh.trans hzero.symm)
  have hbv : n < (seamRight n m r.bottom).val := by
    have hh : r.bottom.val ≠ 0 := fun h => hb (Fin.ext h)
    simp only [seamRight_val]
    omega
  have hpA : seamState x z A = seamLeft n m 0 := by
    rw [seamShortLift_seamState_left_ne_last x z a halast]
    exact congrArg (seamLeft n m) (x.toPerm.apply_symm_apply 0)
  have hqA : seamState x w A = seamLeft n m 0 := by
    rw [seamShortLift_seamState_left_ne_last x w a halast]
    exact congrArg (seamLeft n m) (x.toPerm.apply_symm_apply 0)
  have hpQ : seamState x z Q = seamRight n m r.bottom :=
    seamState_right_of_ne_zero x z r.left hb
  have hqP : seamState x w P = seamRight n m r.bottom := by
    rw [seamState_secondFactorRow, r.map_right, ← bottom_def,
      seamSecondFactorRow_of_ne_zero x _ hb]
  have hqQ : seamState x w Q = seamLeft n m (x (Fin.last n)) :=
    seamState_right_of_zero x w r.left (r.map_left.trans hzero)
  have hvP : v P = seamLeft n m 0 := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_right, hqA]
  have hvQ : v Q = seamLeft n m (x (Fin.last n)) := by
    rw [GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hAQ.symm hPQ.ne.symm, hqQ]
  have hsw : seamSouthwestColumns v = {P, Q} := by
    let s := ofSwapColumns (seamState x w) v A P hAP rfl
    have hh := seamRectangle_birth_southwest_insert_right s
      (by simpa only [s, ofSwapColumns_left] using hA)
      (by simpa only [s, ofSwapColumns_right] using hP)
      (by simp only [s, ofSwapColumns_bottom, hqA, seamLeft_val, Fin.val_zero]; omega)
      (by simpa only [s, ofSwapColumns_top, hqP] using hbv)
    simpa only [s, ofSwapColumns_right, seamState_southwest_singleton,
      seamSecondShort_inverse_zero_of_top r hzero] using hh
  have hrows : (v P).val < (v Q).val := by
    rw [hvP, hvQ, seamLeft_val, seamLeft_val]
    exact hx
  have hswap : seamState x w = (seamState x z).swapColumns Q P :=
    (seamSecondFactorRectangle x r).target_eq_swapColumns
  have hentry : v.swapColumns P Q = (seamState x z).swapColumns Q A := by
    change ((seamState x w).swapColumns A P).swapColumns P Q = _
    rw [hswap, seamSecondShort_swap_top _ A P Q hAP hAQ hPQ.ne]
  have hexit : seamState x w = v.swapColumns A P :=
    (GridState.swapColumns_swapColumns A P (seamState x w)).symm
  let entry := ofSwapColumns (seamState x z) (v.swapColumns P Q) Q A hAQ.symm hentry
  let exit := ofSwapColumns v (seamState x w) A P hAP hexit
  have hfSource : ∀ d ∈ Grid.cIoo r.left r.right, z d ∉ Grid.cIoo r.bottom 0 := by
    simpa only [hzero] using (isEmpty_iff_forall_notMem_cIoo r).mp he
  have hfTarget : ∀ d ∈ Grid.cIoo r.left r.right, w d ∉ Grid.cIoo r.bottom 0 := by
    simpa only [hzero] using seamShortLift_target_empty r he
  have heEntry : entry.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo entry).mpr
    simpa only [entry, ofSwapColumns_left, ofSwapColumns_right,
      ofSwapColumns_bottom, ofSwapColumns_top, hpA, hpQ] using
      seamSecondShort_top_empty x z r.left r.right r.bottom hb hfSource Q A
        (fun d hd => seamSecondShort_secondColumn_mem r.left r.right hcol A hA d (Or.inr hd))
  have heExit : exit.IsEmpty := by
    apply (isEmpty_iff_forall_notMem_cIoo_target exit).mpr
    simpa only [exit, ofSwapColumns_left, ofSwapColumns_right, hqA, hqP] using
      seamSecondShort_top_empty x w r.left r.right r.bottom hb hfTarget A P
        (fun d hd => seamSecondShort_secondColumn_mem r.left r.right hcol A hA d (Or.inl hd))
  exact seamShortLift_correctionOfPair (x, z) (x, w) v P Q hsw hPQ hrows entry heEntry exit heExit

/-- An obstructed empty wrapping rectangle with a zero row endpoint has a short correction. -/
def seamSecondFactorShortLift (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hblocked : ¬ (seamSecondFactorRectangle x r).IsEmpty) (hcol : r.right < r.left)
    (hzero : r.bottom = 0 ∨ r.top = 0) : SeamCorrectionPath 0 (x, z) (x, w) := by
  classical
  by_cases hb : r.bottom = 0
  · exact seamSecondFactorShortLift_bottom_zero x r he hblocked hcol hb
  · exact seamSecondFactorShortLift_top_zero x r he hblocked hcol (hzero.resolve_left hb)

/-- The bottom-zero correction's matching source is the specified swap of the retained target. -/
theorem seamSecondFactorShortLift_bottom_zero_node (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hblocked : ¬ (seamSecondFactorRectangle x r).IsEmpty)
    (hcol : r.right < r.left) (hzero : r.bottom = 0) :
    (seamSecondFactorShortLift_bottom_zero x r he hblocked hcol hzero).1.val.val =
      (seamState x w).swapColumns (seamLeft n m (x.toPerm.symm (Fin.last n)))
        (seamRight n m r.left) := rfl

/-- The top-zero correction's matching source is the specified swap of the retained target. -/
theorem seamSecondFactorShortLift_top_zero_node (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hblocked : ¬ (seamSecondFactorRectangle x r).IsEmpty)
    (hcol : r.right < r.left) (hzero : r.top = 0) :
    (seamSecondFactorShortLift_top_zero x r he hblocked hcol hzero).1.val.val =
      (seamState x w).swapColumns (seamLeft n m (x.toPerm.symm 0))
        (seamRight n m r.right) := rfl

/-- Exact endpoints of the bottom-zero entry and exit. -/
theorem seamSecondFactorShortLift_bottom_zero_sides (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hblocked : ¬ (seamSecondFactorRectangle x r).IsEmpty)
    (hcol : r.right < r.left) (hzero : r.bottom = 0) :
    let p := seamSecondFactorShortLift_bottom_zero x r he hblocked hcol hzero
    p.2.1 = p.1 ∧
      p.2.2.1.val.left = seamLeft n m (x.toPerm.symm (Fin.last n)) ∧
      p.2.2.1.val.right = seamRight n m r.right ∧
      p.2.2.2.2.val.left = seamRight n m r.left ∧
      p.2.2.2.2.val.right = seamLeft n m (x.toPerm.symm (Fin.last n)) := by
  simp only [seamSecondFactorShortLift_bottom_zero, seamShortLift_correctionOfPair,
    ofSwapColumns_left, ofSwapColumns_right, and_self]

/-- Exact endpoints of the top-zero entry and exit. -/
theorem seamSecondFactorShortLift_top_zero_sides (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hblocked : ¬ (seamSecondFactorRectangle x r).IsEmpty)
    (hcol : r.right < r.left) (hzero : r.top = 0) :
    let p := seamSecondFactorShortLift_top_zero x r he hblocked hcol hzero
    p.2.1 = p.1 ∧
      p.2.2.1.val.left = seamRight n m r.left ∧
      p.2.2.1.val.right = seamLeft n m (x.toPerm.symm 0) ∧
      p.2.2.2.2.val.left = seamLeft n m (x.toPerm.symm 0) ∧
      p.2.2.2.2.val.right = seamRight n m r.right := by
  simp only [seamSecondFactorShortLift_top_zero, seamShortLift_correctionOfPair,
    ofSwapColumns_left, ofSwapColumns_right, and_self]

/-- Bottom zero gives the entry-left/exit-right mixed orientation. -/
theorem seamSecondFactorShortLift_bottom_zero_small_sides (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hblocked : ¬ (seamSecondFactorRectangle x r).IsEmpty)
    (hcol : r.right < r.left) (hzero : r.bottom = 0) :
    let p := seamSecondFactorShortLift_bottom_zero x r he hblocked hcol hzero
    p.2.2.1.val.left.val < n ∧ p.2.2.2.2.val.right.val < n := by
  have hs := seamSecondFactorShortLift_bottom_zero_sides x r he hblocked hcol hzero
  dsimp only
  rw [hs.2.1, hs.2.2.2.2, seamLeft_val]
  have hx := (seamSecondFactorRectangle_blocked_bottom_zero_iff x r he hcol hzero).mp hblocked
  have hn : x (Fin.last n) ≠ Fin.last n := by
    intro hh; rw [hh] at hx; exact (lt_irrefl n) hx
  have hh := seamSecondShort_inverse_lt x (Fin.last n) hn
  exact ⟨hh, hh⟩

/-- Top zero gives the entry-right/exit-left mixed orientation. -/
theorem seamSecondFactorShortLift_top_zero_small_sides (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hblocked : ¬ (seamSecondFactorRectangle x r).IsEmpty)
    (hcol : r.right < r.left) (hzero : r.top = 0) :
    let p := seamSecondFactorShortLift_top_zero x r he hblocked hcol hzero
    p.2.2.1.val.right.val < n ∧ p.2.2.2.2.val.left.val < n := by
  have hs := seamSecondFactorShortLift_top_zero_sides x r he hblocked hcol hzero
  dsimp only
  rw [hs.2.2.1, hs.2.2.2.1, seamLeft_val]
  have hx := (seamSecondFactorRectangle_blocked_top_zero_iff x r he hcol hzero).mp hblocked
  have hn : x (Fin.last n) ≠ 0 := by
    intro hh; rw [hh] at hx; exact (lt_irrefl 0) hx
  have hh := seamSecondShort_inverse_lt x 0 hn
  exact ⟨hh, hh⟩

/-- Recovering a second-factor index is independent of the proof of its lower bound. -/
theorem seamSecondShort_index_eq (c : Fin (n + m + 1)) (d : Fin (m + 1))
    (h : c = seamRight n m d) (hc : n ≤ c.val) : seamSecondFactorIndex c hc = d := by
  subst c
  exact seamSecondFactorIndex_right d

/-- Both second-factor endpoints are recovered from the bottom-zero correction. -/
theorem seamSecondFactorShortLift_bottom_zero_indices (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hblocked : ¬ (seamSecondFactorRectangle x r).IsEmpty)
    (hcol : r.right < r.left) (hzero : r.bottom = 0) :
    let p := seamSecondFactorShortLift_bottom_zero x r he hblocked hcol hzero
    ∀ hE : n ≤ p.2.2.1.val.right.val, ∀ hF : n ≤ p.2.2.2.2.val.left.val,
      seamSecondFactorIndex p.2.2.1.val.right hE = r.right ∧
        seamSecondFactorIndex p.2.2.2.2.val.left hF = r.left := by
  intro p hE hF
  have hs := seamSecondFactorShortLift_bottom_zero_sides x r he hblocked hcol hzero
  exact ⟨seamSecondShort_index_eq _ _ hs.2.2.1 hE,
    seamSecondShort_index_eq _ _ hs.2.2.2.1 hF⟩

/-- Both second-factor endpoints are recovered from the top-zero correction. -/
theorem seamSecondFactorShortLift_top_zero_indices (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hblocked : ¬ (seamSecondFactorRectangle x r).IsEmpty)
    (hcol : r.right < r.left) (hzero : r.top = 0) :
    let p := seamSecondFactorShortLift_top_zero x r he hblocked hcol hzero
    ∀ hE : n ≤ p.2.2.1.val.left.val, ∀ hF : n ≤ p.2.2.2.2.val.right.val,
      seamSecondFactorIndex p.2.2.1.val.left hE = r.left ∧
        seamSecondFactorIndex p.2.2.2.2.val.right hF = r.right := by
  intro p hE hF
  have hs := seamSecondFactorShortLift_top_zero_sides x r he hblocked hcol hzero
  exact ⟨seamSecondShort_index_eq _ _ hs.2.1 hE,
    seamSecondShort_index_eq _ _ hs.2.2.2.2 hF⟩

end OnLeConjecture.KnotFloer.GridFull

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFlatTwoStepBarrier
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamThreeStepSectors

/-! # Exclusion of completely flat correction paths

A correction path is completely flat when every matching source on it has
exactly one northeast column. The fixed northeast point `(A, x A)` survives every
flat transition. After two flat transitions, the current matching source
satisfies one of four invariants, according to the types of the last two
transitions. Each invariant records two previously exchanged columns and the
emptiness of the last two rectangles, rewritten in current coordinates. Every
further flat transition preserves one of the four invariants, and each
invariant places a state point in both possible exit rectangles.

This is Theorem J05:thm:flat of the written proof. Corollary J05:cor:three
(M603) and the cases `n ≤ 1` and `m ≤ 1` of Corollary J05:cor:thin follow.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

section FlatPathNumeric

variable {N : ℕ}

/-- Order data of a matching source with southwest columns `P < Q` and
northeast column `A`. -/
def FlatPathBase (n : ℕ) (x : Fin N → Fin N) (P Q A : Fin N) : Prop :=
  A.val < n ∧ n ≤ P.val ∧ P.val < Q.val ∧ (x P).val < (x Q).val ∧ (x Q).val ≤ n ∧
    n < (x A).val

/-- The invariant after a `lowSecond` transition at `R` preceded by a
`lowFirst` transition at `L`. -/
def FlatPathLowMinus (n : ℕ) (x : Fin N → Fin N) (P Q A L R : Fin N) : Prop :=
  R.val < A.val ∧ A.val < L.val ∧ L.val < n ∧ (x L).val < (x P).val ∧
    (x Q).val < (x R).val ∧ (x R).val ≤ n ∧
    flatEmpty x L P (x R) (x L) ∧ flatEmpty x Q R (x R) (x P)

/-- The invariant after a `lowFirst` transition at `L` preceded by a
`lowSecond` transition at `R`. -/
def FlatPathLowPlus (n : ℕ) (x : Fin N → Fin N) (P Q A L R : Fin N) : Prop :=
  R.val < A.val ∧ A.val < L.val ∧ L.val < n ∧ (x L).val < (x P).val ∧
    (x Q).val < (x R).val ∧ (x R).val ≤ n ∧
    flatEmpty x L P (x Q) (x L) ∧ flatEmpty x Q R (x R) (x L)

/-- The invariant after a `highSecond` transition leaving the column `W`,
preceded by a `highFirst` transition leaving the column `Y`. -/
def FlatPathHighMinus (n : ℕ) (x : Fin N → Fin N) (P Q A Y W : Fin N) : Prop :=
  n ≤ Y.val ∧ Y.val < P.val ∧ Q.val < W.val ∧ (x A).val < (x Y).val ∧
    n < (x W).val ∧ (x W).val < (x A).val ∧
    flatEmpty x W P (x Q) (x W) ∧ flatEmpty x W Y (x Y) (x P)

/-- The invariant after a `highFirst` transition leaving the column `Y`,
preceded by a `highSecond` transition leaving the column `W`. -/
def FlatPathHighPlus (n : ℕ) (x : Fin N → Fin N) (P Q A Y W : Fin N) : Prop :=
  n ≤ Y.val ∧ Y.val < P.val ∧ Q.val < W.val ∧ (x A).val < (x Y).val ∧
    n < (x W).val ∧ (x W).val < (x A).val ∧
    flatEmpty x Q Y (x Y) (x P) ∧ flatEmpty x W Y (x Q) (x W)

/-- The relaxation of `FlatPathLowMinus` in which `L` may be the northeast column. -/
def FlatPathLowMinusWeak (n : ℕ) (x : Fin N → Fin N) (P Q A L R : Fin N) : Prop :=
  R.val < A.val ∧ L.val < n ∧ (x Q).val < (x R).val ∧ (x R).val ≤ n ∧
    (L = A ∨ (A.val < L.val ∧ (x L).val < (x P).val)) ∧
    flatEmpty x L P (x R) (x L) ∧ flatEmpty x Q R (x R) (x P)

/-- The relaxation of `FlatPathLowPlus` in which `R` may be the northeast column. -/
def FlatPathLowPlusWeak (n : ℕ) (x : Fin N → Fin N) (P Q A L R : Fin N) : Prop :=
  A.val < L.val ∧ L.val < n ∧ (x L).val < (x P).val ∧
    (R = A ∨ (R.val < A.val ∧ (x Q).val < (x R).val ∧ (x R).val ≤ n)) ∧
    flatEmpty x L P (x Q) (x L) ∧ flatEmpty x Q R (x R) (x L)

/-- The relaxation of `FlatPathHighMinus` in which `Y` may be the northeast column. -/
def FlatPathHighMinusWeak (n : ℕ) (x : Fin N → Fin N) (P Q A Y W : Fin N) : Prop :=
  Q.val < W.val ∧ n < (x W).val ∧ (x W).val < (x A).val ∧
    (Y = A ∨ (n ≤ Y.val ∧ Y.val < P.val ∧ (x A).val < (x Y).val)) ∧
    flatEmpty x W P (x Q) (x W) ∧ flatEmpty x W Y (x Y) (x P)

/-- The relaxation of `FlatPathHighPlus` in which `W` may be the northeast column. -/
def FlatPathHighPlusWeak (n : ℕ) (x : Fin N → Fin N) (P Q A Y W : Fin N) : Prop :=
  n ≤ Y.val ∧ Y.val < P.val ∧ (x A).val < (x Y).val ∧
    (W = A ∨ (Q.val < W.val ∧ n < (x W).val ∧ (x W).val < (x A).val)) ∧
    flatEmpty x Q Y (x Y) (x P) ∧ flatEmpty x W Y (x Q) (x W)

/-- One of the four invariants holds for some pair of exchanged columns. -/
def FlatPathInv (n : ℕ) (x : Fin N → Fin N) (P Q A : Fin N) : Prop :=
  ∃ U V : Fin N, FlatPathLowMinus n x P Q A U V ∨ FlatPathLowPlus n x P Q A U V ∨
    FlatPathHighMinus n x P Q A U V ∨ FlatPathHighPlus n x P Q A U V

/-- One of the four relaxed invariants holds for some pair of columns. -/
def FlatPathInvWeak (n : ℕ) (x : Fin N → Fin N) (P Q A : Fin N) : Prop :=
  ∃ U V : Fin N, FlatPathLowMinusWeak n x P Q A U V ∨ FlatPathLowPlusWeak n x P Q A U V ∨
    FlatPathHighMinusWeak n x P Q A U V ∨ FlatPathHighPlusWeak n x P Q A U V

theorem FlatPathInv.weak {n : ℕ} {x : Fin N → Fin N} {P Q A : Fin N}
    (h : FlatPathInv n x P Q A) : FlatPathInvWeak n x P Q A := by
  obtain ⟨U, V, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ |
    ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩ := h
  · exact ⟨U, V, Or.inl ⟨h1, h3, h5, h6, Or.inr ⟨h2, h4⟩, h7, h8⟩⟩
  · exact ⟨U, V, Or.inr (Or.inl ⟨h2, h3, h4, Or.inr ⟨h1, h5, h6⟩, h7, h8⟩)⟩
  · exact ⟨U, V, Or.inr (Or.inr (Or.inl ⟨h3, h5, h6, Or.inr ⟨h1, h2, h4⟩, h7, h8⟩))⟩
  · exact ⟨U, V, Or.inr (Or.inr (Or.inr ⟨h1, h2, h4, Or.inr ⟨h3, h5, h6⟩, h7, h8⟩))⟩

theorem flatPath_cong (x : Fin N → Fin N) (a b : Fin N) :
    a.val = b.val → (x a).val = (x b).val := fun h => by rw [Fin.ext h]

theorem flatPath_inj {x : Fin N → Fin N} (hx : Function.Injective x) (a b : Fin N) :
    (x a).val = (x b).val → a.val = b.val := fun h => congrArg Fin.val (hx (Fin.ext h))

theorem flatPath_test {x : Fin N → Fin N} {l r b t : Fin N} (h : flatEmpty x l r b t)
    (c : Fin N) (h1 : flatInside l r c) (h2 : flatInside b t (x c)) : False :=
  h c ⟨h1, h2⟩

theorem flatPath_transfer {x y : Fin N → Fin N} {l r b t : Fin N} (h : flatEmpty x l r b t)
    (hxy : ∀ c, flatInside l r c → y c = x c) : flatEmpty y l r b t := fun c hc =>
  h c ⟨hc.1, hxy c hc.1 ▸ hc.2⟩

theorem flatPathApply_of_ne (i : FlatKind) (x : Fin N → Fin N) {P Q C c : Fin N}
    (hP : c.val ≠ P.val) (hQ : c.val ≠ Q.val) (hC : c.val ≠ C.val) :
    flatApply i x P Q C c = x c := by
  have hP' : c ≠ P := fun h => hP (congrArg Fin.val h)
  have hQ' : c ≠ Q := fun h => hQ (congrArg Fin.val h)
  have hC' : c ≠ C := fun h => hC (congrArg Fin.val h)
  cases i <;> simp only [flatApply, if_neg hP', if_neg hQ', if_neg hC']

theorem flatPathApply_lowFirst (x : Fin N → Fin N) {P Q C : Fin N} (hPQ : P.val ≠ Q.val)
    (hPC : P.val ≠ C.val) (hQC : Q.val ≠ C.val) :
    flatApply .lowFirst x P Q C P = x Q ∧ flatApply .lowFirst x P Q C Q = x C ∧
      flatApply .lowFirst x P Q C C = x P := by
  have h1 : Q ≠ P := fun h => hPQ (congrArg Fin.val h).symm
  have h2 : C ≠ P := fun h => hPC (congrArg Fin.val h).symm
  have h3 : C ≠ Q := fun h => hQC (congrArg Fin.val h).symm
  simp [flatApply, h1, h2, h3]

theorem flatPathApply_highSecond (x : Fin N → Fin N) {P Q C : Fin N} (hPQ : P.val ≠ Q.val)
    (hPC : P.val ≠ C.val) (hQC : Q.val ≠ C.val) :
    flatApply .highSecond x P Q C P = x Q ∧ flatApply .highSecond x P Q C Q = x C ∧
      flatApply .highSecond x P Q C C = x P := by
  have h1 : Q ≠ P := fun h => hPQ (congrArg Fin.val h).symm
  have h2 : C ≠ P := fun h => hPC (congrArg Fin.val h).symm
  have h3 : C ≠ Q := fun h => hQC (congrArg Fin.val h).symm
  simp [flatApply, h1, h2, h3]

theorem flatPathApply_lowSecond (x : Fin N → Fin N) {P Q C : Fin N} (hPQ : P.val ≠ Q.val)
    (hPC : P.val ≠ C.val) (hQC : Q.val ≠ C.val) :
    flatApply .lowSecond x P Q C P = x C ∧ flatApply .lowSecond x P Q C Q = x P ∧
      flatApply .lowSecond x P Q C C = x Q := by
  have h1 : Q ≠ P := fun h => hPQ (congrArg Fin.val h).symm
  have h2 : C ≠ P := fun h => hPC (congrArg Fin.val h).symm
  have h3 : C ≠ Q := fun h => hQC (congrArg Fin.val h).symm
  simp [flatApply, h1, h2, h3]

theorem flatPathApply_highFirst (x : Fin N → Fin N) {P Q C : Fin N} (hPQ : P.val ≠ Q.val)
    (hPC : P.val ≠ C.val) (hQC : Q.val ≠ C.val) :
    flatApply .highFirst x P Q C P = x C ∧ flatApply .highFirst x P Q C Q = x P ∧
      flatApply .highFirst x P Q C C = x Q := by
  have h1 : Q ≠ P := fun h => hPQ (congrArg Fin.val h).symm
  have h2 : C ≠ P := fun h => hPC (congrArg Fin.val h).symm
  have h3 : C ≠ Q := fun h => hQC (congrArg Fin.val h).symm
  simp [flatApply, h1, h2, h3]

/-- Prove a cyclic interval membership from the linear order facts in context. -/
local macro "flat_path_inside" : tactic =>
  `(tactic| (unfold flatInside; split_ifs <;> omega))

/-- Show that a flat transition leaves every column of a cyclic interval unchanged. -/
local macro "flat_path_same" : tactic =>
  `(tactic| (intro c hc; unfold flatInside at hc; split_ifs at hc <;>
      exact flatPathApply_of_ne _ _ (by omega) (by omega) (by omega)))

theorem flatPathLowMinusWeak_step (n : ℕ) {x : Fin N → Fin N} (hx : Function.Injective x)
    {P Q A L R Z : Fin N} (i : FlatKind) (hb : FlatPathBase n x P Q A)
    (hinv : FlatPathLowMinusWeak n x P Q A L R) (hi : flatRange i n x P Q Z)
    (hr : flatEmpty x (flatLeft i P Q Z) (flatRight i P Q Z)
      (x (flatLeft i P Q Z)) (x (flatRight i P Q Z))) :
    FlatPathInv n (flatApply i x P Q Z) (flatFirst i P Q Z) (flatSecond i P Q Z) A := by
  obtain ⟨hA, hP, hPQ, hpq, hQ, hAH⟩ := hb
  obtain ⟨hRA, hLn, hQR, hRn, hL, h3, h4⟩ := hinv
  have hL' : L.val = A.val ∨ (A.val < L.val ∧ (x L).val < (x P).val) :=
    hL.imp (fun h => by rw [h]) id
  have hLA := flatPath_cong x L A
  clear hL
  cases i with
  | lowFirst =>
    simp only [flatRange, flatLeft, flatRight] at hi hr
    obtain ⟨hZn, hZle, hZq⟩ := hi
    have hZA := flatPath_cong x Z A
    have hZL := flatPath_cong x Z L
    have hZR := flatPath_inj hx Z R
    have hAZ : A.val < Z.val := by
      by_contra hc
      exact flatPath_test hr A (by flat_path_inside) (by flat_path_inside)
    have hLZ : L.val < Z.val := by
      by_contra hc
      exact flatPath_test hr L (by flat_path_inside) (by flat_path_inside)
    have hZR' : (x Z).val < (x R).val := by
      by_contra hc
      exact flatPath_test h3 Z (by flat_path_inside) (by flat_path_inside)
    change FlatPathInv n (flatApply .lowFirst x P Q Z) P Q A
    obtain ⟨hyP, hyQ, hyZ⟩ :=
      flatPathApply_lowFirst x (P := P) (Q := Q) (C := Z) (by omega) (by omega) (by omega)
    have hyR : flatApply .lowFirst x P Q Z R = x R :=
      flatPathApply_of_ne _ _ (by omega) (by omega) (by omega)
    refine ⟨Z, R, Or.inr (Or.inl ⟨hRA, hAZ, hZn, ?_, ?_, ?_, ?_, ?_⟩)⟩
    · rw [hyZ, hyP]; exact hpq
    · rw [hyQ, hyR]; exact hZR'
    · rw [hyR]; exact hRn
    · rw [hyQ, hyZ]; exact flatPath_transfer hr (by flat_path_same)
    · rw [hyR, hyZ]; exact flatPath_transfer h4 (by flat_path_same)
  | lowSecond =>
    simp only [flatRange, flatLeft, flatRight] at hi hr
    obtain ⟨hZn, hZle, hZp⟩ := hi
    have hZA := flatPath_cong x Z A
    have hZR := flatPath_cong x Z R
    have hZA' : Z.val < A.val := by
      by_contra hc
      exact flatPath_test hr A (by flat_path_inside) (by flat_path_inside)
    have hZR' : Z.val < R.val := by
      by_contra hc
      exact flatPath_test hr R (by flat_path_inside) (by flat_path_inside)
    exact (flatPath_test h4 Z (by flat_path_inside) (by flat_path_inside)).elim
  | highFirst =>
    simp only [flatRange, flatLeft, flatRight, Fin.lt_def] at hi hr
    obtain ⟨hZn, hZh, hQZ⟩ := hi
    exact (flatPath_test h4 Z (by flat_path_inside) (by flat_path_inside)).elim
  | highSecond =>
    simp only [flatRange, flatLeft, flatRight, Fin.lt_def] at hi hr
    obtain ⟨hZn, hZh, hZP⟩ := hi
    exact (flatPath_test hr R (by flat_path_inside) (by flat_path_inside)).elim

theorem flatPathLowPlusWeak_step (n : ℕ) {x : Fin N → Fin N} (hx : Function.Injective x)
    {P Q A L R Z : Fin N} (i : FlatKind) (hb : FlatPathBase n x P Q A)
    (hinv : FlatPathLowPlusWeak n x P Q A L R) (hi : flatRange i n x P Q Z)
    (hr : flatEmpty x (flatLeft i P Q Z) (flatRight i P Q Z)
      (x (flatLeft i P Q Z)) (x (flatRight i P Q Z))) :
    FlatPathInv n (flatApply i x P Q Z) (flatFirst i P Q Z) (flatSecond i P Q Z) A := by
  obtain ⟨hA, hP, hPQ, hpq, hQ, hAH⟩ := hb
  obtain ⟨hAL, hLn, hLp, hR, h3, h4⟩ := hinv
  have hR' : R.val = A.val ∨ (R.val < A.val ∧ (x Q).val < (x R).val ∧ (x R).val ≤ n) :=
    hR.imp (fun h => by rw [h]) id
  have hRA := flatPath_cong x R A
  clear hR
  cases i with
  | lowFirst =>
    simp only [flatRange, flatLeft, flatRight] at hi hr
    obtain ⟨hZn, hZle, hZq⟩ := hi
    have hZA := flatPath_cong x Z A
    have hZL := flatPath_cong x Z L
    have hAZ : A.val < Z.val := by
      by_contra hc
      exact flatPath_test hr A (by flat_path_inside) (by flat_path_inside)
    have hLZ : L.val < Z.val := by
      by_contra hc
      exact flatPath_test hr L (by flat_path_inside) (by flat_path_inside)
    exact (flatPath_test h3 Z (by flat_path_inside) (by flat_path_inside)).elim
  | lowSecond =>
    simp only [flatRange, flatLeft, flatRight] at hi hr
    obtain ⟨hZn, hZle, hZp⟩ := hi
    have hZA := flatPath_cong x Z A
    have hZR := flatPath_cong x Z R
    have hZL := flatPath_inj hx Z L
    have hZA' : Z.val < A.val := by
      by_contra hc
      exact flatPath_test hr A (by flat_path_inside) (by flat_path_inside)
    have hZR' : Z.val < R.val := by
      by_contra hc
      exact flatPath_test hr R (by flat_path_inside) (by flat_path_inside)
    have hLZ : (x L).val < (x Z).val := by
      by_contra hc
      exact flatPath_test h4 Z (by flat_path_inside) (by flat_path_inside)
    change FlatPathInv n (flatApply .lowSecond x P Q Z) P Q A
    obtain ⟨hyP, hyQ, hyZ⟩ :=
      flatPathApply_lowSecond x (P := P) (Q := Q) (C := Z) (by omega) (by omega) (by omega)
    have hyL : flatApply .lowSecond x P Q Z L = x L :=
      flatPathApply_of_ne _ _ (by omega) (by omega) (by omega)
    refine ⟨L, Z, Or.inl ⟨hZA', hAL, hLn, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hyL, hyP]; exact hLZ
    · rw [hyQ, hyZ]; exact hpq
    · rw [hyZ]; exact hQ
    · rw [hyZ, hyL]; exact flatPath_transfer h3 (by flat_path_same)
    · rw [hyZ, hyP]; exact flatPath_transfer hr (by flat_path_same)
  | highFirst =>
    simp only [flatRange, flatLeft, flatRight, Fin.lt_def] at hi hr
    obtain ⟨hZn, hZh, hQZ⟩ := hi
    have hZA := flatPath_inj hx Z A
    have hAZ : (x A).val < (x Z).val := by
      by_contra hc
      exact flatPath_test hr A (by flat_path_inside) (by flat_path_inside)
    exact (flatPath_test h4 Z (by flat_path_inside) (by flat_path_inside)).elim
  | highSecond =>
    simp only [flatRange, flatLeft, flatRight, Fin.lt_def] at hi hr
    obtain ⟨hZn, hZh, hZP⟩ := hi
    exact (flatPath_test h3 Z (by flat_path_inside) (by flat_path_inside)).elim

theorem flatPathHighMinusWeak_step (n : ℕ) {x : Fin N → Fin N} (hx : Function.Injective x)
    {P Q A Y W Z : Fin N} (i : FlatKind) (hb : FlatPathBase n x P Q A)
    (hinv : FlatPathHighMinusWeak n x P Q A Y W) (hi : flatRange i n x P Q Z)
    (hr : flatEmpty x (flatLeft i P Q Z) (flatRight i P Q Z)
      (x (flatLeft i P Q Z)) (x (flatRight i P Q Z))) :
    FlatPathInv n (flatApply i x P Q Z) (flatFirst i P Q Z) (flatSecond i P Q Z) A := by
  obtain ⟨hA, hP, hPQ, hpq, hQ, hAH⟩ := hb
  obtain ⟨hQW, hWn, hWA, hY, h3, h4⟩ := hinv
  have hY' : Y.val = A.val ∨ (n ≤ Y.val ∧ Y.val < P.val ∧ (x A).val < (x Y).val) :=
    hY.imp (fun h => by rw [h]) id
  have hYA := flatPath_cong x Y A
  clear hY
  cases i with
  | lowFirst =>
    simp only [flatRange, flatLeft, flatRight] at hi hr
    obtain ⟨hZn, hZle, hZq⟩ := hi
    exact (flatPath_test h3 Z (by flat_path_inside) (by flat_path_inside)).elim
  | lowSecond =>
    simp only [flatRange, flatLeft, flatRight] at hi hr
    obtain ⟨hZn, hZle, hZp⟩ := hi
    exact (flatPath_test hr W (by flat_path_inside) (by flat_path_inside)).elim
  | highSecond =>
    simp only [flatRange, flatLeft, flatRight, Fin.lt_def] at hi hr
    obtain ⟨hZn, hZh, hZP⟩ := hi
    have hZW := flatPath_inj hx Z W
    have h1 : (x Z).val ≤ (x W).val := by
      by_contra hc
      exact flatPath_test hr W (by flat_path_inside) (by flat_path_inside)
    have h2 : (x W).val ≤ (x Z).val := by
      by_contra hc
      exact flatPath_test h3 Z (by flat_path_inside) (by flat_path_inside)
    omega
  | highFirst =>
    simp only [flatRange, flatLeft, flatRight, Fin.lt_def] at hi hr
    obtain ⟨hZn, hZh, hQZ⟩ := hi
    have hZA := flatPath_inj hx Z A
    have hZY := flatPath_inj hx Z Y
    have hZW := flatPath_cong x Z W
    have hAZ : (x A).val < (x Z).val := by
      by_contra hc
      exact flatPath_test hr A (by flat_path_inside) (by flat_path_inside)
    have hYZ : (x Y).val < (x Z).val := by
      by_contra hc
      exact flatPath_test hr Y (by flat_path_inside) (by flat_path_inside)
    have hZW' : Z.val < W.val := by
      by_contra hc
      exact flatPath_test h4 Z (by flat_path_inside) (by flat_path_inside)
    change FlatPathInv n (flatApply .highFirst x P Q Z) Q Z A
    obtain ⟨hyP, hyQ, hyZ⟩ :=
      flatPathApply_highFirst x (P := P) (Q := Q) (C := Z) (by omega) (by omega) (by omega)
    have hyW : flatApply .highFirst x P Q Z W = x W :=
      flatPathApply_of_ne _ _ (by omega) (by omega) (by omega)
    have hyA : flatApply .highFirst x P Q Z A = x A :=
      flatPathApply_of_ne _ _ (by omega) (by omega) (by omega)
    refine ⟨P, W, Or.inr (Or.inr (Or.inr ⟨hP, hPQ, hZW', ?_, ?_, ?_, ?_, ?_⟩))⟩
    · rw [hyA, hyP]; exact hAZ
    · rw [hyW]; exact hWn
    · rw [hyW, hyA]; exact hWA
    · rw [hyP, hyQ]; exact flatPath_transfer hr (by flat_path_same)
    · rw [hyZ, hyW]; exact flatPath_transfer h3 (by flat_path_same)

theorem flatPathHighPlusWeak_step (n : ℕ) {x : Fin N → Fin N} (hx : Function.Injective x)
    {P Q A Y W Z : Fin N} (i : FlatKind) (hb : FlatPathBase n x P Q A)
    (hinv : FlatPathHighPlusWeak n x P Q A Y W) (hi : flatRange i n x P Q Z)
    (hr : flatEmpty x (flatLeft i P Q Z) (flatRight i P Q Z)
      (x (flatLeft i P Q Z)) (x (flatRight i P Q Z))) :
    FlatPathInv n (flatApply i x P Q Z) (flatFirst i P Q Z) (flatSecond i P Q Z) A := by
  obtain ⟨hA, hP, hPQ, hpq, hQ, hAH⟩ := hb
  obtain ⟨hYn, hYP, hAY, hW, h3, h4⟩ := hinv
  have hW' : W.val = A.val ∨ (Q.val < W.val ∧ n < (x W).val ∧ (x W).val < (x A).val) :=
    hW.imp (fun h => by rw [h]) id
  have hWA := flatPath_cong x W A
  clear hW
  cases i with
  | lowFirst =>
    simp only [flatRange, flatLeft, flatRight] at hi hr
    obtain ⟨hZn, hZle, hZq⟩ := hi
    exact (flatPath_test hr Y (by flat_path_inside) (by flat_path_inside)).elim
  | lowSecond =>
    simp only [flatRange, flatLeft, flatRight] at hi hr
    obtain ⟨hZn, hZle, hZp⟩ := hi
    exact (flatPath_test h3 Z (by flat_path_inside) (by flat_path_inside)).elim
  | highFirst =>
    simp only [flatRange, flatLeft, flatRight, Fin.lt_def] at hi hr
    obtain ⟨hZn, hZh, hQZ⟩ := hi
    have hZY := flatPath_inj hx Z Y
    have h1 : (x Z).val ≤ (x Y).val := by
      by_contra hc
      exact flatPath_test h3 Z (by flat_path_inside) (by flat_path_inside)
    have h2 : (x Y).val ≤ (x Z).val := by
      by_contra hc
      exact flatPath_test hr Y (by flat_path_inside) (by flat_path_inside)
    omega
  | highSecond =>
    simp only [flatRange, flatLeft, flatRight, Fin.lt_def] at hi hr
    obtain ⟨hZn, hZh, hZP⟩ := hi
    have hZA := flatPath_inj hx Z A
    have hZW := flatPath_inj hx Z W
    have hZY := flatPath_cong x Z Y
    have hZA' : (x Z).val < (x A).val := by
      by_contra hc
      exact flatPath_test hr A (by flat_path_inside) (by flat_path_inside)
    have hZW' : (x Z).val < (x W).val := by
      by_contra hc
      exact flatPath_test hr W (by flat_path_inside) (by flat_path_inside)
    have hYZ : Y.val < Z.val := by
      by_contra hc
      exact flatPath_test h4 Z (by flat_path_inside) (by flat_path_inside)
    change FlatPathInv n (flatApply .highSecond x P Q Z) Z P A
    obtain ⟨hyP, hyQ, hyZ⟩ :=
      flatPathApply_highSecond x (P := P) (Q := Q) (C := Z) (by omega) (by omega) (by omega)
    have hyY : flatApply .highSecond x P Q Z Y = x Y :=
      flatPathApply_of_ne _ _ (by omega) (by omega) (by omega)
    have hyA : flatApply .highSecond x P Q Z A = x A :=
      flatPathApply_of_ne _ _ (by omega) (by omega) (by omega)
    refine ⟨Y, Q, Or.inr (Or.inr (Or.inl ⟨hYn, hYZ, hPQ, ?_, ?_, ?_, ?_, ?_⟩))⟩
    · rw [hyA, hyY]; exact hAY
    · rw [hyQ]; exact hZh
    · rw [hyQ, hyA]; exact hZA'
    · rw [hyP, hyQ]; exact flatPath_transfer hr (by flat_path_same)
    · rw [hyY, hyZ]; exact flatPath_transfer h3 (by flat_path_same)

/-- A flat transition from a relaxed invariant produces one of the four invariants. -/
theorem flatPathInvWeak_step (n : ℕ) {x : Fin N → Fin N} (hx : Function.Injective x)
    {P Q A Z : Fin N} (i : FlatKind) (hb : FlatPathBase n x P Q A)
    (hinv : FlatPathInvWeak n x P Q A) (hi : flatRange i n x P Q Z)
    (hr : flatEmpty x (flatLeft i P Q Z) (flatRight i P Q Z)
      (x (flatLeft i P Q Z)) (x (flatRight i P Q Z))) :
    FlatPathInv n (flatApply i x P Q Z) (flatFirst i P Q Z) (flatSecond i P Q Z) A := by
  obtain ⟨U, V, h | h | h | h⟩ := hinv
  · exact flatPathLowMinusWeak_step n hx i hb h hi hr
  · exact flatPathLowPlusWeak_step n hx i hb h hi hr
  · exact flatPathHighMinusWeak_step n hx i hb h hi hr
  · exact flatPathHighPlusWeak_step n hx i hb h hi hr

/-- The first flat transition after an empty entry rectangle produces a relaxed invariant. -/
theorem flatPath_entry_step (n : ℕ) {x : Fin N → Fin N} (hx : Function.Injective x)
    {P Q A Z : Fin N} (i : FlatKind) (left : Bool) (hb : FlatPathBase n x P Q A)
    (he : flatEmpty x (if left then A else Q) (if left then P else A)
      (if left then x Q else x A) (if left then x A else x P))
    (hi : flatRange i n x P Q Z)
    (hr : flatEmpty x (flatLeft i P Q Z) (flatRight i P Q Z)
      (x (flatLeft i P Q Z)) (x (flatRight i P Q Z))) :
    FlatPathInvWeak n (flatApply i x P Q Z) (flatFirst i P Q Z) (flatSecond i P Q Z) A := by
  obtain ⟨hA, hP, hPQ, hpq, hQ, hAH⟩ := hb
  cases i with
  | lowFirst =>
    simp only [flatRange, flatLeft, flatRight] at hi hr
    obtain ⟨hZn, hZle, hZq⟩ := hi
    have hZA := flatPath_cong x Z A
    have hAZ : A.val < Z.val := by
      by_contra hc
      exact flatPath_test hr A (by flat_path_inside) (by flat_path_inside)
    cases left with
    | true =>
      simp only [if_true] at he
      exact (flatPath_test he Z (by flat_path_inside) (by flat_path_inside)).elim
    | false =>
      simp only [Bool.false_eq_true, if_false] at he
      change FlatPathInvWeak n (flatApply .lowFirst x P Q Z) P Q A
      obtain ⟨hyP, hyQ, hyZ⟩ :=
        flatPathApply_lowFirst x (P := P) (Q := Q) (C := Z) (by omega) (by omega) (by omega)
      have hyA : flatApply .lowFirst x P Q Z A = x A :=
        flatPathApply_of_ne _ _ (by omega) (by omega) (by omega)
      refine ⟨Z, A, Or.inr (Or.inl ⟨hAZ, hZn, ?_, Or.inl rfl, ?_, ?_⟩)⟩
      · rw [hyZ, hyP]; exact hpq
      · rw [hyQ, hyZ]; exact flatPath_transfer hr (by flat_path_same)
      · rw [hyA, hyZ]; exact flatPath_transfer he (by flat_path_same)
  | lowSecond =>
    simp only [flatRange, flatLeft, flatRight] at hi hr
    obtain ⟨hZn, hZle, hZp⟩ := hi
    have hZA := flatPath_cong x Z A
    have hZA' : Z.val < A.val := by
      by_contra hc
      exact flatPath_test hr A (by flat_path_inside) (by flat_path_inside)
    cases left with
    | true =>
      simp only [if_true] at he
      change FlatPathInvWeak n (flatApply .lowSecond x P Q Z) P Q A
      obtain ⟨hyP, hyQ, hyZ⟩ :=
        flatPathApply_lowSecond x (P := P) (Q := Q) (C := Z) (by omega) (by omega) (by omega)
      have hyA : flatApply .lowSecond x P Q Z A = x A :=
        flatPathApply_of_ne _ _ (by omega) (by omega) (by omega)
      refine ⟨A, Z, Or.inl ⟨hZA', hA, ?_, ?_, Or.inl rfl, ?_, ?_⟩⟩
      · rw [hyQ, hyZ]; exact hpq
      · rw [hyZ]; exact hQ
      · rw [hyZ, hyA]; exact flatPath_transfer he (by flat_path_same)
      · rw [hyZ, hyP]; exact flatPath_transfer hr (by flat_path_same)
    | false =>
      simp only [Bool.false_eq_true, if_false] at he
      exact (flatPath_test he Z (by flat_path_inside) (by flat_path_inside)).elim
  | highFirst =>
    simp only [flatRange, flatLeft, flatRight, Fin.lt_def] at hi hr
    obtain ⟨hZn, hZh, hQZ⟩ := hi
    have hZA := flatPath_inj hx Z A
    have hAZ : (x A).val < (x Z).val := by
      by_contra hc
      exact flatPath_test hr A (by flat_path_inside) (by flat_path_inside)
    cases left with
    | true =>
      simp only [if_true] at he
      change FlatPathInvWeak n (flatApply .highFirst x P Q Z) Q Z A
      obtain ⟨hyP, hyQ, hyZ⟩ :=
        flatPathApply_highFirst x (P := P) (Q := Q) (C := Z) (by omega) (by omega) (by omega)
      have hyA : flatApply .highFirst x P Q Z A = x A :=
        flatPathApply_of_ne _ _ (by omega) (by omega) (by omega)
      refine ⟨P, A, Or.inr (Or.inr (Or.inr ⟨hP, hPQ, ?_, Or.inl rfl, ?_, ?_⟩))⟩
      · rw [hyA, hyP]; exact hAZ
      · rw [hyP, hyQ]; exact flatPath_transfer hr (by flat_path_same)
      · rw [hyZ, hyA]; exact flatPath_transfer he (by flat_path_same)
    | false =>
      simp only [Bool.false_eq_true, if_false] at he
      exact (flatPath_test he Z (by flat_path_inside) (by flat_path_inside)).elim
  | highSecond =>
    simp only [flatRange, flatLeft, flatRight, Fin.lt_def] at hi hr
    obtain ⟨hZn, hZh, hZP⟩ := hi
    have hZA := flatPath_inj hx Z A
    have hZA' : (x Z).val < (x A).val := by
      by_contra hc
      exact flatPath_test hr A (by flat_path_inside) (by flat_path_inside)
    cases left with
    | true =>
      simp only [if_true] at he
      exact (flatPath_test he Z (by flat_path_inside) (by flat_path_inside)).elim
    | false =>
      simp only [Bool.false_eq_true, if_false] at he
      change FlatPathInvWeak n (flatApply .highSecond x P Q Z) Z P A
      obtain ⟨hyP, hyQ, hyZ⟩ :=
        flatPathApply_highSecond x (P := P) (Q := Q) (C := Z) (by omega) (by omega) (by omega)
      have hyA : flatApply .highSecond x P Q Z A = x A :=
        flatPathApply_of_ne _ _ (by omega) (by omega) (by omega)
      refine ⟨A, Q, Or.inr (Or.inr (Or.inl ⟨hPQ, ?_, ?_, Or.inl rfl, ?_, ?_⟩))⟩
      · rw [hyQ]; exact hZh
      · rw [hyQ, hyA]; exact hZA'
      · rw [hyP, hyQ]; exact flatPath_transfer hr (by flat_path_same)
      · rw [hyA, hyZ]; exact flatPath_transfer he (by flat_path_same)

/-- Each of the four invariants places a state point in both possible exit rectangles. -/
theorem flatPathInv_exit (n : ℕ) {x : Fin N → Fin N} {P Q A : Fin N}
    (hb : FlatPathBase n x P Q A) (hinv : FlatPathInv n x P Q A) (left : Bool)
    (hf : flatEmpty x (if left then A else Q) (if left then P else A)
      (if left then x A else x Q) (if left then x P else x A)) : False := by
  obtain ⟨hA, hP, hPQ, hpq, hQ, hAH⟩ := hb
  obtain ⟨U, V, ⟨h1, h2, h3, h4, h5, h6, -, -⟩ | ⟨h1, h2, h3, h4, h5, h6, -, -⟩ |
    ⟨h1, h2, h3, h4, h5, h6, -, -⟩ | ⟨h1, h2, h3, h4, h5, h6, -, -⟩⟩ := hinv <;>
    cases left <;> simp only [if_true, Bool.false_eq_true, if_false] at hf
  · exact flatPath_test hf V (by flat_path_inside) (by flat_path_inside)
  · exact flatPath_test hf U (by flat_path_inside) (by flat_path_inside)
  · exact flatPath_test hf V (by flat_path_inside) (by flat_path_inside)
  · exact flatPath_test hf U (by flat_path_inside) (by flat_path_inside)
  · exact flatPath_test hf V (by flat_path_inside) (by flat_path_inside)
  · exact flatPath_test hf U (by flat_path_inside) (by flat_path_inside)
  · exact flatPath_test hf V (by flat_path_inside) (by flat_path_inside)
  · exact flatPath_test hf U (by flat_path_inside) (by flat_path_inside)

end FlatPathNumeric

/-- Every matching source visited by the internal path, including both ends, has
northeast count one. -/
def SeamInternalPath.AllFlat :
    {k : ℕ} → {x y : SeamMatchingSource n m} → SeamInternalPath k x y → Prop
  | 0, x, _, _ => (seamNortheastColumns x.val.val).card = 1
  | _ + 1, x, _, ⟨_, _, π⟩ => (seamNortheastColumns x.val.val).card = 1 ∧ AllFlat π

theorem SeamInternalPath.allFlat_zero {x y : SeamMatchingSource n m}
    (π : SeamInternalPath 0 x y) : π.AllFlat ↔ (seamNortheastColumns x.val.val).card = 1 :=
  Iff.rfl

theorem SeamInternalPath.allFlat_succ {k : ℕ} {x y : SeamMatchingSource n m}
    (z : SeamMatchingSource n m) (r : SeamInternalRectangle x z) (π : SeamInternalPath k z y) :
    SeamInternalPath.AllFlat (k := k + 1) (y := y) ⟨z, r, π⟩ ↔
      (seamNortheastColumns x.val.val).card = 1 ∧ π.AllFlat :=
  Iff.rfl

theorem SeamInternalPath.allFlat_head {k : ℕ} {x y : SeamMatchingSource n m}
    (π : SeamInternalPath k x y) (h : π.AllFlat) : (seamNortheastColumns x.val.val).card = 1 := by
  cases k with
  | zero => exact h
  | succ k =>
    obtain ⟨z, r, π'⟩ := π
    exact h.1

theorem SeamInternalPath.allFlat_of_forall {k : ℕ} {x y : SeamMatchingSource n m}
    (π : SeamInternalPath k x y)
    (h : ∀ z : SeamMatchingSource n m, (seamNortheastColumns z.val.val).card = 1) :
    π.AllFlat := by
  induction k generalizing x with
  | zero => exact h x
  | succ k ih =>
    obtain ⟨z, r, π'⟩ := π
    exact ⟨h x, ih π'⟩

/-- The order data of a matching source whose northeast column is `A`. -/
theorem flatPathBase_source (x : SeamMatchingSource n m) (A : Fin (n + m + 1))
    (hA : A.val < n) (hAH : n < (x.val.val A).val) :
    FlatPathBase n x.val.val (seamComplementFirst x.val) (seamComplementSecond x.val) A := by
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  exact ⟨hA, hp.1, Fin.lt_def.mp (seamComplementFirst_lt_second x.val), x.property, hq.2, hAH⟩

/-- A flat internal rectangle is one of the four native flat transitions. -/
theorem flatPath_rectangle_data {x z : SeamMatchingSource n m} (r : SeamInternalRectangle x z)
    (hx : (seamNortheastColumns x.val.val).card = 1)
    (hz : (seamNortheastColumns z.val.val).card = 1) :
    ∃ i : FlatKind, ∃ C : Fin (n + m + 1),
      flatRange i n x.val.val (seamComplementFirst x.val) (seamComplementSecond x.val) C ∧
      flatEmpty x.val.val
        (flatLeft i (seamComplementFirst x.val) (seamComplementSecond x.val) C)
        (flatRight i (seamComplementFirst x.val) (seamComplementSecond x.val) C)
        (x.val.val (flatLeft i (seamComplementFirst x.val) (seamComplementSecond x.val) C))
        (x.val.val (flatRight i (seamComplementFirst x.val) (seamComplementSecond x.val) C)) ∧
      (z.val.val : Fin (n + m + 1) → Fin (n + m + 1)) =
        flatApply i x.val.val (seamComplementFirst x.val) (seamComplementSecond x.val) C ∧
      seamComplementFirst z.val =
        flatFirst i (seamComplementFirst x.val) (seamComplementSecond x.val) C ∧
      seamComplementSecond z.val =
        flatSecond i (seamComplementFirst x.val) (seamComplementSecond x.val) C := by
  have hxSW : (seamSouthwestColumns x.val.val).card = 2 := by
    rw [seamSouthwestColumns_card, hx]
  have hzSW : (seamSouthwestColumns z.val.val).card = 2 := by
    rw [seamSouthwestColumns_card, hz]
  obtain ⟨i, C, hi, hL, hR, hP, hQ⟩ :=
    flatStep_cases r.val r.property.1 r.property.2 hxSW hzSW
  refine ⟨i, C, hi, ?_, flatStep_apply r.val i C hi hL hR hP hQ, hP, hQ⟩
  simpa only [bottom_def, top_def, hL, hR] using flatEmpty_source r.val r.property.2

/-- A flat internal rectangle carries a relaxed invariant to one of the four invariants. -/
theorem flatPath_source_step {x z : SeamMatchingSource n m} (r : SeamInternalRectangle x z)
    (hx : (seamNortheastColumns x.val.val).card = 1)
    (hz : (seamNortheastColumns z.val.val).card = 1)
    (A : Fin (n + m + 1)) (hA : A.val < n) (hAH : n < (x.val.val A).val)
    (hinv : FlatPathInvWeak n x.val.val (seamComplementFirst x.val)
      (seamComplementSecond x.val) A) :
    n < (z.val.val A).val ∧
      FlatPathInv n z.val.val (seamComplementFirst z.val) (seamComplementSecond z.val) A := by
  obtain ⟨i, C, hi, hr, happ, hP, hQ⟩ := flatPath_rectangle_data r hx hz
  have hb := flatPathBase_source x A hA hAH
  have key := flatPathInvWeak_step n x.val.val.toPerm.injective i hb hinv hi hr
  refine ⟨?_, ?_⟩
  · rw [congrFun happ A, flatApply_high n x.val.val i _ _ C A hb.2.1
      (Fin.lt_def.mpr hb.2.2.1) hA hAH hi]
    exact hAH
  · rw [happ, hP, hQ]
    exact key

/-- The entry rectangle and the first flat internal rectangle give a relaxed invariant. -/
theorem flatPath_source_entry (p : SeamRetainedIndex n m) {x z : SeamMatchingSource n m}
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (he : e.IsEmpty) (r : SeamInternalRectangle x z)
    (hz : (seamNortheastColumns z.val.val).card = 1) :
    ∃ A : Fin (n + m + 1), A.val < n ∧ n < (z.val.val A).val ∧
      FlatPathInvWeak n z.val.val (seamComplementFirst z.val) (seamComplementSecond z.val) A := by
  have hx := seamMatchingEntry_northeast_card p x e
  obtain ⟨A, left, hA, hAH, heData⟩ := flatEntry_data p x e he
  obtain ⟨i, C, hi, hr, happ, hP, hQ⟩ := flatPath_rectangle_data r hx hz
  have hb := flatPathBase_source x A hA hAH
  have key := flatPath_entry_step n x.val.val.toPerm.injective i left hb heData hi hr
  refine ⟨A, hA, ?_, ?_⟩
  · rw [congrFun happ A, flatApply_high n x.val.val i _ _ C A hb.2.1
      (Fin.lt_def.mpr hb.2.2.1) hA hAH hi]
    exact hAH
  · rw [happ, hP, hQ]
    exact key

/-- Along a completely flat internal path, the four invariants persist. -/
theorem flatPath_internal {k : ℕ} {x y : SeamMatchingSource n m} (π : SeamInternalPath k x y)
    (hπ : π.AllFlat) (A : Fin (n + m + 1)) (hA : A.val < n) (hAH : n < (x.val.val A).val)
    (hinv : FlatPathInv n x.val.val (seamComplementFirst x.val) (seamComplementSecond x.val) A) :
    n < (y.val.val A).val ∧
      FlatPathInv n y.val.val (seamComplementFirst y.val) (seamComplementSecond y.val) A := by
  induction k generalizing x with
  | zero =>
    have h : x = y := π.property
    subst h
    exact ⟨hAH, hinv⟩
  | succ k ih =>
    obtain ⟨z, r, π'⟩ := π
    obtain ⟨hx, hπ'⟩ := hπ
    have hz := SeamInternalPath.allFlat_head π' hπ'
    obtain ⟨hzA, hzinv⟩ := flatPath_source_step r hx hz A hA hAH hinv.weak
    exact ih π' hπ' hzA hzinv

/-- Theorem J05:thm:flat: no correction path with at least two internal
transitions has northeast count one at every matching source. -/
theorem seamCorrectionPath_not_allFlat {k : ℕ} (hk : 2 ≤ k) {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) : ¬ π.2.2.2.1.AllFlat := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rcases π with ⟨a, b, e, ⟨a1, r0, ⟨a2, r1, rest⟩⟩, f⟩
  rintro ⟨-, ha1, hrest⟩
  have ha2 := SeamInternalPath.allFlat_head rest hrest
  obtain ⟨A, hA, hAH1, hinv1⟩ := flatPath_source_entry p e.val e.property r0 ha1
  obtain ⟨hAH2, hinv2⟩ := flatPath_source_step r1 ha1 ha2 A hA hAH1 hinv1
  obtain ⟨hAHb, hinvb⟩ := flatPath_internal rest hrest A hA hAH2 hinv2
  obtain ⟨left, hf⟩ := flatExit_data q b f.val f.property A hA hAHb
  exact flatPathInv_exit n (flatPathBase_source b A hA hAHb) hinvb left hf

/-- Lemma J05:lem:countbound, first half: northeast columns lie before the shared column. -/
theorem seamNortheastColumns_card_le_left (w : GridState (n + m + 1)) :
    (seamNortheastColumns (n := n) (m := m) w).card ≤ n := by
  calc (seamNortheastColumns (n := n) (m := m) w).card
      ≤ (Finset.univ.filter (fun c : Fin (n + m + 1) => c.val < n)).card := by
        apply Finset.card_le_card
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ((mem_seamNortheastColumns _ _).mp hc).1
    _ = n := seam_first_columns_card

/-- Lemma J05:lem:countbound, second half: the southwest columns lie in the last
`m + 1` columns, and there is one more southwest column than northeast columns. -/
theorem seamNortheastColumns_card_le_right (w : GridState (n + m + 1)) :
    (seamNortheastColumns (n := n) (m := m) w).card ≤ m := by
  have h1 := seamSouthwestColumns_card (n := n) (m := m) w
  have h2 : (seamSouthwestColumns (n := n) (m := m) w).card ≤ m + 1 := by
    calc (seamSouthwestColumns (n := n) (m := m) w).card
        ≤ (Finset.Ici (⟨n, by omega⟩ : Fin (n + m + 1))).card := by
          apply Finset.card_le_card
          intro c hc
          rw [Finset.mem_Ici, Fin.le_def]
          exact ((mem_seamSouthwestColumns _ _).mp hc).1
      _ = m + 1 := by
          rw [Fin.card_Ici]
          simp only
          omega
  omega

theorem seamMatchingSource_northeast_card_pos (x : SeamMatchingSource n m) :
    0 < (seamNortheastColumns x.val.val).card :=
  Finset.card_pos.mpr ((seamNortheastColumns_nonempty_iff x.val.val).mpr x.val.property)

/-- Corollary J05:cor:thin for `n ≤ 1`: every matching source then has northeast
count one, so no correction path has at least two internal transitions. -/
theorem seamCorrectionPath_isEmpty_of_left_le_one (hn : n ≤ 1) {k : ℕ} (hk : 2 ≤ k)
    (p q : SeamRetainedIndex n m) : IsEmpty (SeamCorrectionPath k p q) := by
  refine ⟨fun π => seamCorrectionPath_not_allFlat hk π
    (SeamInternalPath.allFlat_of_forall _ fun z => ?_)⟩
  have h1 := seamMatchingSource_northeast_card_pos z
  have h2 := seamNortheastColumns_card_le_left (n := n) (m := m) z.val.val
  omega

/-- Corollary J05:cor:thin for `m ≤ 1`: every matching source then has northeast
count one, so no correction path has at least two internal transitions. -/
theorem seamCorrectionPath_isEmpty_of_right_le_one (hm : m ≤ 1) {k : ℕ} (hk : 2 ≤ k)
    (p q : SeamRetainedIndex n m) : IsEmpty (SeamCorrectionPath k p q) := by
  refine ⟨fun π => seamCorrectionPath_not_allFlat hk π
    (SeamInternalPath.allFlat_of_forall _ fun z => ?_)⟩
  have h1 := seamMatchingSource_northeast_card_pos z
  have h2 := seamNortheastColumns_card_le_right (n := n) (m := m) z.val.val
  omega

/-- Corollary J05:cor:three (M603): with fixed second factor, there is no
three-transition correction path. -/
theorem seamCorrectionThree_fixedSecond_isEmpty (x y : GridState (n + 1))
    (z : GridState (m + 1)) : IsEmpty (SeamCorrectionPath 3 (x, z) (y, z)) := by
  refine ⟨fun π => ?_⟩
  have hmid := seamCorrectionThree_middle_eq_one x y z π
  apply seamCorrectionPath_not_allFlat (by norm_num) π
  rcases π with ⟨a, d, e, ⟨b, r, ⟨c, s, ⟨d', t, tail⟩⟩⟩, f⟩
  have hlast : d' = d := tail.property
  subst hlast
  exact ⟨seamMatchingEntry_northeast_card _ a e.val, hmid.1, hmid.2,
    seamMatchingExit_northeast_card _ d' f.val⟩

end OnLeConjecture.KnotFloer.GridFull

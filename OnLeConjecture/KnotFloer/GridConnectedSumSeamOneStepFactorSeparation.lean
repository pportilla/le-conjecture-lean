/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamOneStepOrientations
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamLongPathReduction

/-!
# A one-transition correction changes at most one retained factor

The actual entry, transition and exit permutations compose to a single
retained transposition. Its two columns lie in the same block, according
to the four proved neutral types. In particular there are no one-transition
corrections between retained pairs whose two factors both differ.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m k : ℕ}

def seamOneStepNetLeft (i : FlatKind) (P Q C : Fin k) : Fin k :=
  match i with
  | .lowFirst | .lowSecond => C
  | .highFirst => P
  | .highSecond => Q

def seamOneStepNetRight (i : FlatKind) (C A : Fin k) : Fin k :=
  match i with
  | .lowFirst | .lowSecond => A
  | .highFirst | .highSecond => C

theorem seamOneStep_target_swap (x y : GridState k) (i : FlatKind) (P Q C A : Fin k)
    (hPQ : P ≠ Q) (hPC : P ≠ C) (hQC : Q ≠ C)
    (hAP : A ≠ P) (hAQ : A ≠ Q) (hAC : A ≠ C)
    (hy : (y : Fin k → Fin k) = flatApply i x P Q C) :
    y.swapColumns (if seamOneStepExitLeft i then A else flatSecond i P Q C)
      (if seamOneStepExitLeft i then flatFirst i P Q C else A) =
    (((x.swapColumns P Q).swapColumns (if seamOneStepEntryLeft i then A else Q)
      (if seamOneStepEntryLeft i then P else A))).swapColumns
        (seamOneStepNetLeft i P Q C) (seamOneStepNetRight i C A) := by
  apply GridState.ext
  intro j
  simp only [GridState.swapColumns_apply]
  rw [congrFun hy (Equiv.swap
    (if seamOneStepExitLeft i then A else flatSecond i P Q C)
    (if seamOneStepExitLeft i then flatFirst i P Q C else A) j)]
  cases i <;> by_cases hjA : j = A
  all_goals first
    | subst j; simp [seamOneStepEntryLeft, seamOneStepExitLeft,
        seamOneStepNetLeft, seamOneStepNetRight, flatFirst, flatSecond, flatApply,
        Equiv.swap_apply_def, hPQ.symm, hPC.symm, hQC.symm, hAP, hAQ, hAC, hAC.symm]
    | skip
  all_goals by_cases hjP : j = P
  all_goals first
    | subst j; simp [seamOneStepEntryLeft, seamOneStepExitLeft,
        seamOneStepNetLeft, seamOneStepNetRight, flatFirst, flatSecond, flatApply,
        Equiv.swap_apply_def, hPQ, hPC, hPC.symm, hQC.symm, hAP, hAP.symm, hAQ, hAC, hAC.symm]
    | skip
  all_goals by_cases hjQ : j = Q
  all_goals first
    | subst j; simp [seamOneStepEntryLeft, seamOneStepExitLeft,
        seamOneStepNetLeft, seamOneStepNetRight, flatFirst, flatSecond, flatApply,
        Equiv.swap_apply_def, hPQ.symm, hPC.symm, hQC, hQC.symm, hAP, hAQ, hAQ.symm, hAC,
        hAC.symm]
    | skip
  all_goals by_cases hjC : j = C
  all_goals first
    | subst j; simp [seamOneStepEntryLeft, seamOneStepExitLeft,
        seamOneStepNetLeft, seamOneStepNetRight, flatFirst, flatSecond, flatApply,
        Equiv.swap_apply_def, hPC.symm, hQC.symm, hAP, hAQ, hAC, hAC.symm]
    | simp [seamOneStepEntryLeft, seamOneStepExitLeft,
        seamOneStepNetLeft, seamOneStepNetRight, flatFirst, flatSecond, flatApply,
        Equiv.swap_apply_def, hjA, hjP, hjQ, hjC]

/-- The full retained endpoints of any one-transition correction differ by a rectangle. -/
theorem seamOneStep_retained_rectangle (p q : SeamRetainedIndex n m)
    (x y : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (f : GridRectangleBetween y.val.val (seamState q.1 q.2))
    (hne : x ≠ y) (he : e.IsEmpty) (hr : r.IsEmpty) (hf : f.IsEmpty) :
    Nonempty (GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2)) := by
  obtain ⟨i, C, A, hA, hAH, hi, hrL, hrR, hyP, hyQ, heL, heR, hfL, hfR⟩ :=
    seamOneStep_all_orientations p q x y e r f hne he hr hf
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hPQ := seamComplementFirst_lt_second x.val
  have hAP : A ≠ seamComplementFirst x.val := by
    intro hh; have := congrArg Fin.val hh; omega
  have hAQ : A ≠ seamComplementSecond x.val := by
    intro hh; have := congrArg Fin.val hh; omega
  have hPC : seamComplementFirst x.val ≠ C := by
    intro hh
    subst C
    cases i <;> simp only [flatRange] at hi <;> omega
  have hQC : seamComplementSecond x.val ≠ C := by
    intro hh
    subst C
    cases i <;> simp only [flatRange] at hi <;> omega
  have hAC : A ≠ C := by
    intro hh
    subst C
    cases i <;> simp only [flatRange] at hi <;> omega
  have hcols : seamOneStepNetLeft i (seamComplementFirst x.val) (seamComplementSecond x.val) C ≠
      seamOneStepNetRight i C A := by
    cases i
    · exact hAC.symm
    · exact hAC.symm
    · exact hPC
    · exact hQC
  have hyApply := flatStep_apply r i C hi hrL hrR hyP hyQ
  have hsource := seamMatchingEntry_source_eq_swaps p x e
  rw [heL, heR] at hsource
  have htarget := f.target_eq_swapColumns
  rw [hfL, hfR, hyP, hyQ] at htarget
  have hswap := seamOneStep_target_swap x.val.val y.val.val i
    (seamComplementFirst x.val) (seamComplementSecond x.val) C A hPQ.ne hPC hQC hAP hAQ hAC
    hyApply
  have hfinal : seamState q.1 q.2 = (seamState p.1 p.2).swapColumns
      (seamOneStepNetLeft i (seamComplementFirst x.val) (seamComplementSecond x.val) C)
      (seamOneStepNetRight i C A) :=
    htarget.trans (hswap.trans (congrArg (fun v => v.swapColumns
      (seamOneStepNetLeft i (seamComplementFirst x.val) (seamComplementSecond x.val) C)
      (seamOneStepNetRight i C A)) hsource.symm))
  exact ⟨ofSwapColumns _ _ _ _ hcols hfinal⟩

/-- A complete one-transition correction changes at most one retained factor. -/
theorem seamCorrectionOne_factor_eq {p q : SeamRetainedIndex n m}
    (path : SeamCorrectionPath 1 p q) : p.1 = q.1 ∨ p.2 = q.2 := by
  rcases path with ⟨x, z, e, ⟨y, r, tail⟩, f⟩
  have hy : y = z := tail.property
  subst y
  obtain ⟨R⟩ := seamOneStep_retained_rectangle p q x z e.val r.val f.val
    r.property.1 e.property r.property.2 f.property
  exact seamRetainedRectangle_factor_eq p q R

/-- One-transition paths cannot contribute when both retained factors change. -/
theorem seamCorrectionOne_isEmpty_of_both_ne (p q : SeamRetainedIndex n m)
    (h₁ : p.1 ≠ q.1) (h₂ : p.2 ≠ q.2) : IsEmpty (SeamCorrectionPath 1 p q) :=
  ⟨fun path => (seamCorrectionOne_factor_eq path).elim h₁ h₂⟩

/-- When both factors change, the positive count begins at two internal transitions. -/
theorem seamPositiveCorrectionCount_both_ne_eq_two_long (p q : SeamRetainedIndex n m)
    (h₁ : p.1 ≠ q.1) (h₂ : p.2 ≠ q.2) :
    seamPositiveCorrectionCount p q = Fintype.card (SeamCorrectionPath 2 p q) +
      seamLongCorrectionCount p q := by
  have hzero : Fintype.card (SeamCorrectionPath 1 p q) = 0 :=
    Fintype.card_eq_zero_iff.mpr (seamCorrectionOne_isEmpty_of_both_ne p q h₁ h₂)
  rw [seamPositiveCorrectionCount_one_two_long, hzero, Nat.zero_add]

end OnLeConjecture.KnotFloer.GridFull

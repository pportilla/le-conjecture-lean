/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearWordEmbedding
public import Mathlib.Topology.CompactOpen

/-! # Closing the word deformation at its prescribed permutation

The source is the finite union of closed strand intervals with the terminal endpoint
of label `k` identified with the initial endpoint of label `w.permutation.symm k`.
The explicit relation is proved to describe exactly the cylinder coincidences of
both deformations. In particular no additional intersections arise at the seam.
The terminal carrier is polygonal. No smoothness at its corners is asserted.
-/

@[expose] public noncomputable section

open Set
open scoped Topology

namespace OnLeConjecture.KnotTheory

/-- On one closed period, equality of phases identifies only equal coordinates or
its two endpoints. -/
theorem circle_exp_scaled_eq_iff {T x y : ℝ} (hT : 0 < T)
    (hx : x ∈ Icc 0 T) (hy : y ∈ Icc 0 T) :
    Circle.exp (2 * Real.pi * x / T) = Circle.exp (2 * Real.pi * y / T) ↔
      x = y ∨ (x = 0 ∧ y = T) ∨ (x = T ∧ y = 0) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp h
    have he : x = y + (n : ℝ) * T := by
      have hh := congrArg (fun z : ℝ => z * T / (2 * Real.pi)) hn
      field_simp at hh
      nlinarith [Real.pi_pos]
    have hnlo : (-1 : ℤ) ≤ n := by
      by_contra h
      have hn' : (n : ℝ) ≤ -2 := by exact_mod_cast (show n ≤ -2 by omega)
      nlinarith [mul_le_mul_of_nonneg_right hn' hT.le, hx.1, hy.2]
    have hnhi : n ≤ (1 : ℤ) := by
      by_contra h
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
      nlinarith [mul_le_mul_of_nonneg_right hn' hT.le, hx.2, hy.1]
    interval_cases n
    · right; left
      norm_num at he
      constructor <;> linarith [hx.1, hy.2]
    · left
      simpa using he
    · right; right
      norm_num at he
      constructor <;> linarith [hx.2, hy.1]
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    all_goals simp [mul_div_cancel_right₀ _ hT.ne']

/-- The compact finite union of the source intervals of the word tangle. -/
abbrev PositiveRectilinearWordTangleSource {m : ℕ} (w : PositiveAdjacentWord m) :=
  Fin m × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1)

/-- The explicit endpoint identifications used to close the word. -/
def PositiveRectilinearWordClosureRel {m : ℕ} (w : PositiveAdjacentWord m)
    (p q : PositiveRectilinearWordTangleSource w) : Prop :=
  p = q ∨
    (p.2.val = 0 ∧ q.2.val = 2 * (w.length : ℝ) + 1 ∧
      p.1 = w.permutation.symm q.1) ∨
    (p.2.val = 2 * (w.length : ℝ) + 1 ∧ q.2.val = 0 ∧
      q.1 = w.permutation.symm p.1)

private theorem cylinder_eq_iff_closureRel {m : ℕ} (w : PositiveAdjacentWord m)
    (F : Fin m → ℝ → ℝ × ℂ)
    (hinj : Function.Injective (fun p : PositiveRectilinearWordTangleSource w => F p.1 p.2))
    (hslab : ∀ k t, t ∈ Icc 0 (2 * (w.length : ℝ) + 1) →
      (F k t).1 ∈ Icc 0 (2 * (w.length : ℝ) + 1) ∧
      ((F k t).1 = 0 ↔ t = 0) ∧
      ((F k t).1 = 2 * (w.length : ℝ) + 1 ↔ t = 2 * (w.length : ℝ) + 1))
    (hends : ∀ k, F k 0 = (0, (k.val : ℂ)) ∧
      F k (2 * (w.length : ℝ) + 1) =
        (2 * (w.length : ℝ) + 1, ((w.permutation.symm k).val : ℂ)))
    (p q : PositiveRectilinearWordTangleSource w) :
    positiveRectilinearCylinderPoint w (F p.1 p.2) =
      positiveRectilinearCylinderPoint w (F q.1 q.2) ↔
        PositiveRectilinearWordClosureRel w p q := by
  have hT : 0 < 2 * (w.length : ℝ) + 1 := by positivity
  constructor
  · intro he
    have hr := congrArg Prod.fst he
    have hi := congrArg Prod.snd he
    change Circle.exp _ = Circle.exp _ at hr
    change (F p.1 p.2).2 = (F q.1 q.2).2 at hi
    rcases (circle_exp_scaled_eq_iff hT
      (hslab p.1 p.2 p.2.property).1 (hslab q.1 q.2 q.2.property).1).mp hr with
      h | ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact Or.inl (hinj (Prod.ext h hi))
    · have hp' := (hslab p.1 p.2 p.2.property).2.1.mp hp
      have hq' := (hslab q.1 q.2 q.2.property).2.2.mp hq
      refine Or.inr (Or.inl ⟨hp', hq', ?_⟩)
      rw [hp', hq', (hends p.1).1, (hends q.1).2] at hi
      exact Fin.ext (Nat.cast_injective hi)
    · have hp' := (hslab p.1 p.2 p.2.property).2.2.mp hp
      have hq' := (hslab q.1 q.2 q.2.property).2.1.mp hq
      refine Or.inr (Or.inr ⟨hp', hq', ?_⟩)
      rw [hp', hq', (hends p.1).2, (hends q.1).1] at hi
      exact Fin.ext (Nat.cast_injective hi.symm)
  · rintro (rfl | ⟨hp, hq, hk⟩ | ⟨hp, hq, hk⟩)
    · rfl
    · rw [hp, hq, (hends p.1).1, (hends q.1).2, hk]
      simp [positiveRectilinearCylinderPoint, mul_div_cancel_right₀ _ hT.ne']
    · rw [hp, hq, (hends p.1).2, (hends q.1).1, hk]
      simp [positiveRectilinearCylinderPoint, mul_div_cancel_right₀ _ hT.ne']

/-- The first deformation has precisely the specified seam identifications. -/
theorem positiveRectilinearWordLift_cylinder_eq_iff {m : ℕ} (w : PositiveAdjacentWord m)
    {s : ℝ} (hs : s ∈ Icc 0 1) (p q : PositiveRectilinearWordTangleSource w) :
    positiveRectilinearCylinderPoint w (positiveRectilinearWordLift w p.1 s p.2) =
      positiveRectilinearCylinderPoint w (positiveRectilinearWordLift w q.1 s q.2) ↔
        PositiveRectilinearWordClosureRel w p q := by
  apply cylinder_eq_iff_closureRel w (fun k t => positiveRectilinearWordLift w k s t)
    (positiveRectilinearWordLift_injective w hs) _
    (fun k => positiveRectilinearWordLift_endpoints w k s)
  intro k t ht
  rw [positiveRectilinearWordLift_fst w k s ht]
  exact ⟨ht, Iff.rfl, Iff.rfl⟩

/-- Straightening has the same seam identifications, including its polygonal endpoint. -/
theorem positiveRectilinearWordStraighten_cylinder_eq_iff {m : ℕ}
    (w : PositiveAdjacentWord m) {s : ℝ} (hs : s ∈ Icc 0 1)
    (p q : PositiveRectilinearWordTangleSource w) :
    positiveRectilinearCylinderPoint w (positiveRectilinearWordStraighten w p.1 s p.2) =
      positiveRectilinearCylinderPoint w (positiveRectilinearWordStraighten w q.1 s q.2) ↔
        PositiveRectilinearWordClosureRel w p q :=
  cylinder_eq_iff_closureRel w (fun k t => positiveRectilinearWordStraighten w k s t)
    (positiveRectilinearWordStraighten_injective w hs)
    (fun k _ ht => positiveRectilinearWordStraighten_fst_slab w k hs ht)
    (fun k => positiveRectilinearWordStraighten_endpoints w k s) p q

/-- The seam relation is an equivalence relation. The proof uses its verified exact
coincidence characterization, not an enlarged equivalence closure. -/
def positiveRectilinearWordClosureSetoid {m : ℕ} (w : PositiveAdjacentWord m) :
    Setoid (PositiveRectilinearWordTangleSource w) where
  r := PositiveRectilinearWordClosureRel w
  iseqv := by
    have h := positiveRectilinearWordLift_cylinder_eq_iff w (s := 0) ⟨le_rfl, zero_le_one⟩
    exact ⟨fun p => (h p p).mp rfl,
      fun {p q} hpq => (h q p).mp ((h p q).mpr hpq).symm,
      fun {p q r} hpq hqr => (h p r).mp (((h p q).mpr hpq).trans ((h q r).mpr hqr))⟩

/-- The closed source obtained from precisely the terminal permutation identifications. -/
abbrev PositiveRectilinearWordClosedSource {m : ℕ} (w : PositiveAdjacentWord m) :=
  Quotient (positiveRectilinearWordClosureSetoid w)

/-- The first deformation on the closed source. -/
def positiveRectilinearWordClosedLift {m : ℕ} (w : PositiveAdjacentWord m)
    (s : Icc (0 : ℝ) 1) : PositiveRectilinearWordClosedSource w → Circle × ℂ :=
  Quotient.lift
    (fun p => positiveRectilinearCylinderPoint w (positiveRectilinearWordLift w p.1 s p.2))
    (fun p q h => (positiveRectilinearWordLift_cylinder_eq_iff w s.property p q).mpr h)

/-- The straightening deformation on the same closed source. -/
def positiveRectilinearWordClosedStraighten {m : ℕ} (w : PositiveAdjacentWord m)
    (s : Icc (0 : ℝ) 1) : PositiveRectilinearWordClosedSource w → Circle × ℂ :=
  Quotient.lift
    (fun p => positiveRectilinearCylinderPoint w
      (positiveRectilinearWordStraighten w p.1 s p.2))
    (fun p q h => (positiveRectilinearWordStraighten_cylinder_eq_iff w s.property p q).mpr h)

/-- Evaluation on a strand representative is the specified first-stage formula. -/
@[simp] theorem positiveRectilinearWordClosedLift_mk {m : ℕ} (w : PositiveAdjacentWord m)
    (s : Icc (0 : ℝ) 1) (p : PositiveRectilinearWordTangleSource w) :
    positiveRectilinearWordClosedLift w s (Quotient.mk (positiveRectilinearWordClosureSetoid w) p) =
      positiveRectilinearCylinderPoint w (positiveRectilinearWordLift w p.1 s p.2) := rfl

/-- Evaluation on a strand representative is the specified straightening formula. -/
@[simp] theorem positiveRectilinearWordClosedStraighten_mk {m : ℕ}
    (w : PositiveAdjacentWord m) (s : Icc (0 : ℝ) 1)
    (p : PositiveRectilinearWordTangleSource w) :
    positiveRectilinearWordClosedStraighten w s
      (Quotient.mk (positiveRectilinearWordClosureSetoid w) p) =
      positiveRectilinearCylinderPoint w (positiveRectilinearWordStraighten w p.1 s p.2) := rfl

/-- Closing the base coordinate is continuous. -/
theorem positiveRectilinearCylinderPoint_continuous {m : ℕ} (w : PositiveAdjacentWord m) :
    Continuous (positiveRectilinearCylinderPoint w) := by
  unfold positiveRectilinearCylinderPoint
  exact (Circle.exp.continuous.comp
    ((continuous_const.mul continuous_fst).div_const _)).prodMk continuous_snd

private theorem cylinder_family_continuous {m : ℕ} (w : PositiveAdjacentWord m)
    (F : Fin m → ℝ → ℝ → ℝ × ℂ)
    (hF : ∀ k, Continuous (fun st : ℝ × ℝ => F k st.1 st.2)) :
    Continuous (fun p : Icc (0 : ℝ) 1 × PositiveRectilinearWordTangleSource w =>
      positiveRectilinearCylinderPoint w (F p.2.1 p.1 p.2.2)) := by
  have hh : Continuous (fun p : Fin m × (Icc (0 : ℝ) 1 ×
      Icc (0 : ℝ) (2 * (w.length : ℝ) + 1)) =>
      positiveRectilinearCylinderPoint w (F p.1 p.2.1 p.2.2)) := by
    apply continuous_prod_of_discrete_left.mpr
    intro k
    exact (positiveRectilinearCylinderPoint_continuous w).comp
      ((hF k).comp ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)))
  exact hh.comp ((continuous_fst.comp continuous_snd).prodMk
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

/-- Joint continuity holds after descending the entire first deformation. -/
theorem positiveRectilinearWordClosedLift_continuous {m : ℕ} (w : PositiveAdjacentWord m) :
    Continuous (fun p : Icc (0 : ℝ) 1 × PositiveRectilinearWordClosedSource w =>
      positiveRectilinearWordClosedLift w p.1 p.2) := by
  apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
  exact cylinder_family_continuous w _ (positiveRectilinearWordLift_continuous w)

/-- Joint continuity holds after descending the entire straightening deformation. -/
theorem positiveRectilinearWordClosedStraighten_continuous {m : ℕ}
    (w : PositiveAdjacentWord m) :
    Continuous (fun p : Icc (0 : ℝ) 1 × PositiveRectilinearWordClosedSource w =>
      positiveRectilinearWordClosedStraighten w p.1 p.2) := by
  apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
  exact cylinder_family_continuous w _ (positiveRectilinearWordStraighten_continuous w)

/-- Every first-stage map of the closed source is injective. -/
theorem positiveRectilinearWordClosedLift_injective {m : ℕ} (w : PositiveAdjacentWord m)
    (s : Icc (0 : ℝ) 1) : Function.Injective (positiveRectilinearWordClosedLift w s) := by
  intro p q
  induction p using Quotient.inductionOn with | h p =>
    induction q using Quotient.inductionOn with | h q =>
      intro h
      exact Quotient.sound ((positiveRectilinearWordLift_cylinder_eq_iff w s.property p q).mp h)

/-- Every straightening map of the closed source is injective. -/
theorem positiveRectilinearWordClosedStraighten_injective {m : ℕ}
    (w : PositiveAdjacentWord m) (s : Icc (0 : ℝ) 1) :
    Function.Injective (positiveRectilinearWordClosedStraighten w s) := by
  intro p q
  induction p using Quotient.inductionOn with | h p =>
    induction q using Quotient.inductionOn with | h q =>
      intro h
      exact Quotient.sound
        ((positiveRectilinearWordStraighten_cylinder_eq_iff w s.property p q).mp h)

/-- Each first-stage slice is a closed embedding of the prescribed closed source. -/
theorem positiveRectilinearWordClosedLift_isClosedEmbedding {m : ℕ}
    (w : PositiveAdjacentWord m) (s : Icc (0 : ℝ) 1) :
    Topology.IsClosedEmbedding (positiveRectilinearWordClosedLift w s) :=
  ((positiveRectilinearWordClosedLift_continuous w).comp
    (continuous_const.prodMk continuous_id)).isClosedEmbedding
      (positiveRectilinearWordClosedLift_injective w s)

/-- Each straightening slice, including the polygonal endpoint, is a closed embedding. -/
theorem positiveRectilinearWordClosedStraighten_isClosedEmbedding {m : ℕ}
    (w : PositiveAdjacentWord m) (s : Icc (0 : ℝ) 1) :
    Topology.IsClosedEmbedding (positiveRectilinearWordClosedStraighten w s) :=
  ((positiveRectilinearWordClosedStraighten_continuous w).comp
    (continuous_const.prodMk continuous_id)).isClosedEmbedding
      (positiveRectilinearWordClosedStraighten_injective w s)

/-- The two closed deformations have exactly the same common slice. -/
theorem positiveRectilinearWordClosedLift_one {m : ℕ} (w : PositiveAdjacentWord m)
    (p : PositiveRectilinearWordClosedSource w) :
    positiveRectilinearWordClosedLift w ⟨1, zero_le_one, le_rfl⟩ p =
      positiveRectilinearWordClosedStraighten w ⟨0, le_rfl, zero_le_one⟩ p := by
  induction p using Quotient.inductionOn with | h p =>
    change positiveRectilinearCylinderPoint w (positiveRectilinearWordLift w p.1 1 p.2) =
      positiveRectilinearCylinderPoint w (positiveRectilinearWordStraighten w p.1 0 p.2)
    rw [positiveRectilinearWordLift_one]

/-- The terminal closed map is exactly the cylinder image of the literal word carrier. -/
theorem positiveRectilinearWordClosedStraighten_one {m : ℕ} (w : PositiveAdjacentWord m)
    (p : PositiveRectilinearWordTangleSource w) :
    positiveRectilinearWordClosedStraighten w ⟨1, zero_le_one, le_rfl⟩
      (Quotient.mk (positiveRectilinearWordClosureSetoid w) p) =
      positiveRectilinearCylinderPoint w (positiveRectilinearWordCarrier w p.1 p.2) := by
  simp only [positiveRectilinearWordClosedStraighten_mk, positiveRectilinearWordStraighten_one]

/-- The time-preserving map of the first deformation is also a closed embedding. -/
theorem positiveRectilinearWordClosedLift_total_isClosedEmbedding {m : ℕ}
    (w : PositiveAdjacentWord m) :
    Topology.IsClosedEmbedding
      (fun p : Icc (0 : ℝ) 1 × PositiveRectilinearWordClosedSource w =>
        (p.1, positiveRectilinearWordClosedLift w p.1 p.2)) := by
  apply (continuous_fst.prodMk (positiveRectilinearWordClosedLift_continuous w)).isClosedEmbedding
  rintro ⟨s, p⟩ ⟨t, q⟩ h
  have hst := congrArg Prod.fst h
  change s = t at hst
  subst t
  exact Prod.ext rfl (positiveRectilinearWordClosedLift_injective w s (congrArg Prod.snd h))

/-- The time-preserving map of straightening is a closed embedding, including its limit. -/
theorem positiveRectilinearWordClosedStraighten_total_isClosedEmbedding {m : ℕ}
    (w : PositiveAdjacentWord m) :
    Topology.IsClosedEmbedding
      (fun p : Icc (0 : ℝ) 1 × PositiveRectilinearWordClosedSource w =>
        (p.1, positiveRectilinearWordClosedStraighten w p.1 p.2)) := by
  apply (continuous_fst.prodMk
    (positiveRectilinearWordClosedStraighten_continuous w)).isClosedEmbedding
  rintro ⟨s, p⟩ ⟨t, q⟩ h
  have hst := congrArg Prod.fst h
  change s = t at hst
  subst t
  exact Prod.ext rfl (positiveRectilinearWordClosedStraighten_injective w s (congrArg Prod.snd h))

end OnLeConjecture.KnotTheory

/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingBarrier
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingSchur

/-!
# Rectangle paths supporting the matching transition operator

Nonzero internal coefficients have actual empty-rectangle witnesses. The barrier
conditions propagate along these witnesses and force their exit coefficients to vanish.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp
variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- One nonmatching internal edge, witnessed by an actual full empty rectangle. -/
def StabilizationMatchingStep (x z : StabilizationMatchingNode G s) : Prop :=
  x ≠ z ∧ ∃ r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z), r.IsEmpty

/-- An entry followed by at least two nonmatching internal rectangle steps. -/
def StabilizationLongMatchingPath (x : GridState n) (z : StabilizationMatchingNode G s) : Prop :=
  ∃ a b c : StabilizationMatchingNode G s,
    (∃ r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s a), r.IsEmpty) ∧
    StabilizationMatchingStep G s a b ∧ StabilizationMatchingStep G s b c ∧
    Relation.ReflTransGen (StabilizationMatchingStep G s) c z

/-- Appending an internal edge preserves the concrete long-path witness. -/
theorem StabilizationLongMatchingPath.tail {x : GridState n}
    {z w : StabilizationMatchingNode G s} (h : StabilizationLongMatchingPath G s x z)
    (hzw : StabilizationMatchingStep G s z w) : StabilizationLongMatchingPath G s x w := by
  obtain ⟨a, b, c, he, hab, hbc, hp⟩ := h
  exact ⟨a, b, c, he, hab, hbc, hp.tail hzw⟩

/-- The concrete barriers persist along every finite internal rectangle path. -/
theorem StabilizationMatchingBarrier.path {L R : Fin (n + 1)}
    {x z : StabilizationMatchingNode G s}
    (h : StabilizationMatchingBarrier G s L R x)
    (hp : Relation.ReflTransGen (StabilizationMatchingStep G s) x z) :
    StabilizationMatchingBarrier G s L R z := by
  induction hp with
  | refl => exact h
  | @tail y z hp hyz ih =>
    obtain ⟨hne, r, hr⟩ := hyz
    exact ih.transition G s hne r hr

variable (R : Type*) [CommRing R]

private theorem rectangle_of_coefficient_ne_zero {a b : GridState (n + 1)}
    (h : laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R a b ≠ 0) :
    ∃ r : GridRectangleBetween a b, r.IsEmpty := by
  classical
  have hn : (GridRectangleBetween.emptyRectangles a b).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    exact h (by rw [laurentCoefficient_eq, hn, Finset.sum_empty])
  obtain ⟨r, hr⟩ := hn
  exact ⟨r, (GridRectangleBetween.mem_emptyRectangles r).mp hr⟩

/-- A nonzero internal matrix entry supplies a geometric matching step. -/
theorem stabilizationMatchingStep_of_transition_ne_zero
    (x z : StabilizationMatchingNode G s)
    (h : stabilizationMatchingTransition G s R (single x 1) z ≠ 0) :
    StabilizationMatchingStep G s x z := by
  classical
  rw [stabilizationMatchingTransition_single_apply] at h
  split_ifs at h with hxz
  · exact False.elim (h rfl)
  · exact ⟨hxz, rectangle_of_coefficient_ne_zero G s R h⟩

/-- Every nonzero transition output has a supported predecessor joined by an empty rectangle. -/
theorem stabilizationMatchingTransition_support_predecessor
    (c : StabilizationMatchingNode G s →₀ LaurentPolynomial R)
    (z : StabilizationMatchingNode G s)
    (hz : z ∈ (stabilizationMatchingTransition G s R c).support) :
    ∃ x ∈ c.support, StabilizationMatchingStep G s x z := by
  classical
  let := Fintype.ofFinite (StabilizationMatchingNode G s)
  rw [Finsupp.mem_support_iff, finiteEnd_apply_apply] at hz
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  refine ⟨x, Finsupp.mem_support_iff.mpr ?_,
    stabilizationMatchingStep_of_transition_ne_zero G s R x z ?_⟩
  · intro h
    exact hx (by rw [h, zero_mul])
  · intro h
    exact hx (by rw [h, mul_zero])

/-- The matching entry coefficient is precisely the full rectangle coefficient from a center. -/
theorem stabilizationMatchingEntry_single_apply (x : GridState n)
    (z : StabilizationMatchingNode G s) :
    stabilizationMatchingEntry G s R (single x 1) z =
      laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R
        (x.insertPoint s.succ (G.X s).succ) (stabilizationMatchingTargetState G s z) := by
  simp only [stabilizationMatchingEntry, LinearMap.comp_apply,
    laurentStabilizationCenterInclusion_single, stabilizationMatchingTargetProjection_apply,
    laurentDifferential_single, laurentOnGenerator_apply]

/-- The matching exit coefficient is precisely the full rectangle coefficient to a center. -/
theorem stabilizationMatchingExit_single_apply (z : StabilizationMatchingNode G s)
    (x : GridState n) :
    stabilizationMatchingExit G s R (single z 1) x =
      laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R z.val
        (x.insertPoint s.succ (G.X s).succ) := by
  simp only [stabilizationMatchingExit, LinearMap.comp_apply,
    stabilizationMatchingSourceInclusion_single, laurentStabilizationCenterProjection_apply,
    laurentDifferential_single, laurentOnGenerator_apply]

/-- Every supported entry has a full empty rectangle from the prescribed center. -/
theorem stabilizationMatchingEntry_support_rectangle (x : GridState n)
    (z : StabilizationMatchingNode G s)
    (hz : z ∈ (stabilizationMatchingEntry G s R (single x 1)).support) :
    ∃ r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s z), r.IsEmpty := by
  rw [Finsupp.mem_support_iff, stabilizationMatchingEntry_single_apply] at hz
  exact rectangle_of_coefficient_ne_zero G s R hz

/-- Every coefficient after two or more internal transitions is supported on an actual long path. -/
theorem stabilizationMatching_power_entry_support_long_path (k : ℕ) (x : GridState n)
    (z : StabilizationMatchingNode G s)
    (hz : z ∈ ((stabilizationMatchingTransition G s R ^ (k + 2))
      (stabilizationMatchingEntry G s R (single x 1))).support) :
    StabilizationLongMatchingPath G s x z := by
  induction k generalizing z with
  | zero =>
    change z ∈ (stabilizationMatchingTransition G s R
      (stabilizationMatchingTransition G s R
        (stabilizationMatchingEntry G s R (single x 1)))).support at hz
    obtain ⟨b, hb, hbc⟩ := stabilizationMatchingTransition_support_predecessor G s R _ z hz
    obtain ⟨a, ha, hab⟩ := stabilizationMatchingTransition_support_predecessor G s R _ b hb
    exact ⟨a, b, z, stabilizationMatchingEntry_support_rectangle G s R x a ha,
      hab, hbc, .refl⟩
  | succ k ih =>
    have hpow : k + 1 + 2 = (k + 2) + 1 := by omega
    rw [hpow, pow_succ', Module.End.mul_apply] at hz
    obtain ⟨w, hw, hwz⟩ := stabilizationMatchingTransition_support_predecessor G s R _ z hz
    exact (ih w hw).tail G s hwz

/-- A barrier node has zero full matching exit chain. -/
theorem stabilizationMatchingExit_single_eq_zero_of_barrier {L K : Fin (n + 1)}
    {z : StabilizationMatchingNode G s} (h : StabilizationMatchingBarrier G s L K z) :
    stabilizationMatchingExit G s R (single z 1) = 0 := by
  apply Finsupp.ext
  intro x
  rw [stabilizationMatchingExit_single_apply, Finsupp.zero_apply]
  by_contra hc
  obtain ⟨r, hr⟩ := rectangle_of_coefficient_ne_zero G s R hc
  exact h.no_exit G s x r hr

/-- A chain supported on concrete barrier nodes has zero matching exit. -/
theorem stabilizationMatchingExit_eq_zero_of_support_barrier
    (c : StabilizationMatchingNode G s →₀ LaurentPolynomial R)
    (hc : ∀ z ∈ c.support, ∃ L K, StabilizationMatchingBarrier G s L K z) :
    stabilizationMatchingExit G s R c = 0 := by
  classical
  conv_lhs => rw [← Finsupp.sum_single c, map_finsuppSum]
  apply Finset.sum_eq_zero
  intro z hz
  obtain ⟨L, K, h⟩ := hc z hz
  change stabilizationMatchingExit G s R (single z (c z)) = 0
  rw [← Finsupp.smul_single_one, map_smul,
    stabilizationMatchingExit_single_eq_zero_of_barrier G s R h, smul_zero]

end OnLeConjecture.KnotFloer.GridFull

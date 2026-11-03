/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Linarith

/-! # Separating finitely many row heights

An arbitrarily small common positive affine perturbation by enumeration
rank separates equal heights while preserving every original strict order.
The indices may be horizontal arcs, so their two endpoints retain one row.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology

namespace OnLeConjecture.KnotTheory

/-- Separate the values of a finite real map within any positive tolerance,
preserving every strict comparison. The empty index type is allowed. -/
theorem exists_injective_row_perturbation {α : Type*} [Finite α]
    (f : α → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α → ℝ, Function.Injective g ∧
      (∀ a, |g a - f a| < ε) ∧
      ∀ a b, f a < f b → g a < g b := by
  classical
  let := Fintype.ofFinite α
  let e := Fintype.equivFin α
  let g : ℝ → α → ℝ := fun t a => f a + t * (e a).val
  have hg (a : α) : ContinuousAt (fun t : ℝ => g t a) 0 :=
    continuousAt_const.add (continuousAt_id.mul continuousAt_const)
  have hclose (a : α) : ∀ᶠ t : ℝ in 𝓝 0, |g t a - f a| < ε := by
    have hc : ContinuousAt (fun t : ℝ => |g t a - f a|) 0 := by
      exact ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).sub
        continuousAt_const).abs
    exact hc.eventually_lt continuousAt_const (by simpa [g] using hε)
  have horder (a b : α) : ∀ᶠ t : ℝ in 𝓝 0,
      f a < f b → g t a < g t b := by
    by_cases hab : f a < f b
    · have h := (hg a).eventually_lt (hg b)
        (by simpa [g] using hab)
      exact h.mono fun _ ht _ => ht
    · exact .of_forall fun _ h => (hab h).elim
  have hall := (Filter.eventually_all.mpr hclose).and
    (Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr (horder a))
  obtain ⟨δ, hδ, hspec⟩ := Metric.eventually_nhds_iff.mp hall
  have ht : δ / 2 ∈ ball (0 : ℝ) δ := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  obtain ⟨hnear, hlt⟩ := hspec ht
  refine ⟨g (δ / 2), ?_, hnear, hlt⟩
  intro a b hab
  rcases lt_trichotomy (f a) (f b) with h | h | h
  · exact False.elim ((hlt a b h).ne hab)
  · apply e.injective
    apply Fin.ext
    have hprod : δ / 2 * (e a).val = δ / 2 * (e b).val := by
      have hsum : f b + δ / 2 * (e a).val = f b + δ / 2 * (e b).val := by
        simpa only [g, h] using hab
      exact add_left_cancel hsum
    have heq : ((e a).val : ℝ) = (e b).val :=
      mul_left_cancel₀ (by positivity : δ / 2 ≠ 0) hprod
    exact_mod_cast heq
  · exact False.elim ((hlt b a h).ne hab.symm)

end OnLeConjecture.KnotTheory

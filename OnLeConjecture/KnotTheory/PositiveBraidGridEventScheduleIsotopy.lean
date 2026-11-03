/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridScheduleIsotopy
public import OnLeConjecture.KnotTheory.PositiveBraidGridFixedSchedule

/-! # Transport of the retained event model to the fixed generator schedule

The first endpoint is the literal global event model with its original sorting
labels. The second endpoint uses the same flattened word on the fixed schedule.
The base-period origin remains explicit in the second endpoint formula.
-/

@[expose] public noncomputable section
open Set Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic OnLeConjecture.DifferentialTopology
attribute [local instance] finrank_real_complex_fact'

local instance eventScheduleRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _
local instance eventScheduleRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.KnotTheory

/-- The actual event times and labels determine an ambient transport to the fixed
schedule. Empty event lists and empty subwords are included. -/
theorem exists_positiveGridGlobalWordModel_fixed_schedule_diffeotopy {m N : ℕ}
    (hm : 0 < m) (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin m)) (w : Fin N → PositiveAdjacentWord m)
    (hlt : ∀ j, left j < right j)
    (hsep : ∀ j q, j < q → right j < left q)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (hc : (σ (Fin.last N)).trans (finRotate m) = σ 0)
    (i : Fin 2) (b : ℝ) (hb : ∀ j, b < left j)
    (hd : ∀ j, right j < b + 2 * Real.pi) :
    ∃ W : Circle × ℝ → ℂ, ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞ W ∧
      (∀ k θ, θ ∈ Icc b (b + 2 * Real.pi) → W (braidCircleSheet m k θ, 0) =
        positiveGridGlobalWordModel left right σ w k θ) ∧
      (∀ k θ, θ ∈ Icc b (b + 2 * Real.pi) → W (braidCircleSheet m k θ, 1) =
        (positiveRoundedWordLift (List.ofFn w).flatten ((σ 0).symm k) 0
          (positiveRoundedWordPeriodTime (List.ofFn w).flatten (θ - b))).2) ∧
      ∃ (A B : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
          (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
        (∀ v, (A v : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (v ^ m, W (v, 0))) ∧
        (∀ v, (B v : EuclideanSpace ℂ (Fin 2)) = planeSolidTorusMap i (v ^ m, W (v, 1))) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ v, Φ.final (A v) = B v := by
  have hw : σ 0 * PositiveAdjacentWord.permutation (List.ofFn w).flatten = σ (Fin.last N) :=
    positiveWordSequence_permutation σ w hp
  have hstart (j : Fin (List.ofFn w).flatten.length) :
      b < positiveFlattenedEventLeft w left right j :=
    (hb _).trans (positiveEventLetter_inside w left right hlt _).1
  have hend (j : Fin (List.ofFn w).flatten.length) :
      positiveFlattenedEventRight w left right j < b + 2 * Real.pi :=
    (positiveEventLetter_inside w left right hlt _).2.trans (hd _)
  obtain ⟨W, hW, hs, A, B, hA, hB, Φ, hΦ⟩ := exists_positiveGridSchedule_diffeotopy hm
    (List.ofFn w).flatten (σ 0) (σ (Fin.last N)) hw hc i b
    (positiveFlattenedEventLeft w left right) (positiveFlattenedEventRight w left right)
    (positiveFixedAngularLeft (List.ofFn w).flatten b)
    (positiveFixedAngularRight (List.ofFn w).flatten b)
    (positiveFlattenedEvent_left_lt_right w left right hlt)
    (positiveFixedAngular_left_lt_right _ b)
    (positiveFlattenedEvent_order w left right hlt hsep)
    (positiveFixedAngular_order _ b) hstart
    (fun j => (positiveFixedAngular_inside _ b j).1) hend
    (fun j => (positiveFixedAngular_inside _ b j).2)
  refine ⟨W, hW, ?_, ?_, A, B, hA, hB, Φ, hΦ⟩
  · intro k θ hθ
    rw [hs k θ 0 hθ]
    simp only [positiveGridScheduleFamily, positiveScheduleBlend_zero]
    exact (positiveGridGlobalWordModel_eq_flattened_schedule left right σ w hlt hp k θ).symm
  · intro k θ hθ
    rw [hs k θ 1 hθ]
    simp only [positiveGridScheduleFamily, positiveScheduleBlend_one]
    exact positiveGridScheduledWord_fixedAngular_eq_lift _ b _ θ

end OnLeConjecture.KnotTheory

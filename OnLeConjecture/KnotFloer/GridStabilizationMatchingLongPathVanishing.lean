/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingPaths
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingBarrierInitial

/-!
# Vanishing of every matching contribution with at least two internal steps

An actual entry and its first two internal rectangles create the proved geometric
barriers. The barriers persist along every further rectangle step and exclude every
center exit. Thus these terms of the transferred differential vanish by support.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp
variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- Every actual long matching path produces persistent barriers at its endpoint. -/
theorem StabilizationLongMatchingPath.has_barrier {x : GridState n}
    {z : StabilizationMatchingNode G s} (h : StabilizationLongMatchingPath G s x z) :
    ∃ L K, StabilizationMatchingBarrier G s L K z := by
  obtain ⟨a, b, c, ⟨e, he⟩, ⟨hab, r, hr⟩, ⟨hbc, t, ht⟩, hp⟩ := h
  have hb := stabilizationMatchingBarrier_of_entry_two_steps
    G s x a b c hab hbc e r t he hr ht
  exact ⟨_, _, hb.path G s hp⟩

/-- No actual matching path with at least two internal steps can exit to a center. -/
theorem StabilizationLongMatchingPath.no_exit {x : GridState n}
    {z : StabilizationMatchingNode G s} (h : StabilizationLongMatchingPath G s x z)
    (y : GridState n)
    (r : GridRectangleBetween z.val (y.insertPoint s.succ (G.X s).succ)) : ¬r.IsEmpty := by
  obtain ⟨L, K, hb⟩ := h.has_barrier G s
  exact hb.no_exit G s y r

variable (R : Type*) [CommRing R]

/-- Every higher internal-power contribution vanishes on each old state generator. -/
theorem stabilizationMatchingExit_power_entry_single_eq_zero (k : ℕ) (x : GridState n) :
    stabilizationMatchingExit G s R
      ((stabilizationMatchingTransition G s R ^ (k + 2))
        (stabilizationMatchingEntry G s R (single x 1))) = 0 := by
  apply stabilizationMatchingExit_eq_zero_of_support_barrier G s R
  intro z hz
  exact (stabilizationMatching_power_entry_support_long_path G s R k x z hz).has_barrier G s

/-- The actual matching exit annihilates every power of at least two after the actual entry. -/
theorem stabilizationMatchingExit_power_entry_eq_zero (k : ℕ) :
    stabilizationMatchingExit G s R ∘ₗ
      (stabilizationMatchingTransition G s R ^ (k + 2)) ∘ₗ
        stabilizationMatchingEntry G s R = 0 := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply]
  exact stabilizationMatchingExit_power_entry_single_eq_zero G s R k x

end OnLeConjecture.KnotFloer.GridFull

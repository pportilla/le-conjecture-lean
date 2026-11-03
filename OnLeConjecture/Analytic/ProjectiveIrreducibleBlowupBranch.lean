/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectiveReducedBlowupBranchCount
public import OnLeConjecture.Analytic.IrreducibleBlowupBranch

/-!
# The unique projective point of an irreducible strict transform

Analytic coordinate changes induce a bijection of projective blowup
centers. Transporting the regular-coordinate theorem through this
bijection proves uniqueness and irreducibility without a transversality
assumption on the original coordinates.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- A chart lift preserves irreducibility of the strict transform. -/
theorem HasProjectiveBlowupLift.irreducible
    {e : PointedEquivGerm 2} {a b : Option ℂ}
    (h : HasProjectiveBlowupLift e a b)
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hi : Irreducible (projectiveStrictTransform m (e.forward.pullbackRingHom f)
      (e.forward.pullback_mem_maximalIdeal_pow hf) a)) :
    Irreducible (projectiveStrictTransform m f hf b) := by
  obtain ⟨E, hE⟩ := h.strictTransform_associated m f hf
  exact hE.symm.irreducible ((MulEquiv.irreducible_iff E.pullbackRingEquiv.toMulEquiv).mpr hi)

/-- Every irreducible equation of positive exact order has precisely one
nonunit projective strict transform, which is itself irreducible. -/
theorem exists_unique_irreducible_projectiveStrictTransform
    (m : ℕ) (hm : 0 < m) (f : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (hirr : Irreducible f) :
    ∃ t : Option ℂ, Irreducible (projectiveStrictTransform m f hf t) ∧
      ∀ u, u ≠ t → IsUnit (projectiveStrictTransform m f hf u) := by
  obtain ⟨e, he⟩ := exists_linear_equiv_regularInFirstCoordinateOfOrder hf hnext
  let g := e.forward.pullbackRingHom f
  have hg : g ∈ maximalIdeal 2 ^ m := e.forward.pullback_mem_maximalIdeal_pow hf
  have hgirr : Irreducible g :=
    (MulEquiv.irreducible_iff e.pullbackRingEquiv.toMulEquiv).mpr hirr
  obtain ⟨c, hc, hother, hinfinity⟩ :=
    exists_unique_irreducible_pointBlowupTransform_of_regular m hm g hg hgirr he
  refine ⟨projectiveCenterMap e (some c), ?_, ?_⟩
  · apply (projectiveCenterMap_hasLift e (some c)).irreducible m f hf
    simpa only [projectiveStrictTransform_some] using hc
  · intro u hu
    obtain ⟨a, ha⟩ := (projectiveCenterMap_bijective e).surjective u
    have hane : a ≠ some c := by
      intro hac
      exact hu (by rw [← ha, hac])
    rw [← ha, (projectiveCenterMap_hasLift e a).isUnit_iff m f hf]
    cases a with
    | none => exact hinfinity
    | some z =>
      rw [projectiveStrictTransform_some]
      exact hother z (fun hz => hane (congrArg some hz))

/-- Any nonunit projective strict transform of an irreducible equation
is irreducible, and every other projective strict transform is a unit. -/
theorem irreducible_projectiveStrictTransform_of_nonunit
    (m : ℕ) (hm : 0 < m) (f : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (hirr : Irreducible f) (t : Option ℂ)
    (ht : ¬ IsUnit (projectiveStrictTransform m f hf t)) :
    Irreducible (projectiveStrictTransform m f hf t) ∧
      ∀ u, u ≠ t → IsUnit (projectiveStrictTransform m f hf u) := by
  obtain ⟨a, ha, hother⟩ := exists_unique_irreducible_projectiveStrictTransform
    m hm f hf hnext hirr
  have hta : t = a := by
    by_contra h
    exact ht (hother t h)
  subst a
  exact ⟨ha, hother⟩

/-- At the unique projective point of an irreducible strict transform,
the intersection order with the exceptional divisor is the original order. -/
theorem projectiveExceptionalIntersectionOrder_eq_of_irreducible
    (m : ℕ) (hm : 0 < m) (f : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (hirr : Irreducible f) (t : Option ℂ)
    (ht : ¬ IsUnit (projectiveStrictTransform m f hf t)) :
    projectiveExceptionalIntersectionOrder m f hf t = m := by
  classical
  obtain ⟨_, hother⟩ := irreducible_projectiveStrictTransform_of_nonunit
    m hm f hf hnext hirr t ht
  have hsum := sum_projective_exceptional_restriction_orders_eq m f hf hnext {t} (by
    intro u hu
    apply Finset.mem_singleton.mpr
    by_contra h
    exact (valueRingHom_ne_zero_of_isUnit (hother u h)) (mem_maximalIdeal_iff.mp hu))
  simpa only [Finset.sum_singleton] using hsum

end OnLeConjecture.Analytic.Germ

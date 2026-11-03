/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IrreducibleBlowupPolarDescent
public import OnLeConjecture.Analytic.ExactLinearCoordinates
public import OnLeConjecture.Analytic.AnalyticPointBasis

/-!
# Finite smooth resolution chains for irreducible plane germs

The chain records analytic coordinate changes and the defined analytic
strict transforms. Existence follows by induction on ordinary multiplicity
and then on the finite transverse polar intersection. No resolution
existence or curve parametrization is assumed.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- A finite sequence of analytic coordinate changes and point blowups
whose final strict transform has ordinary order one. -/
inductive HasFiniteSmoothBlowupChain : Germ 2 → Prop where
  | smooth (f : Germ 2) (hf : f ∈ maximalIdeal 2)
      (hnext : f ∉ maximalIdeal 2 ^ 2) : HasFiniteSmoothBlowupChain f
  | source (f : Germ 2) (e : PointedEquivGerm 2)
      (hchild : HasFiniteSmoothBlowupChain (e.forward.pullbackRingHom f)) :
      HasFiniteSmoothBlowupChain f
  | blowup (f : Germ 2) (m : ℕ) (hm : 2 ≤ m)
      (horder : f ∈ maximalIdeal 2 ^ m)
      (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) (c : ℂ)
      (hchild : HasFiniteSmoothBlowupChain (pointBlowupTransform c m f horder)) :
      HasFiniteSmoothBlowupChain f

theorem exists_exact_maximalIdeal_order {n : ℕ} (f : Germ n) (hf : f ≠ 0) :
    ∃ m : ℕ, f ∈ maximalIdeal n ^ m ∧ f ∉ maximalIdeal n ^ (m + 1) := by
  classical
  have hex : ∃ m : ℕ, f ∉ maximalIdeal n ^ (m + 1) := by
    by_contra h
    apply hf
    apply eq_zero_of_mem_maximalIdeal_pow_all
    intro m
    cases m with
    | zero => simp
    | succ m => exact not_not.mp (fun hm => h ⟨m, hm⟩)
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  by_cases hm : Nat.find hex = 0
  · simp only [hm, pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [hk]
    exact not_not.mp (Nat.find_min hex (show k < Nat.find hex by omega))

theorem irreducible_mem_maximalIdeal (f : Germ 2) (hf : Irreducible f) :
    f ∈ maximalIdeal 2 := by
  rw [mem_maximalIdeal_iff]
  by_contra h
  exact hf.not_isUnit (isUnit_of_valueRingHom_ne_zero h)

theorem hasFiniteSmoothBlowupChain_of_irreducible_regular
    (m : ℕ) (f : Germ 2) (hirr : Irreducible f)
    (horder : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (hregular : IsRegularInFirstCoordinateOfOrder f m) :
    HasFiniteSmoothBlowupChain f := by
  suffices main : ∀ m : ℕ, ∀ f : Germ 2, Irreducible f →
      f ∈ maximalIdeal 2 ^ m → f ∉ maximalIdeal 2 ^ (m + 1) →
      IsRegularInFirstCoordinateOfOrder f m → HasFiniteSmoothBlowupChain f by
    exact main m f hirr horder hnext hregular
  intro m
  induction m using Nat.strong_induction_on with
  | h m ihm =>
    have inner : ∀ N : ℕ, ∀ (g : Germ 2) (hg : Irreducible g)
        (ho : g ∈ maximalIdeal 2 ^ m) (hn : g ∉ maximalIdeal 2 ^ (m + 1))
        (hr : IsRegularInFirstCoordinateOfOrder g m)
        (hfin : PlaneCurve.HasFiniteIntersection g (partialDerivative 0 g)),
        PlaneCurve.intersectionMultiplicity g (partialDerivative 0 g) hfin = N →
          HasFiniteSmoothBlowupChain g := by
      intro N
      induction N using Nat.strong_induction_on with
      | h N ihN =>
        intro g hg ho hn hr hfin hN
        have hmpos : 0 < m := by
          by_contra hm
          have hm0 : m = 0 := by omega
          apply hn
          simpa only [hm0, zero_add, pow_one] using irreducible_mem_maximalIdeal g hg
        by_cases hm1 : m = 1
        · apply HasFiniteSmoothBlowupChain.smooth g (irreducible_mem_maximalIdeal g hg)
          simpa only [hm1] using hn
        have hm2 : 2 ≤ m := by omega
        obtain ⟨c, hc, hcfin, hpolar⟩ :=
          exists_irreducible_transform_polar_lt m hm2 g ho hg hr
        let G := pointBlowupTransform c m g ho
        obtain ⟨k, hkorder, hknext⟩ := exists_exact_maximalIdeal_order G hc.ne_zero
        have hkm : k ≤ m := by
          by_contra h
          exact pointBlowupTransform_order_bound c m g ho hn
            ((Ideal.pow_le_pow_right (by omega)) hkorder)
        apply HasFiniteSmoothBlowupChain.blowup g m hm2 ho hn c
        by_cases hkeq : k = m
        · have hGo : G ∈ maximalIdeal 2 ^ m := hkeq ▸ hkorder
          have hGn : G ∉ maximalIdeal 2 ^ (m + 1) := hkeq ▸ hknext
          have hGr := pointBlowupTransform_regular_of_full_order c m g G ho hn hGo
            (pointBlowupTransform_factor c m g ho)
          have hlt : PlaneCurve.intersectionMultiplicity G (partialDerivative 0 G) hcfin < N := by
            simpa only [← hN] using hpolar
          exact ihN _ hlt G hc hGo hGn hGr hcfin rfl
        · obtain ⟨e, he⟩ := exists_linear_equiv_regularInFirstCoordinateOfOrder hkorder hknext
          apply HasFiniteSmoothBlowupChain.source G e
          apply ihm k (lt_of_le_of_ne hkm hkeq) (e.forward.pullbackRingHom G)
          · exact (MulEquiv.irreducible_iff e.pullbackRingEquiv.toMulEquiv).mpr hc
          · exact e.forward.pullback_mem_maximalIdeal_pow hkorder
          · exact (e.pullback_mem_maximalIdeal_pow_iff G).not.mpr hknext
          · exact he
    intro g hg ho hn hr
    exact inner _ g hg ho hn hr
      (PlaneCurve.finite_first_partial_polar_of_irreducible_regular g hg m hr) rfl

/-- Every irreducible plane analytic equation reaches a smooth strict
transform after finitely many analytic point blowups and coordinate changes. -/
theorem hasFiniteSmoothBlowupChain_of_irreducible
    (f : Germ 2) (hf : Irreducible f) : HasFiniteSmoothBlowupChain f := by
  obtain ⟨m, hm, hnext⟩ := exists_exact_maximalIdeal_order f hf.ne_zero
  obtain ⟨e, he⟩ := exists_linear_equiv_regularInFirstCoordinateOfOrder hm hnext
  apply HasFiniteSmoothBlowupChain.source f e
  apply hasFiniteSmoothBlowupChain_of_irreducible_regular m _
  · exact (MulEquiv.irreducible_iff e.pullbackRingEquiv.toMulEquiv).mpr hf
  · exact e.forward.pullback_mem_maximalIdeal_pow hm
  · exact (e.pullback_mem_maximalIdeal_pow_iff f).not.mpr hnext
  · exact he

end OnLeConjecture.Analytic.Germ

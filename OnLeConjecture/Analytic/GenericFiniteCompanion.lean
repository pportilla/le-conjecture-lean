/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericFiniteGermFamilyChoice
public import OnLeConjecture.Analytic.PlaneFiniteColengthCriterion
public import OnLeConjecture.Analytic.RawWeakBlowupPointBasis

/-!
# Generic companion members with finite analytic intersections

A finite-colength ideal of plane analytic germs has a generator not
divisible by any prescribed nonunit germ. For finitely many nonzero
curve equations, avoiding their finitely many irreducible factors
therefore imposes only finitely many proper linear conditions on the
companion coefficients. Their complement is open and meets every
nonempty open coefficient set.

The construction applies simultaneously at every vertex of an actual
weak-blowup tree. It proves finiteness of the local intersections and
constructs a companion with the exact ideal orders. It does not assert
the intersection sum-of-squares formula.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- Finite colength excludes a common nonunit divisor of all generators. -/
theorem exists_generator_not_dvd_of_finite_colength
    {ι : Type*} (F : ι → Germ 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F)))
    (p : Germ 2) (hp : ¬ IsUnit p) : ∃ i, ¬ p ∣ F i := by
  by_contra hnot
  push Not at hnot
  have hpmem : p ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    by_contra hvalue
    exact hp (isUnit_of_valueRingHom_ne_zero hvalue)
  obtain ⟨N, hN⟩ :=
    (quotient_moduleFinite_iff_exists_maximalIdeal_pow_le (Ideal.span (Set.range F))).mp hfinite
  apply not_maximalIdeal_pow_le_span_singleton p hpmem
  refine ⟨N, hN.trans ?_⟩
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Ideal.mem_span_singleton.mpr (hnot i)

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ UniqueFactorizationMonoid

/-- One nonempty open coefficient set gives finite intersections with
every specified nonzero curve, for finitely many finite-colength ideals. -/
theorem exists_open_finite_companion_linear_combinations
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (f : κ → Germ 2) (hf : ∀ k, f k ≠ 0) (F : κ → ι → Germ 2)
    (hfinite : ∀ k, Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range (F k))))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V, ∀ k, PlaneCurve.HasFiniteIntersection (f k) (germLinearCombination (F k) q) := by
  classical
  let := Fintype.ofFinite κ
  let Factors := Σ k : κ, (factors (f k)).toFinset
  let bad : Factors → Submodule ℂ (ι → ℂ) := fun r =>
    ((Ideal.span {r.2.val}).restrictScalars ℂ).comap (germLinearCombination (F r.1))
  have hbad (r : Factors) : bad r ≠ ⊤ := by
    have hp : Irreducible r.2.val := irreducible_of_factor _
      (Multiset.mem_toFinset.mp r.2.property)
    obtain ⟨i, hi⟩ := exists_generator_not_dvd_of_finite_colength (F r.1)
      (hfinite r.1) r.2.val hp.not_isUnit
    intro hz
    have hmem : Pi.single i (1 : ℂ) ∈ bad r := by rw [hz]; trivial
    change germLinearCombination (F r.1) (Pi.single i 1) ∈ Ideal.span {r.2.val} at hmem
    rw [germLinearCombination_single] at hmem
    exact hi (Ideal.mem_span_singleton.mp hmem)
  let V : Set (ι → ℂ) := U ∩ {q | ∀ r, q ∉ bad r}
  have hVopen : IsOpen V := by
    apply hU.inter
    have hset : {q : ι → ℂ | ∀ r, q ∉ bad r} = ⋂ r, (bad r : Set (ι → ℂ))ᶜ := by
      ext q
      simp
    rw [hset]
    apply isOpen_iInter_of_finite
    intro r
    exact (bad r).closed_of_finiteDimensional.isOpen_compl
  have hVne : V.Nonempty := by
    obtain ⟨q, hqU, hq⟩ := exists_coefficients_avoiding_submodules_mem_open
      bad hbad U hU hUne
    exact ⟨q, hqU, hq⟩
  refine ⟨V, hVopen, hVne, fun _ h => h.1, ?_⟩
  intro q hq k
  apply PlaneCurve.hasFiniteIntersection_of_no_common_prime_divisor _ _ (hf k)
  rintro p hp ⟨hpf, hpq⟩
  obtain ⟨r, hr, hpr⟩ := exists_mem_factors_of_dvd (hf k) hp.irreducible hpf
  let index : Factors := ⟨k, r, Multiset.mem_toFinset.mpr hr⟩
  apply hq.2 index
  change germLinearCombination (F k) q ∈ Ideal.span {r}
  exact Ideal.mem_span_singleton.mpr (hpr.dvd_iff_dvd_left.mp hpq)

namespace RawProjectiveWeakBlowupTree

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

omit [Fintype ι] in
/-- Every recorded vertex retains the finite-colength weak ideal. -/
theorem generators_finite_colength (T : RawProjectiveWeakBlowupTree F) :
    ∀ p, Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range (T.generators p))) := by
  induction T with
  | node F m hm horder hexact hfinite points hcard hcomplete children ih =>
      intro p
      cases p with
      | inl p =>
          rw [RawProjectiveWeakBlowupTree.generators]
          exact hfinite
      | inr p =>
          rw [RawProjectiveWeakBlowupTree.generators]
          exact ih p.1 p.2

/-- An exact-order member has finite intersection with all companions
in one nonempty open coefficient set, simultaneously at every vertex. -/
theorem exists_open_finite_companion
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ r ∈ V, ∀ p, PlaneCurve.HasFiniteIntersection
        (germLinearCombination (T.generators p) q)
        (germLinearCombination (T.generators p) r) := by
  apply exists_open_finite_companion_linear_combinations
    (fun p => germLinearCombination (T.generators p) q) _ T.generators
    T.generators_finite_colength U hU hUne
  intro p hz
  apply hq p
  rw [hz]
  exact Ideal.zero_mem _

/-- A companion can have both finite intersections with the chosen
member and the exact weak-ideal order at every recorded center. -/
theorem exists_exact_finite_companion
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ r ∈ U, (∀ p, germLinearCombination (T.generators p) r ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) ∧
      ∀ p, PlaneCurve.HasFiniteIntersection
        (germLinearCombination (T.generators p) q)
        (germLinearCombination (T.generators p) r) := by
  obtain ⟨V, hVopen, hVne, hVU, hV⟩ := T.exists_open_finite_companion q hq U hU hUne
  obtain ⟨r, hrV, hr⟩ := T.exists_exact_coefficients V hVopen hVne
  exact ⟨r, hVU hrV, hr, hV r hrV⟩

end RawProjectiveWeakBlowupTree

end OnLeConjecture.Analytic

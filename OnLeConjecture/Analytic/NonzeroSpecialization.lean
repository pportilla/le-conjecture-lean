/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Domain

/-!
# Nearby nonzero values of analytic germs

A nonzero analytic germ has a representative that is nonzero arbitrarily
close to the origin. A finite collection of nonzero germs has simultaneous
nonzero values arbitrarily close to the origin.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

namespace Germ

/-- A function representing a nonzero analytic germ is nonzero arbitrarily
close to the origin. -/
theorem frequently_ne_zero_of_ofFunction_ne_zero
    {n : ℕ} (F : Source n → ℂ) (hF : AnalyticAt ℂ F 0)
    (hne : Germ.ofFunction F hF ≠ 0) :
    ∃ᶠ z in 𝓝 (0 : Source n), F z ≠ 0 := by
  rw [Filter.Frequently]
  intro heventual
  apply hne
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [heventual] with z hz
  simpa only [not_ne_iff] using hz

/-- Representatives of finitely many nonzero analytic germs are
simultaneously nonzero arbitrarily close to the origin. -/
theorem frequently_forall_ne_zero_of_finite
    {n : ℕ} {ι : Type*} [Finite ι]
    (g : ι → Germ n) (F : ι → Source n → ℂ)
    (hF : ∀ i, AnalyticAt ℂ (F i) 0)
    (hrepresentative : ∀ i, g i = Germ.ofFunction (F i) (hF i))
    (hne : ∀ i, g i ≠ 0) :
    ∃ᶠ z in 𝓝 (0 : Source n), ∀ i, F i z ≠ 0 := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let productFunction : Source n → ℂ := fun z => ∏ i, F i z
  have hproductAnalytic : AnalyticAt ℂ productFunction 0 := by
    change AnalyticAt ℂ (fun z => ∏ i, F i z) 0
    exact Finset.univ.analyticAt_fun_prod fun i _ => hF i
  have hproductGerm : (∏ i, g i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  have hproductRepresentative :
      (∏ i, g i) = Germ.ofFunction productFunction hproductAnalytic := by
    rw [Finset.prod_congr rfl fun i _ => hrepresentative i]
    have hofProduct (s : Finset ι) :
        (∏ i ∈ s, Germ.ofFunction (F i) (hF i)) =
          Germ.ofFunction (fun z => ∏ i ∈ s, F i z)
            (s.analyticAt_fun_prod fun i _ => hF i) := by
      induction s using Finset.induction_on with
      | empty =>
          apply Subtype.ext
          rfl
      | @insert i s hi ih =>
          rw [Finset.prod_insert hi, ih]
          let htail : AnalyticAt ℂ (fun z => ∏ j ∈ s, F j z) 0 :=
            s.analyticAt_fun_prod fun j _ => hF j
          let hmul : AnalyticAt ℂ
              (fun z => F i z * ∏ j ∈ s, F j z) 0 :=
            (hF i).mul htail
          calc
            Germ.ofFunction (F i) (hF i) *
                Germ.ofFunction (fun z => ∏ j ∈ s, F j z) htail =
              Germ.ofFunction (fun z => F i z * ∏ j ∈ s, F j z)
                hmul := by
                  apply Subtype.ext
                  rfl
            _ = Germ.ofFunction (fun z => ∏ j ∈ insert i s, F j z)
                ((insert i s).analyticAt_fun_prod fun j _ => hF j) := by
                  apply Germ.ofFunction_eq_of_eventuallyEq
                  exact Filter.Eventually.of_forall fun z => by
                    change F i z * (∏ j ∈ s, F j z) =
                      ∏ j ∈ insert i s, F j z
                    rw [Finset.prod_insert hi]
    simpa only [productFunction] using hofProduct Finset.univ
  have hfrequent : ∃ᶠ z in 𝓝 (0 : Source n), productFunction z ≠ 0 :=
    frequently_ne_zero_of_ofFunction_ne_zero productFunction
      hproductAnalytic (hproductRepresentative ▸ hproductGerm)
  apply hfrequent.mono
  intro z hproduct i hzero
  apply hproduct
  exact Finset.prod_eq_zero (Finset.mem_univ i) hzero

/-- Every neighborhood of the origin contains a point where representatives
of finitely many nonzero analytic germs are all nonzero. -/
theorem exists_mem_forall_ne_zero_of_finite
    {n : ℕ} {ι : Type*} [Finite ι]
    (g : ι → Germ n) (F : ι → Source n → ℂ)
    (hF : ∀ i, AnalyticAt ℂ (F i) 0)
    (hrepresentative : ∀ i, g i = Germ.ofFunction (F i) (hF i))
    (hne : ∀ i, g i ≠ 0)
    {s : Set (Source n)} (hs : s ∈ 𝓝 (0 : Source n)) :
    ∃ z ∈ s, ∀ i, F i z ≠ 0 := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have hfrequent := frequently_forall_ne_zero_of_finite
    g F hF hrepresentative hne
  obtain ⟨z, hz, hzs⟩ := (hfrequent.and_eventually hs).exists
  exact ⟨z, hzs, hz⟩

end Germ

end OnLeConjecture.Analytic

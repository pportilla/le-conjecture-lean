/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericTransverseCoordinates
public import OnLeConjecture.Analytic.TransverseTargetCoordinates

/-!
# Generic transverse sections of an exact common Jacobian component

An exact common power of an irreducible Jacobian component determines the
parameter order of constructed transverse sections at every sufficiently
small nonzero point of its parametrization. Representative injectivity,
source coordinates, target coordinate selection, and residual units are
proved during the construction.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- The exact common-minor exponent gives the parameter order of a
locally injective transverse section at every sufficiently small nonzero
point of the specified irreducible curve parametrization. A prescribed
property of the transverse coordinate is retained in the construction. -/
theorem eventually_exists_transverse_section_preserving_coordinate_property
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (S : Set (Source 2)) (hS : S ∈ 𝓝 0) (hinj : InjOn G S)
    (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
    (hp : Irreducible (Germ.ofFunction P hP)) (k : ℕ)
    (hdiv : ∀ i j : Fin 3, Germ.ofFunction P hP ^ k ∣
      jacobian ((PointedMapGerm.ofFunction G hG hG0).1.component i)
        ((PointedMapGerm.ofFunction G hG hG0).1.component j))
    (hexact : ∃ i j : Fin 3, ¬ Germ.ofFunction P hP ^ (k + 1) ∣
      jacobian ((PointedMapGerm.ofFunction G hG hG0).1.component i)
        ((PointedMapGerm.ofFunction G hG hG0).1.component j))
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hker : ∀ h : Germ 2,
      (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom h = 0 ↔ Germ.ofFunction P hP ∣ h)
    (B : Fin 3 → Prop)
    (htrans : ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
      ∃ (hGt : AnalyticAt ℂ G (C t)) (hPt : AnalyticAt ℂ P (C t)),
        P (C t) = 0 ∧ ∃ i : Fin 3, B i ∧
          IsUnit (jacobian ((PointedMapGerm.recenterOfFunction G (C t) hGt).1.component i)
            (Germ.ofFunctionAt P (C t) hPt))) :
    ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
      ∃ (hGt : AnalyticAt ℂ G (C t)) (hPt : AnalyticAt ℂ P (C t))
        (i : Fin 3) (e : PointedEquivGerm 2) (β : PointedMapGerm 1 2),
        B i ∧ P (C t) = 0 ∧
        e.forward.pullbackRingHom ((PointedMapGerm.recenterOfFunction G (C t) hGt).1.component i) =
          coordinate 0 ∧
        e.forward.pullbackRingHom (Germ.ofFunctionAt P (C t) hPt) = coordinate 1 ∧
        (hyperplaneInclusionGerm 2).comp β =
          ((coordinateSwapPointedEquiv i).forward.comp
            (PointedMapGerm.recenterOfFunction G (C t) hGt)).comp
              (e.forward.comp (hyperplaneInclusionGerm 1)) ∧
        β.HasInjectiveRepresentative ∧
        min (vanishingOrder (β.1.component 0)) (vanishingOrder (β.1.component 1)) =
          (k + 1 : ℕ) := by
  let g := PointedMapGerm.ofFunction G hG hG0
  let A (ij : Fin 3 × Fin 3) (y : Source 2) :=
    fderiv ℂ (fun z => G z ij.1) y (coordinateVector 0) *
      fderiv ℂ (fun z => G z ij.2) y (coordinateVector 1) -
    fderiv ℂ (fun z => G z ij.1) y (coordinateVector 1) *
      fderiv ℂ (fun z => G z ij.2) y (coordinateVector 0)
  have hD (i : Fin 3) (j : Fin 2) :
      AnalyticAt ℂ (fun y => fderiv ℂ (fun z => G z i) y (coordinateVector j)) 0 :=
    ((ContinuousLinearMap.apply ℂ ℂ (coordinateVector j)).analyticAt _).comp
      ((analyticAt_pi_iff.mp hG) i).fderiv
  have hA (ij : Fin 3 × Fin 3) : AnalyticAt ℂ (A ij) 0 :=
    ((hD ij.1 0).mul (hD ij.2 1)).sub ((hD ij.1 1).mul (hD ij.2 0))
  have hAeq (ij : Fin 3 × Fin 3) : Germ.ofFunction (A ij) (hA ij) =
      jacobian (g.1.component ij.1) (g.1.component ij.2) := by
    apply Subtype.ext
    rfl
  have hdivA (ij : Fin 3 × Fin 3) :
      Germ.ofFunction P hP ^ k ∣ Germ.ofFunction (A ij) (hA ij) := by
    rw [hAeq]
    exact hdiv ij.1 ij.2
  have hexactA : ∃ ij : Fin 3 × Fin 3,
      ¬ Germ.ofFunction P hP ^ (k + 1) ∣ Germ.ofFunction (A ij) (hA ij) := by
    obtain ⟨i, j, hij⟩ := hexact
    exact ⟨(i, j), by simpa only [hAeq] using hij⟩
  obtain ⟨U, ij, hres⟩ := exists_generic_rebased_common_factor
    P hP A hA k hdivA hexactA C hC hC0 hker
  have hsmooth := eventually_fderiv_ne_zero_along_irreducible_curve P hP hp C hC hC0 hker
  obtain ⟨S₀, hS₀sub, hS₀, hS₀0⟩ := _root_.mem_nhds_iff.mp hS
  have hCt : Tendsto C (𝓝 0) (𝓝 (0 : Source 2)) := by
    simpa only [hC0] using hC.continuousAt.tendsto
  filter_upwards [hres, htrans, hsmooth, hCt.eventually (hS₀.mem_nhds hS₀0)]
    with t htres httrans htsmooth htS htn
  obtain ⟨hGt, hPt, htP0, i, hiB, hi⟩ := httrans htn
  obtain ⟨_, hAt, hUt, hpLocal, hfactor, hunit⟩ := htres htn
  let gLocal := PointedMapGerm.recenterOfFunction G (C t) hGt
  let pLocal := Germ.ofFunctionAt P (C t) hPt
  let R (a b : Fin 3) := Germ.ofFunctionAt (U (a, b)) (C t) (hUt (a, b))
  have hLocalInjective : gLocal.HasInjectiveRepresentative :=
    PointedMapGerm.recenter_hasInjectiveRepresentative G (C t) hGt S₀
      (hS₀.mem_nhds htS) (hinj.mono hS₀sub)
  have hpLocalNe : pLocal ≠ 0 := by
    intro hz
    have h := congrArg Germ.differential hz
    rw [Germ.differential_ofFunctionAt, Germ.differential_zero] at h
    exact htsmooth htn h
  have hR (a b : Fin 3) : jacobian (gLocal.1.component a) (gLocal.1.component b) =
      pLocal ^ k * R a b := by
    obtain ⟨hJ, hJeq⟩ := PointedMapGerm.jacobian_recenterOfFunction_components G (C t) hGt a b
    exact hJeq.trans (hfactor (a, b))
  obtain ⟨e, β, he, hep, hβfactor, hβinj, horder⟩ :=
    gLocal.exists_transverse_section_order_at_component hLocalInjective
      pLocal hpLocal hpLocalNe k R hR ⟨ij.1, ij.2, hunit⟩ i hi
  exact ⟨hGt, hPt, i, e, β, hiB, htP0, he, hep, hβfactor, hβinj, horder⟩

/-- The exact common-minor exponent determines the generic transverse order,
with a target coordinate supplied by finiteness of the map. -/
theorem eventually_exists_injective_transverse_section_of_exact_common_power
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (S : Set (Source 2)) (hS : S ∈ 𝓝 0) (hinj : InjOn G S)
    (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
    (hp : Irreducible (Germ.ofFunction P hP)) (k : ℕ)
    (hdiv : ∀ i j : Fin 3, Germ.ofFunction P hP ^ k ∣
      jacobian ((PointedMapGerm.ofFunction G hG hG0).1.component i)
        ((PointedMapGerm.ofFunction G hG hG0).1.component j))
    (hexact : ∃ i j : Fin 3, ¬ Germ.ofFunction P hP ^ (k + 1) ∣
      jacobian ((PointedMapGerm.ofFunction G hG hG0).1.component i)
        ((PointedMapGerm.ofFunction G hG hG0).1.component j))
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hn : ∃ i, (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom (coordinate i) ≠ 0)
    (hker : ∀ h : Germ 2,
      (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom h = 0 ↔ Germ.ofFunction P hP ∣ h) :
    ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
      ∃ (hGt : AnalyticAt ℂ G (C t)) (hPt : AnalyticAt ℂ P (C t))
        (i : Fin 3) (e : PointedEquivGerm 2) (β : PointedMapGerm 1 2),
        P (C t) = 0 ∧
        e.forward.pullbackRingHom ((PointedMapGerm.recenterOfFunction G (C t) hGt).1.component i) =
          coordinate 0 ∧
        e.forward.pullbackRingHom (Germ.ofFunctionAt P (C t) hPt) = coordinate 1 ∧
        (hyperplaneInclusionGerm 2).comp β =
          ((coordinateSwapPointedEquiv i).forward.comp
            (PointedMapGerm.recenterOfFunction G (C t) hGt)).comp
              (e.forward.comp (hyperplaneInclusionGerm 1)) ∧
        β.HasInjectiveRepresentative ∧
        min (vanishingOrder (β.1.component 0)) (vanishingOrder (β.1.component 1)) =
          (k + 1 : ℕ) := by
  let g := PointedMapGerm.ofFunction G hG hG0
  have hgi : g.HasInjectiveRepresentative := ⟨G, hG, hG0, rfl, S, hS, hinj⟩
  have htrans := g.eventually_exists_rebased_component_curve_jacobian_unit
    (g.injective_isFiniteAtOrigin_two hgi) G hG hG0 rfl P hP hp C hC hC0 hn hker
  have hchoice : ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
      ∃ (hGt : AnalyticAt ℂ G (C t)) (hPt : AnalyticAt ℂ P (C t)),
        P (C t) = 0 ∧ ∃ i : Fin 3, True ∧
          IsUnit (jacobian ((PointedMapGerm.recenterOfFunction G (C t) hGt).1.component i)
            (Germ.ofFunctionAt P (C t) hPt)) := by
    filter_upwards [htrans] with t ht htn
    obtain ⟨hGt, hPt, hP0, i, hi⟩ := ht htn
    exact ⟨hGt, hPt, hP0, i, trivial, hi⟩
  have h := eventually_exists_transverse_section_preserving_coordinate_property
    G hG hG0 S hS hinj P hP hp k hdiv hexact C hC hC0 hker (fun _ => True) hchoice
  filter_upwards [h] with t ht htn
  obtain ⟨hGt, hPt, i, e, β, _, hrest⟩ := ht htn
  exact ⟨hGt, hPt, i, e, β, hrest⟩

end OnLeConjecture.Analytic

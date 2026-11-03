/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import OnLeConjecture.External.TauCeti.Analysis.ODE.GlobalSolution
public import OnLeConjecture.External.TauCeti.Analysis.ODE.SmoothParameterGlobal

/-!
# Smooth dependence of global ODE solutions

This selective port proves joint smooth dependence on the initial point and time.

Source: https://github.com/TauCetiProject/TauCeti/blob/eb4dd2412a1cd62f73128361bfd3cb422df32e37/TauCeti/Analysis/ODE/InitialCondition.lean
Retrieved 2026-10-29. Retain all global smooth-dependence results. Omit the local-vector-field
theorem and its bump-function dependency. Proofs unchanged.
-/

public section

open Filter Set Topology
open scoped ContDiff NNReal

noncomputable section

universe u

namespace ODE

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Time rescaling.** A curve solving the field `v` sped up by the factor `ε` on the unit
interval reaches, at time `1`, the value of the global solution at time `ε`. Only right
derivatives are required, which is the form in which the parameterized Picard theorem delivers
its solutions. -/
private theorem eq_globalSolution_of_smul [CompleteSpace E] (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (x : E) (ε : ℝ) {u : ℝ → E} (hu₀ : u 0 = x)
    (hu : ContinuousOn u (Icc 0 1))
    (hu' : ∀ s ∈ Ico (0 : ℝ) 1, HasDerivWithinAt u (ε • v (u s)) (Ici s) s) :
    u 1 = globalSolution v hv x ε := by
  have hflow : ∀ s : ℝ, HasDerivAt (fun r : ℝ ↦ globalSolution v hv x (ε * r))
      (ε • v (globalSolution v hv x (ε * s))) s := fun s ↦ by
    simpa [Function.comp_def, mul_comm] using
      (hasDerivAt_globalSolution v hv x (ε * s)).scomp s ((hasDerivAt_id s).const_mul ε)
  have heq := ODE_solution_unique (v := fun _ z ↦ ε • v z) (K := ‖ε‖₊ * K)
    (a := 0) (b := 1) (f := u) (g := fun r ↦ globalSolution v hv x (ε * r))
    (fun _ ↦ (lipschitzWith_smul ε).comp hv) hu hu'
    (((continuous_globalSolution_apply v hv x).comp
      (continuous_const.mul continuous_id)).continuousOn)
    (fun s _ ↦ (hflow s).hasDerivWithinAt)
    (by simp [hu₀])
  simpa using heq (right_mem_Icc.2 zero_le_one)

section

variable [CompleteSpace E]

/-- **The global solution of a globally Lipschitz field depends smoothly on time and on its
initial condition**, near time `0`, at the order of the field. -/
theorem contDiffAt_globalSolution {n : ℕ∞} (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    (hvs : ContDiff ℝ (n + 1) v) (a : E) :
    ContDiffAt ℝ (n + 1) (fun p : E × ℝ ↦ globalSolution v hv p.1 p.2) (a, 0) := by
  -- The field of the rescaled equation, with the initial condition and the speed as parameters.
  have hf : ContDiff ℝ (n + 1) fun q : (E × ℝ) × E ↦ q.1.2 • v (q.1.1 + q.2) :=
    ContDiff.smul (contDiff_fst.snd) (hvs.comp (contDiff_fst.fst.add contDiff_snd))
  have hzero : ∀ᶠ y in nhds (0 : E),
      (fun q : (E × ℝ) × E ↦ q.1.2 • v (q.1.1 + q.2)) (((a, (0 : ℝ))), y) = 0 :=
    .of_forall fun y ↦ zero_smul ℝ _
  obtain ⟨γ, U, hU, hp₀U, hγU, -, hprop⟩ :=
    exists_contDiffOn_picard_solution_of_contDiff
      (fun q : (E × ℝ) × E ↦ q.1.2 • v (q.1.1 + q.2)) (a, (0 : ℝ)) (0 : E) hf hzero
  have hγ : ContDiffAt ℝ (n + 1) γ (a, 0) := hγU.contDiffAt (hU.mem_nhds hp₀U)
  have hsmooth : ContDiffAt ℝ (n + 1)
      (fun p : E × ℝ ↦ p.1 + γ p ⟨1, by norm_num⟩) (a, 0) := by
    have := ((ContinuousMap.evalCLM (R := ℝ) (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1)).contDiff
      (n := n + 1)).comp_contDiffAt (a, (0 : ℝ)) hγ
    exact contDiffAt_fst.add (by simpa [Function.comp_def] using this)
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hp₀U] with p hpU
  have hp := hprop p hpU
  obtain ⟨hpicard, -, hright⟩ := hp
  -- The rescaled solution starts at `p.1` and moves with speed `p.2 • v`.
  have hbase : γ p ⟨0, by norm_num⟩ = 0 := by simpa using hpicard ⟨0, by norm_num⟩
  have hcont : ContinuousOn (fun s : ℝ ↦ p.1 + γ p (projIcc 0 1 zero_le_one s)) (Icc 0 1) :=
    Continuous.continuousOn (by fun_prop)
  have hderiv : ∀ s ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun r : ℝ ↦ p.1 + γ p (projIcc 0 1 zero_le_one r))
        (p.2 • v (p.1 + γ p (projIcc 0 1 zero_le_one s))) (Ici s) s :=
    fun s hs ↦ (hright s hs).const_add p.1
  have := eq_globalSolution_of_smul v hv p.1 p.2
    (u := fun s : ℝ ↦ p.1 + γ p (projIcc 0 1 zero_le_one s))
    (by simpa [projIcc_left] using congrArg (fun w : E ↦ p.1 + w) hbase) hcont hderiv
  simpa [projIcc_right] using this.symm

/-- **The global solution of a globally Lipschitz `C^(n+1)` field is `C^(n+1)` jointly in its
initial condition and time.**

For every finite positive regularity order, the global solution has the same joint regularity as
the vector field. -/
theorem contDiff_globalSolution (n : ℕ) (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    (hvs : ContDiff ℝ (n + 1) v) :
    ContDiff ℝ (n + 1) (fun p : E × ℝ ↦ globalSolution v hv p.1 p.2) := by
  -- For a fixed initial condition, the smooth times form a nonempty clopen subset of `ℝ`:
  -- the flow law propagates smoothness locally, including at limit points.
  let G : E × ℝ → E := fun p ↦ globalSolution v hv p.1 p.2
  have hlocal (a : E) : ContDiffAt ℝ (n + 1) G (a, 0) := by
    exact_mod_cast contDiffAt_globalSolution (n := (n : ℕ∞)) v hv (by exact_mod_cast hvs) a
  have hfinite : (n + 1 : ℕ∞) ≠ ∞ := by simp
  have propagate (a : E) {s t : ℝ} (hs : ContDiffAt ℝ (n + 1) G (a, s))
      (hout : ContDiffAt ℝ (n + 1) G (globalSolution v hv a s, t - s)) :
      ContDiffAt ℝ (n + 1) G (a, t) := by
    have hfixed : ContDiffAt ℝ (n + 1) (fun x ↦ globalSolution v hv x s) a :=
      hs.comp a (contDiffAt_id.prodMk contDiffAt_const)
    have hinner : ContDiffAt ℝ (n + 1)
        (fun p : E × ℝ ↦ (globalSolution v hv p.1 s, p.2 - s)) (a, t) :=
      (hfixed.comp (a, t) contDiffAt_fst).prodMk (contDiffAt_snd.sub contDiffAt_const)
    apply (hout.comp (a, t) hinner).congr_of_eventuallyEq
    filter_upwards [] with p
    dsimp only [G, Function.comp_apply]
    rw [← globalSolution_add]
    congr 2
    ring
  apply contDiff_iff_contDiffAt.2
  rintro ⟨a, t⟩
  let S : Set ℝ := {s | ContDiffAt ℝ (n + 1) G (a, s)}
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have houter : ∀ᶠ u in nhds s,
        ContDiffAt ℝ (n + 1) G (globalSolution v hv a s, u - s) := by
      have hevent := (hlocal (globalSolution v hv a s)).eventually hfinite
      have htend : Tendsto (fun u : ℝ ↦ (globalSolution v hv a s, u - s)) (nhds s)
          (nhds (globalSolution v hv a s, 0)) := by
        have hconst : ContinuousAt (fun _ : ℝ ↦ globalSolution v hv a s) s := continuousAt_const
        have hsub : ContinuousAt (fun u : ℝ ↦ u - s) s :=
          continuousAt_id.sub continuousAt_const
        have htend' := hconst.prodMk hsub
        simpa only [ContinuousAt, sub_self] using htend'
      exact htend.eventually hevent
    exact houter.mono fun u hu ↦ propagate a hs hu
  have hclosed : IsClosed S := by
    apply isClosed_of_closure_subset
    intro s hs
    have houter : ∀ᶠ u in nhds s,
        ContDiffAt ℝ (n + 1) G (globalSolution v hv a u, s - u) := by
      have hevent := (hlocal (globalSolution v hv a s)).eventually hfinite
      have htend : Tendsto (fun u ↦ (globalSolution v hv a u, s - u)) (nhds s)
          (nhds (globalSolution v hv a s, 0)) := by
        have hsub : ContinuousAt (fun u : ℝ ↦ s - u) s :=
          continuousAt_const.sub continuousAt_id
        have htend' := (continuous_globalSolution_apply v hv a).continuousAt.prodMk hsub
        simpa only [ContinuousAt, sub_self] using htend'
      exact htend.eventually hevent
    obtain ⟨u, hu⟩ := (mem_closure_iff_nhds').1 hs _ houter
    exact propagate a u.property hu
  have hSuniv : S = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, hlocal a⟩
  have ht : t ∈ S := by
    rw [hSuniv]
    exact Set.mem_univ t
  exact ht

/-- At every fixed time, the global solution of a globally Lipschitz `C^(n+1)` field is a
`C^(n+1)` function of its initial condition. -/
theorem contDiff_globalSolution_apply (n : ℕ) (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    (hvs : ContDiff ℝ (n + 1) v) (t : ℝ) :
    ContDiff ℝ (n + 1) fun x ↦ globalSolution v hv x t :=
  (contDiff_globalSolution n v hv hvs).comp (contDiff_id.prodMk contDiff_const)

end


end ODE

end

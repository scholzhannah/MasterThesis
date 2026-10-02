/-
Copyright (c) 2026 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import CollarNeighbourhoods.PicardLindelofBoundary

/-!
# Existence and uniqueness of solutions to ODEs

This file collects the public-facing existence and uniqueness theorems for solutions to ODEs in
normed spaces.

## Main results

* `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`: the Picard-Lindelöf theorem,
  stating the existence of a local solution to a time-dependent ODE.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`: the
  existence of a local flow that is Lipschitz continuous in the initial point.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`: the existence
  of a local flow `E × ℝ → E` that is continuous on its domain.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`: the existence
  of a local flow to a time-dependent vector field.
* `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`: a `C¹` vector
  field admits solutions on open intervals for all nearby initial points.
* `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`: a `C¹` vector
  field admits a local solution.
* `ContDiffAt.exists_eventually_eq_hasDerivAt`: a `C¹` vector field admits a local flow.
* `ODE_solution_unique` and variants: uniqueness statements for ODE solutions on various intervals.

## Tags

integral curve, vector field, existence, uniqueness, Picard-Lindelöf, Gronwall
-/

@[expose] public section

open Function Metric Set
open scoped Nat NNReal Topology

/-! ## Existence of solutions to ODEs -/

open ODE
namespace IsPicardLindelofWithin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} (h : tmin ≤ tmax) {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}
  {s : Set E} (hx₀ : x₀ ∈ s)

include h hx₀ in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local solution. -/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt
    (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K) :
    ∃ α : ℝ → E, α tmin = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t ∧ α t ∈ s := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next h hf (hx₀ := hx₀)
  refine ⟨α.compProj, by rw [α.compProj_val h (t := ⟨tmin, le_refl _, h⟩),
    ← hα, FunSpace.next_apply₀ h hf ], fun t ht ↦ ⟨?_, ?_⟩⟩
  · apply hasDerivWithinAt_picard_Icc ⟨le_refl _, h⟩ hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ ht' ↦ ⟨α.compProj_mem_closedBall h hf.mul_max_le, α.compProj_mem_set⟩)
      x₀ ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [FunSpace.compProj_of_mem h ht', FunSpace.next_apply]
  · rw [FunSpace.compProj_apply h]
    exact α.range_subset (mem_range_self _)

include h in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local solution. -/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt_of_subset {t : Set E} (hts : t ⊆ s)
    (hx₀ : x₀ ∈ t)
    (hf : IsPicardLindelofWithin f t tmin tmax x₀ a r L K) :
    ∃ α : ℝ → E, α tmin = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t ∧ α t ∈ s := by
  obtain ⟨α, hαx₀, hα⟩ := exists_eq_forall_mem_Icc_hasDerivWithinAt h hx₀ hf
  use α, hαx₀
  intro t ht
  exact ⟨(hα t ht).1, hts (hα t ht).2⟩

include h hx₀ in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. -/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K) :
    ∃ α : ℝ → E, α tmin = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t ∧ α t ∈ s :=
  exists_eq_forall_mem_Icc_hasDerivWithinAt h hx₀ hf

include h in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. -/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt₀_of_subset {t : Set E} (hts : t ⊆ s)
    (hx₀ : x₀ ∈ t)
    (hf : IsPicardLindelofWithin f t tmin tmax x₀ a r L K) :
    ∃ α : ℝ → E, α tmin = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t ∧ α t ∈ s := by
  obtain ⟨α, hαx₀, hα⟩ := exists_eq_forall_mem_Icc_hasDerivWithinAt₀ h hx₀ hf
  use α, hαx₀
  intro t ht
  exact ⟨(hα t ht).1, hts (hα t ht).2⟩

end IsPicardLindelofWithin

/-! ## $C^1$ vector field -/

namespace ContDiffAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → E} {x₀ : E} {s : Set E}


/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x`, where
`x` may be different from `x₀`. -/
theorem exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt
    (hs₁ : Convex ℝ s) (hs₃ : (interior s).Nonempty) (hx₀ : x₀ ∈ s)
    {hfx₀ : inwardPointing ℝ s x₀ (f x₀)} (hf : ContDiffWithinAt ℝ 1 f s x₀) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc t₀ (t₀ + ε), HasDerivWithinAt α (f (α t)) (Icc t₀ (t₀ + ε)) t ∧ α t ∈ s := by
  have ⟨t, hts, htx₀, ε, hε, a, r, _, _, hr, hpl⟩ :=
    IsPicardLindelofWithin.exists_subset_of_contDiffAt_one hs₁ hs₃ hx₀ hfx₀ hf
  refine ⟨ε, hε, ?_⟩
  obtain ⟨α, hα1, hα2⟩ := (hpl t₀).exists_eq_forall_mem_Icc_hasDerivWithinAt_of_subset
    (le_add_of_nonneg_right hε.le) hts htx₀
  refine ⟨α, hα1, fun t ht ↦ ?_⟩
  apply hα2
  exact ht

end ContDiffAt

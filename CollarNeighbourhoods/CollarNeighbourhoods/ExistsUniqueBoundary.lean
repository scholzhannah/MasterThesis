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

namespace IsPicardLindelofWithin

open ODEWithin

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
variable [NormedSpace ℝ E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {x₀ x y : E} {a r L K : ℝ≥0} {s : Set E} {s' : E → Set E}
  (hx₀ : x₀ ∈ s)
  (h : tmin ≤ tmax)

include h hx₀ in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local solution whose initial point `x` may be different from the centre `x₀` of
the closed ball within which the properties of the vector field hold. -/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt
    (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K) (hx : x ∈ closedBall x₀ r ∩ s) :
    ∃ α : ℝ → E, α tmin = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t ∧ α t ∈ s := by
  obtain ⟨α, hα⟩ := FunSpaceWithin.exists_isFixedPt_next h hf hx (hx₀ := hx₀)
  refine ⟨α.compProj, by rw [FunSpaceWithin.compProj_val h (α := α) (t:= ⟨tmin, by simp [h]⟩),
    ← hα, FunSpaceWithin.next_apply₀], fun t ht ↦ ?_⟩
  refine ⟨?_, α.compProj_mem_set h⟩
  apply hasDerivWithinAt_picard_Icc (t₀ := tmin) (by simp [h]) hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn
    (fun _ ht' ↦ ⟨α.compProj_mem_closedBall h hf.mul_max_le, α.compProj_mem_set⟩)
    x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [FunSpaceWithin.compProj_of_mem h ht', FunSpaceWithin.next_apply]

include h hx₀ in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. -/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K) :
    ∃ α : ℝ → E, α tmin = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t ∧ α t ∈ s :=
  exists_eq_forall_mem_Icc_hasDerivWithinAt hx₀ h hf ⟨mem_closedBall_self r.2, hx₀⟩

include h hx₀ in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow and that it is Lipschitz continuous in the initial point. -/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
    (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K) :
    ∃ α : E → ℝ → E, (∀ x ∈ closedBall x₀ r ∩ s, α x tmin = x ∧
      ∀ t ∈ Icc tmin tmax, (HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧ α x t ∈ s) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall x₀ r ∩ s) := by
  classical
  have (x) (hx : x ∈ closedBall x₀ r ∩ s) := FunSpaceWithin.exists_isFixedPt_next
    (hx₀ := hx₀) h hf hx
  choose α hα using this
  set α' := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r ∩ s then
    α x hx |>.compProj else 0 with hα'
  refine ⟨α', fun x hx ↦ ⟨?_, fun t ht ↦ ?_⟩, ?_⟩
  · rw [hα']
    beta_reduce
    rw [dite_eq_left hx, FunSpaceWithin.compProj_val (t := ⟨tmin, by simp [h]⟩),
      ← hα, FunSpaceWithin.next_apply₀]
  · rw [hα']
    beta_reduce
    rw [dite_eq_left hx, FunSpaceWithin.compProj_apply]
    constructor
    · apply hasDerivWithinAt_picard_Icc (t₀ := tmin) (by simp [h]) hf.continuousOn_uncurry
        (α x hx |>.continuous_compProj.continuousOn)
        (fun _ ht' ↦ ⟨(α x hx).compProj_mem_closedBall h hf.mul_max_le, (α x hx).compProj_mem_set⟩)
        x ht |>.congr_of_mem _ ht
      intro t' ht'
      nth_rw 1 [← hα]
      rw [FunSpaceWithin.compProj_of_mem (hx₀ := hx₀) h ht', FunSpaceWithin.next_apply]
    · rw [← FunSpaceWithin.compProj_apply h]
      exact (α x hx).compProj_mem_set h
  · obtain ⟨L', h'⟩ := FunSpaceWithin.exists_forall_closedBall_funSpace_dist_le_mul h hf
    refine ⟨L', fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
    simp_rw [hα']
    rw [dite_eq_left hx, dite_eq_left hy, FunSpaceWithin.compProj_apply,
      FunSpaceWithin.compProj_apply, ← FunSpaceWithin.toContinuousMap_apply_eq_apply,
      ← FunSpaceWithin.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨tmin, by simp [h]⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h' x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)

include h hx₀ in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow and that it is continuous on its domain as a (partial) map `E × ℝ → E`. -/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K) :
    ∃ α : E × ℝ → E, (∀ x ∈ closedBall x₀ r ∩ s, α ⟨x, tmin⟩ = x ∧
      ∀ t ∈ Icc tmin tmax, (HasDerivWithinAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) (Icc tmin tmax) t)
      ∧ α (x, t) ∈ s) ∧ ContinuousOn α ((closedBall x₀ r ∩ s) ×ˢ Icc tmin tmax) := by
  obtain ⟨α, hα1, L', hα2⟩ :=
    hf.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith hx₀ h
  refine ⟨uncurry α, hα1, ?_⟩
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hα2
  exact fun x hx ↦ HasDerivWithinAt.continuousOn (fun t ht ↦ ((hα1 x hx).2 t ht).1)

include h hx₀ in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow. -/
theorem exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
    (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K) :
    ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r ∩ s, α x tmin = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t ∧ α x t ∈ s := by
  obtain ⟨α, hα⟩ :=
    hf.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith hx₀ h
  exact ⟨α, hα.1⟩

end IsPicardLindelofWithin

/-! ## $C^1$ vector field -/

namespace ContDiffWithinAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → E} {x₀ : E} {s : Set E}

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x`, where
`x` may be different from `x₀`. -/
theorem exists_forall_mem_closedBall_exists_eq_forall_mem_Ico_hasDerivAt (hs₁ : Convex ℝ s)
    (hs₂ : IsClosed s) (hs₃ : (interior s).Nonempty) (hx₀ : x₀ ∈ s)
    (hfx₀ : inwardPointing s x₀ (f x₀))
    (hf : ContDiffWithinAt ℝ 1 f s x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r ∩ s, ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Ico t₀ (t₀ + ε), HasDerivWithinAt α (f (α t)) (Icc t₀ (t₀ + ε)) t ∧ α t ∈ s := by
  have ⟨s', ε, hε, a, r, _, _, hr, hpl⟩ :=
    IsPicardLindelofWithin.of_contDiffWithinAt_one hs₁ hs₂ hs₃ hx₀ hfx₀ hf
  refine ⟨r, hr, ε, hε, fun x hx ↦ ?_⟩
  have : t₀ ≤ t₀ + ε := (le_add_iff_nonneg_right t₀).2 hε.le
  obtain ⟨α, hα1, hα2⟩ := (hpl t₀).exists_eq_forall_mem_Icc_hasDerivWithinAt hx₀ this hx
  refine ⟨α, hα1, fun t ht ↦ ?_⟩
  exact hα2 t (Ico_subset_Icc_self ht)

/-- This version shows the existence of a local flow. -/
theorem exists_mem_closedBall_eq_forall_mem_Ico_hasDerivAt (hs₁ : Convex ℝ s)
    (hs₂ : IsClosed s) (hs₃ : (interior s).Nonempty) (hx₀ : x₀ ∈ s)
    (hfx₀ : inwardPointing s x₀ (f x₀))
    (hf : ContDiffWithinAt ℝ 1 f s x₀) (t₀ : ℝ) :
    ∃ r > 0, ∃ ε > 0, ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r ∩ s, α x t₀ = x ∧
      ∀ t ∈ Icc t₀ (t₀ + ε), HasDerivWithinAt (α x) (f (α x t)) (Icc t₀ (t₀ + ε)) t ∧
        α x t ∈ s := by
  have ⟨s', ε, hε, a, r, _, _, hr, hpl⟩ :=
    IsPicardLindelofWithin.of_contDiffWithinAt_one hs₁ hs₂ hs₃ hx₀ hfx₀ hf
  have : t₀ ≤ t₀ + ε := (le_add_iff_nonneg_right t₀).2 hε.le
  obtain ⟨α, hα⟩ := (hpl t₀).exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt hx₀
    this
  use r, hr, ε, hε, α

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x₀`. -/
theorem exists_forall_mem_closedBall_exists_eq_forall_mem_Ico_hasDerivAt₀ (hs₁ : Convex ℝ s)
    (hs₂ : IsClosed s) (hs₃ : (interior s).Nonempty) (hx₀ : x₀ ∈ s)
    (hfx₀ : inwardPointing s x₀ (f x₀))
    (hf : ContDiffWithinAt ℝ 1 f s x₀) (t₀ : ℝ) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ico (t₀) (t₀ + ε), HasDerivWithinAt α (f (α t)) (Icc t₀ (t₀ + ε)) t ∧ α t ∈ s :=
  have ⟨_, hr, ε, hε, H⟩ :=
    exists_forall_mem_closedBall_exists_eq_forall_mem_Ico_hasDerivAt hs₁ hs₂ hs₃ hx₀ hfx₀ hf t₀
  have ⟨α, hα1, hα2⟩ := H x₀ ⟨mem_closedBall_self (le_of_lt hr), hx₀⟩
  ⟨α, hα1, ε, hε, hα2⟩

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x₀`. -/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (hs₃ : (interior s).Nonempty) (hx₀ : x₀ ∈ s)
    (hfx₀ : inwardPointing s x₀ (f x₀))
    (hf : ContDiffWithinAt ℝ 1 f s x₀) (t₀ : ℝ) :
    ∃ r > 0, ∃ ε > 0, ∃ α : E × ℝ → E, (∀ x ∈ closedBall x₀ r ∩ s, α ⟨x, t₀⟩ = x ∧
      ∀ t ∈ Icc t₀ (t₀ + ε), (HasDerivWithinAt (α ⟨x, ·⟩) (f (α ⟨x, t⟩)) (Icc t₀ (t₀ + ε)) t)
      ∧ α (x, t) ∈ s) ∧ ContinuousOn α ((closedBall x₀ r ∩ s) ×ˢ Icc t₀ (t₀ + ε)) := by
  have ⟨s', ε, hε, a, r, _, _, hr, hpl⟩ :=
    IsPicardLindelofWithin.of_contDiffWithinAt_one hs₁ hs₂ hs₃ hx₀ hfx₀ hf
  have : t₀ ≤ t₀ + ε := (le_add_iff_nonneg_right t₀).2 hε.le
  obtain ⟨α, hα⟩ := (hpl t₀).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn hx₀
    this
  use r, hr, ε, hε, α

theorem exists_eventually_eq_hasDerivWithinAt_continuousWithinAt
    (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (hs₃ : (interior s).Nonempty) (hx₀ : x₀ ∈ s)
    (hfx₀ : inwardPointing s x₀ (f x₀))
    (hf : ContDiffWithinAt ℝ 1 f s x₀) (t₀ : ℝ) :
    ∃ α : E × ℝ → E, ∀ᶠ xt in 𝓝[s ×ˢ Ici t₀] ⟨x₀, t₀⟩,
      α ⟨xt.1, t₀⟩ = xt.1 ∧ HasDerivWithinAt (α ⟨xt.1, ·⟩) (f (α xt)) (Ici t₀) xt.2 ∧ α xt ∈ s ∧
      ContinuousWithinAt α (s ×ˢ Ici t₀) xt := by
  have ⟨r, hr, ε, hε, α, hα1,  hα2⟩ :=
    exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn hs₁ hs₂ hs₃ hx₀ hfx₀ hf t₀
  use α
  rw [Filter.eventually_iff_exists_mem]
  use (ball x₀ r ∩ s) ×ˢ Ico t₀ (t₀ + ε)
  constructor
  · refine nhdsWithin_prod ?_ (Ico_mem_nhdsGE (by simp [hε]))
    exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x₀ hr))
      self_mem_nhdsWithin
  · intro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨(hα1 x ⟨ball_subset_closedBall hx.1, hx.2⟩).1, ?_,
      ((hα1 x ⟨ball_subset_closedBall hx.1, hx.2⟩).2 t (Ico_subset_Icc_self ht)).2, ?_⟩
    · apply ((hα1 x ⟨ball_subset_closedBall hx.1, hx.2⟩).2 t (Ico_subset_Icc_self ht)).1.congr_set
      rw [← nhdsWithin_eq_iff_eventuallyEqSet]
      exact nhdsWithin_Icc_eq_nhdsGE' ht.2
    · apply (hα2 (x, t) ⟨⟨ball_subset_closedBall hx.1, hx.2⟩, Ico_subset_Icc_self ht⟩).congr_set
      rw [← nhdsWithin_eq_iff_eventuallyEqSet, nhdsWithin_prod_eq, nhdsWithin_prod_eq]
      have : (𝓝[closedBall x₀ r ∩ s] x).NeBot :=
        nhdsWithin_neBot_of_mem ⟨ball_subset_closedBall hx.1, hx.2⟩
      have : (𝓝[Icc t₀ (t₀ + ε)] t).NeBot := nhdsWithin_neBot_of_mem (Ico_subset_Icc_self ht)
      refine Filter.prod_inj.mpr ⟨?_, nhdsWithin_Icc_eq_nhdsGE' ht.2⟩
      exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds_of_mem hx.1))


-- I'm missing the lemma `exists_eventually_eq_hasDerivAt` which is could do later

end ContDiffWithinAt

/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Winston Yin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.MetricSpace.Contracting
public import CollarNeighbourhoods.IsInwardPointingNew

/-!
# Picard-Lindelöf (Cauchy-Lipschitz) Theorem

We prove the (local) existence of integral curves and flows to time-dependent vector fields.

Let `f : ℝ → E → E` be a time-dependent (local) vector field on a Banach space, and let `t₀ : ℝ`
and `x₀ : E`. If `f` is Lipschitz continuous in `x` within a closed ball around `x₀` of radius
`a ≥ 0` at every `t` and continuous in `t` at every `x`, then there exists a (local) solution
`α : ℝ → E` to the initial value problem `α t₀ = x₀` and `deriv α t = f t (α t)` for all
`t ∈ Icc tmin tmax`, where `L * max (tmax - t₀) (t₀ - tmin) ≤ a`.

We actually prove a more general version of this theorem for the existence of local flows. If there
is some `r ≥ 0` such that `L * max (tmax - t₀) (t₀ - tmin) ≤ a - r`, then for every
`x ∈ closedBall x₀ r`, there exists a (local) solution `α x` with the initial condition `α t₀ = x`.
In other words, there exists a local flow `α : E → ℝ → E` defined on `closedBall x₀ r` and
`Icc tmin tmax`.

The proof relies on demonstrating the existence of a solution `α` to the following integral
equation:
$$\alpha(t) = x_0 + \int_{t_0}^t f(\tau, \alpha(\tau))\,\mathrm{d}\tau.$$
This is done via the contraction mapping theorem, applied to the space of Lipschitz continuous
functions from a closed interval to a Banach space. The needed contraction map is constructed by
repeated applications of the right-hand side of this equation.

## Main definitions and results

* `picard f t₀ x₀ α t`: the Picard iteration, applied to the curve `α`
* `IsPicardLindelof`: the structure holding the assumptions of the Picard-Lindelöf theorem

The public-facing existence theorems stated using the integral curve API are in
`Mathlib.Analysis.ODE.ExistUnique`.

## Implementation notes

* The structure `FunSpace` and theorems within this namespace are implementation details of the
  proof of the Picard-Lindelöf theorem and are not intended to be used outside of this file.
* Some sources, such as Lang, define `FunSpace` as the space of continuous functions from a closed
  interval to a closed ball. We instead define `FunSpace` here as the space of Lipschitz continuous
  functions from a closed interval. This slightly stronger condition allows us to postpone the usage
  of the completeness condition on the space `E` until the application of the contraction mapping
  theorem.
* We have chosen to formalise many of the real constants as `ℝ≥0`, so that the non-negativity of
  certain quantities constructed from them can be shown more easily. When subtraction is involved,
  especially note whether it is the usual subtraction between two reals or the truncated subtraction
  between two non-negative reals.
* In this file, We only prove the existence of a solution. For uniqueness, see
  `IsIntegralCurveOn.eqOn` and related theorems in `Mathlib/Analysis/ODE/ExistUnique.lean`.

## Tags

differential equation, dynamical system, initial value problem, Picard-Lindelöf theorem,
Cauchy-Lipschitz theorem

-/

@[expose] public section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

/-! ## Assumptions of the Picard-Lindelöf theorem-/

-- we might could already fix `tmin` to be `t₀`
structure IsPicardLindelofWithin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) (s : Set E) (tmin tmax : ℝ) (x₀ : E) (a r L K : ℝ≥0) :
    Prop where
  /-- The vector field at any time is Lipschitz with constant `K` within a closed ball. -/
  lipschitzOnWith : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a ∩ s)
  /-- The vector field is continuous in time within a closed ball. -/
  continuousOn : ∀ x ∈ closedBall x₀ a ∩ s, ContinuousOn (f · x) (Icc tmin tmax)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a ∩ s, ‖f t x‖ ≤ L
  /-- The time interval of validity -/
  mul_max_le : L * (tmax - tmin) ≤ a - r
  /-- The set `s` is  convex. -/
  convex : Convex ℝ s
  isClosed : IsClosed s
  /-- The set `s` has nonempty interior. -/
  nonempty_interior : (interior s).Nonempty
  /-- The vector field is inward pointing within a closed ball. -/
  isInwardPointing: ∀ v, (∃ t ∈ Icc tmin tmax, ‖f t x₀ - v‖ ≤ 2 * L * a) →
    inwardPointing ℝ s x₀ v
  norm_sub_le : ∀ t ∈ Icc tmin tmax, ‖f tmin x₀ - f t x₀‖ ≤ L * a
  mem_of_derivableWithinAt : ∀ v, derivableWithinAt ℝ s x₀ v → ‖v‖ ≤ a → (x₀ + v) ∈ s

namespace ODE

/-! ## Integral equation

For any time-dependent vector field `f : ℝ → E → E`, we define an integral equation that is
equivalent to the initial value problem defined by `f`.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {t₀ : ℝ}

/-- The Picard iteration. It will be shown that if `α : ℝ → E` and `picard f t₀ x₀ α` agree on an
interval containing `t₀`, then `α` is a solution to `f` with `α t₀ = x₀` on this interval. -/
noncomputable def picard (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (α : ℝ → E) : ℝ → E :=
  fun t ↦ x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]
lemma picard_apply {x₀ : E} {t : ℝ} : picard f t₀ x₀ α t = x₀ + ∫ τ in t₀..t, f τ (α τ) := rfl

lemma picard_apply₀ {x₀ : E} : picard f t₀ x₀ α t₀ = x₀ := by simp

/-- Given a $C^n$ time-dependent vector field `f` and a $C^n$ curve `α`, the composition `f t (α t)`
is $C^n$ in `t`. -/
lemma contDiffOn_comp {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) (s ×ˢ u))
    (hα : ContDiffOn ℝ n α s) (hmem : ∀ t ∈ s, α t ∈ u) :
    ContDiffOn ℝ n (fun t ↦ f t (α t)) s := by
  simpa only [← uncurry_apply_pair f] using! hf.comp (by fun_prop) (by tauto)

/-- Given a continuous time-dependent vector field `f` and a continuous curve `α`, the composition
`f t (α t)` is continuous in `t`. -/
lemma continuousOn_comp
    (hf : ContinuousOn (uncurry f) (s ×ˢ u)) (hα : ContinuousOn α s) (hmem : MapsTo α s u) :
    ContinuousOn (fun t ↦ f t (α t)) s :=
  contDiffOn_zero.mp <| (contDiffOn_comp (contDiffOn_zero.mpr hf) (contDiffOn_zero.mpr hα) hmem)

end

/-! ## Space of Lipschitz functions on a closed interval

We define the space of Lipschitz continuous functions from a closed interval. This will be shown to
be a complete metric space on which `picard` is a contracting map, leading to a fixed point that
will serve as the solution to the ODE. The domain is a closed interval in order to easily inherit
the sup metric from continuous maps on compact spaces. We cannot use functions `ℝ → E` with junk
values outside the domain, as the supremum within a closed interval will only be a pseudo-metric,
and the contracting map will fail to have a fixed point. In order to accommodate flows, we do not
require a specific initial condition. Rather, `FunSpace` contains curves whose initial condition is
within a closed ball.
-/

/-- The space of `L`-Lipschitz functions `α : Icc tmin tmax → E` -/
structure FunSpace {E : Type*} [NormedAddCommGroup E] (s : Set E)
    (tmin tmax : ℝ) (x₀ : E) (hx₀ : x₀ ∈ s) (h : tmin ≤ tmax) (r L : ℝ≥0) where
  /-- The domain is `Icc tmin tmax`. -/
  toFun : Icc tmin tmax → E
  lipschitzWith : LipschitzWith L toFun
  mem_closedBall₀ : toFun ⟨tmin, by simp [h]⟩ ∈ closedBall x₀ r
  range_subset : range toFun ⊆ s


namespace FunSpace

variable {E : Type*} [NormedAddCommGroup E]

section

variable {s : Set E} {tmin tmax : ℝ} {x₀ : E} {hx₀ : x₀ ∈ s} {h : tmin ≤ tmax} {a r L : ℝ≥0}

instance : CoeFun (FunSpace s tmin tmax x₀ hx₀ h r L) fun _ ↦ Icc tmin tmax → E := ⟨fun α ↦ α.toFun⟩

@[ext]
lemma ext {α β : FunSpace s tmin tmax x₀ hx₀ h r L} (h : ∀ t, α t = β t) : α = β := by
  cases α; cases β; simp only [mk.injEq]; ext t; exact h t

/-- `FunSpace t₀ x₀ r L` contains the constant map at `x₀`. -/
instance : Inhabited (FunSpace s tmin tmax x₀ hx₀ h r L) :=
  ⟨fun _ ↦ x₀, (LipschitzWith.const _).weaken zero_le, mem_closedBall_self r.2,
    range_subset_iff.2 fun _ ↦ hx₀⟩

protected lemma continuous (α : FunSpace s tmin tmax x₀ hx₀ h L r) : Continuous α :=
  α.lipschitzWith.continuous

/-- The embedding of `FunSpace` into the space of continuous maps -/
def toContinuousMap : FunSpace s tmin tmax x₀ hx₀ h r L ↪ C(Icc tmin tmax, E) :=
  ⟨fun α ↦ ⟨α, α.continuous⟩, fun α β h ↦ by cases α; cases β; simpa using h⟩

@[simp]
lemma toContinuousMap_apply_eq_apply (α : FunSpace s tmin tmax x₀ hx₀ h r L) (t : Icc tmin tmax) :
    α.toContinuousMap t = α t := rfl

/-- When the radius is zero, a curve in `FunSpace` evaluated at `t₀` equals `x₀`. -/
lemma apply_of_zero (α : FunSpace s tmin tmax x₀ hx₀ h 0 L) (h : tmin ≤ tmax) :
    α ⟨tmin, by simp [h]⟩ = x₀ := by
  simpa using α.mem_closedBall₀

/-- The metric between two curves `α` and `β` is the supremum of the metric between `α t` and `β t`
over all `t` in the domain. This is finite when the domain is compact, such as a closed
interval in our case. -/
noncomputable instance : MetricSpace (FunSpace s tmin tmax x₀ hx₀ h r L) :=
  MetricSpace.induced toContinuousMap toContinuousMap.injective inferInstance

lemma isUniformInducing_toContinuousMap :
    IsUniformInducing fun α : FunSpace s tmin tmax x₀ hx₀ h r L ↦ α.toContinuousMap := ⟨rfl⟩

lemma range_toContinuousMap :
    range (fun α : FunSpace s tmin tmax x₀ hx₀ h r L ↦ α.toContinuousMap) =
      { α : C(Icc tmin tmax, E) | LipschitzWith L α ∧ α ⟨tmin, by simp [h]⟩ ∈ closedBall x₀ r ∧
        range α ⊆ s } := by
  ext α
  constructor
  · rintro ⟨⟨α, hα1, hα2, hα3⟩, rfl⟩
    exact ⟨hα1, hα2, hα3⟩
  · rintro ⟨hα1, hα2, hα3⟩
    exact ⟨⟨α, hα1, hα2, hα3⟩, rfl⟩

lemma isClosed_range_subset_of_isClosed {α : Type*} [TopologicalSpace α] [SequentialSpace C(α, E)]
      (s : Set E) (hs : IsClosed s) :
    IsClosed {f : C(α, E) | range f ⊆ s} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  simp only [subset_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff, mem_ofPred_eq]
  intro a
  rw [← isSeqClosed_iff_isClosed] at hs
  apply hs (x := fun n ↦ f n a) fun n ↦ hf n ( mem_range_self _)
  exact hfg.eval_const a

/-- We show that `FunSpace` is complete in order to apply the contraction mapping theorem. -/
theorem completeSpaceFunSpace [CompleteSpace E] (hs : IsClosed s) :
    CompleteSpace (FunSpace s tmin tmax x₀ hx₀ h r L) := by
  rw [completeSpace_iff_isComplete_range isUniformInducing_toContinuousMap]
  apply IsClosed.isComplete
  rw [range_toContinuousMap, ofPred_and]
  apply isClosed_setOfPred_lipschitzWith L |>.preimage continuous_coeFun |>.inter
  apply IsClosed.and ?_ <| isClosed_range_subset_of_isClosed _ hs
  simp_rw [mem_closedBall_iff_norm]
  exact isClosed_le (by fun_prop) (by fun_prop)

variable (h : tmin ≤ tmax)

/-- Extend the domain of `α` from `Icc tmin tmax` to `ℝ` such that `α t = α tmin` for all `t ≤ tmin`
and `α t = α tmax` for all `t ≥ tmax`. -/
noncomputable def compProj (α : FunSpace s tmin tmax x₀ hx₀ h r L) (t : ℝ) : E :=
  α <| projIcc tmin tmax h t

@[simp]
lemma compProj_apply {α : FunSpace s tmin tmax x₀ hx₀ h r L} {t : ℝ} :
    α.compProj h t = α (projIcc tmin tmax h t) := rfl

lemma compProj_val {α : FunSpace s tmin tmax x₀ hx₀ h r L} {t : Icc tmin tmax} :
    α.compProj h t = α t := by simp only [compProj_apply, projIcc_val]

lemma compProj_of_mem {α : FunSpace s tmin tmax x₀ hx₀ h r L} {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    α.compProj h t = α ⟨t, ht⟩ := by rw [compProj_apply, projIcc_of_mem]

@[continuity, fun_prop]
lemma continuous_compProj (α : FunSpace s tmin tmax x₀ hx₀ h r L) : Continuous (α.compProj h) :=
  α.continuous.comp continuous_projIcc

/-- The image of a function in `FunSpace` is contained within a closed ball. -/
protected lemma mem_closedBall' (α : Icc tmin tmax → E) (hα : LipschitzWith L α)
    (hαr : α ⟨tmin, by simp [h]⟩ ∈ closedBall x₀ r)
    (h' : L * (tmax - tmin) ≤ a - r)
    {t : Icc tmin tmax} :
    α t ∈ closedBall x₀ a := by
  rw [mem_closedBall, dist_eq_norm]
  have : tmin ∈ Icc tmin tmax := by simp [le_trans t.2.1 t.2.2]
  calc
    ‖α t - x₀‖ ≤ ‖α t - α ⟨tmin, this⟩‖ + ‖α ⟨tmin, this⟩ - x₀‖ :=
      norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ L * |t.1 - tmin| + r := by
      apply add_le_add _ <| mem_closedBall_iff_norm.mp <| hαr
      rw [← dist_eq_norm]
      exact hα.dist_le_mul _ _
    _ ≤ L * (tmax - tmin) + r := by
      gcongr
      rw [abs_of_nonneg (by simp [t.2.1]), sub_le_sub_iff_right tmin]
      exact t.2.2
    _ ≤ a - r + r := by gcongr
    _ = a := sub_add_cancel _ _

/-- The image of a function in `FunSpace` is contained within a closed ball. -/
protected lemma mem_closedBall (α : FunSpace s tmin tmax x₀ hx₀ h r L)
    (h' : L * (tmax - tmin) ≤ a - r)
    {t : Icc tmin tmax} :
    α t ∈ closedBall x₀ a :=
  ODE.FunSpace.mem_closedBall' h  _ α.lipschitzWith α.mem_closedBall₀ h'

lemma compProj_mem_closedBall
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) (h' : L * (tmax - tmin) ≤ a - r) {t : ℝ} :
    α.compProj h t ∈ closedBall x₀ a :=
  α.mem_closedBall h h'

lemma compProj_mem_set
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) {t : ℝ} :
    α.compProj h t ∈ s :=
  α.range_subset <| mem_range_self _

end

/-! ## Contracting map on the space of Lipschitz functions -/

section

variable [NormedSpace ℝ E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {x₀ x y : E} {a r L K : ℝ≥0} {s : Set E} {hx₀ : x₀ ∈ s}
  (h : tmin ≤ tmax)

/-- The integrand in `next` is continuous. -/
lemma continuousOn_comp_compProj (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) :
    ContinuousOn (fun t' ↦ f t' (α.compProj h t')) (Icc tmin tmax) :=
  continuousOn_comp
    (continuousOn_prod_of_continuousOn_lipschitzOnWith' (uncurry f) K hf.lipschitzOnWith
      hf.continuousOn)
    (α.continuous_compProj h).continuousOn
    fun _ _ ↦ ⟨compProj_mem_closedBall h α hf.mul_max_le, compProj_mem_set h α⟩

/-- The integrand in `next` is integrable. -/
lemma intervalIntegrable_comp_compProj (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) (t : Icc tmin tmax) :
    IntervalIntegrable (fun t' ↦ f t' (α.compProj h t')) volume tmin t := by
  apply ContinuousOn.intervalIntegrable
  apply α.continuousOn_comp_compProj h hf |>.mono
  exact uIcc_subset_Icc (left_mem_Icc.mpr h) t.2

lemma lipschitzWith_picard (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) :
    LipschitzWith L (fun t ↦ picard f tmin x₀ (compProj h α) t : Icc tmin tmax → _) :=
  LipschitzWith.of_dist_le_mul fun t₁ t₂ ↦ by
    rw [dist_eq_norm, picard_apply, picard_apply, add_sub_add_left_eq_sub,
      integral_interval_sub_left (intervalIntegrable_comp_compProj h hf _ t₁)
        (intervalIntegrable_comp_compProj h hf _ t₂), Subtype.dist_eq, Real.dist_eq]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    -- Can `grind` do this in the future?
    have ht : t ∈ Icc tmin tmax := subset_trans uIoc_subset_uIcc (uIcc_subset_Icc t₂.2 t₁.2) ht
    apply hf.norm_le _ ht
    exact ⟨α.mem_closedBall h hf.mul_max_le, compProj_mem_set h α⟩

/-- The map on `FunSpace` defined by `picard`, some `n`-th iterate of which will be a contracting
map -/
noncomputable def next (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) : FunSpace s tmin tmax x₀ hx₀ h r L where
  toFun t := picard f tmin x₀ α.compProj t
  lipschitzWith := lipschitzWith_picard h hf α
  mem_closedBall₀ := by simp
  range_subset := by
    unfold picard
    rw [range_subset_iff]
    intro t
    -- I only know how to prove this for `x = x₀` but this file reads like this might not be enough
    -- for the existence of local flows...
    apply hf.mem_of_derivableWithinAt (v := ∫ τ in tmin..t, f τ (compProj h α τ))
    · sorry
    · suffices picard f tmin x₀ (compProj h α) t ∈ closedBall x₀ a by simpa
      exact ODE.FunSpace.mem_closedBall' h (picard f tmin x₀ (compProj h α) ∘ Subtype.val)
        (α.lipschitzWith_picard h hf) (by simp) (hf.mul_max_le)

end

end FunSpace

end ODE

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
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.IntervalAverage

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

structure IsPicardLindelofWithin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) (s : Set E) (s' : E → Set E) (tmin tmax : ℝ) (x₀ : E) (a r L K : ℝ≥0) :
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
  convex' : ∀ x ∈ closedBall x₀ r ∩ s, Convex ℝ (s' x)
  mem_set : ∀ x ∈ closedBall x₀ r ∩ s, x ∈ s' x
  /-- The vector field is inward pointing within a closed ball. -/
  isInwardPointing: ∀ v, ∀ x ∈ closedBall x₀ r ∩ s, (∃ t ∈ Icc tmin tmax, ‖f t x₀ - v‖ ≤ K * a) →
    inwardPointing (s' x) x v
  --norm_sub_le : ∀ t ∈ Icc tmin tmax, ‖f tmin x₀ - f t x₀‖ ≤ L * a
  mem_of_derivableWithinAt : ∀ x ∈ closedBall x₀ r ∩ s,
    ∀ v, derivableWithinAt (s' x) x v → ‖v‖ ≤ a → (x + v) ∈ s

namespace ODEWithin

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
structure FunSpaceWithin {E : Type*} [NormedAddCommGroup E] (s : Set E)
    (tmin tmax : ℝ) (x₀ : E) (hx₀ : x₀ ∈ s) (h : tmin ≤ tmax) (r L : ℝ≥0) where
  /-- The domain is `Icc tmin tmax`. -/
  toFun : Icc tmin tmax → E
  lipschitzWith : LipschitzWith L toFun
  mem_closedBall₀ : toFun ⟨tmin, by simp [h]⟩ ∈ closedBall x₀ r
  range_subset : range toFun ⊆ s

namespace FunSpaceWithin

variable {E : Type*} [NormedAddCommGroup E]

section

variable {s : Set E} {tmin tmax : ℝ} {x₀ : E} {hx₀ : x₀ ∈ s} {h : tmin ≤ tmax} {a r L : ℝ≥0}

instance : CoeFun (FunSpaceWithin s tmin tmax x₀ hx₀ h r L) fun _ ↦ Icc tmin tmax → E :=
  ⟨fun α ↦ α.toFun⟩

@[ext]
lemma ext {α β : FunSpaceWithin s tmin tmax x₀ hx₀ h r L} (h : ∀ t, α t = β t) : α = β := by
  cases α; cases β; simp only [mk.injEq]; ext t; exact h t

/-- `FunSpaceWithin t₀ x₀ r L` contains the constant map at `x₀`. -/
instance : Inhabited (FunSpaceWithin s tmin tmax x₀ hx₀ h r L) :=
  ⟨fun _ ↦ x₀, (LipschitzWith.const _).weaken zero_le, mem_closedBall_self r.2,
    range_subset_iff.2 fun _ ↦ hx₀⟩

protected lemma continuous (α : FunSpaceWithin s tmin tmax x₀ hx₀ h L r) : Continuous α :=
  α.lipschitzWith.continuous

/-- The embedding of `FunSpace` into the space of continuous maps -/
def toContinuousMap : FunSpaceWithin s tmin tmax x₀ hx₀ h r L ↪ C(Icc tmin tmax, E) :=
  ⟨fun α ↦ ⟨α, α.continuous⟩, fun α β h ↦ by cases α; cases β; simpa using h⟩

@[simp]
lemma toContinuousMap_apply_eq_apply (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L)
    (t : Icc tmin tmax) : α.toContinuousMap t = α t := rfl

/-- When the radius is zero, a curve in `FunSpace` evaluated at `t₀` equals `x₀`. -/
lemma apply_of_zero (α : FunSpaceWithin s tmin tmax x₀ hx₀ h 0 L) (h : tmin ≤ tmax) :
    α ⟨tmin, by simp [h]⟩ = x₀ := by
  simpa using α.mem_closedBall₀

/-- The metric between two curves `α` and `β` is the supremum of the metric between `α t` and `β t`
over all `t` in the domain. This is finite when the domain is compact, such as a closed
interval in our case. -/
noncomputable instance : MetricSpace (FunSpaceWithin s tmin tmax x₀ hx₀ h r L) :=
  MetricSpace.induced toContinuousMap toContinuousMap.injective inferInstance

lemma isUniformInducing_toContinuousMap :
    IsUniformInducing fun α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L ↦ α.toContinuousMap := ⟨rfl⟩

lemma range_toContinuousMap :
    range (fun α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L ↦ α.toContinuousMap) =
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
theorem completeSpaceFunSpaceWithin [CompleteSpace E] (hs : IsClosed s) :
    CompleteSpace (FunSpaceWithin s tmin tmax x₀ hx₀ h r L) := by
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
noncomputable def compProj (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) (t : ℝ) : E :=
  α <| projIcc tmin tmax h t

@[simp]
lemma compProj_apply {α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L} {t : ℝ} :
    α.compProj h t = α (projIcc tmin tmax h t) := rfl

lemma compProj_val {α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L} {t : Icc tmin tmax} :
    α.compProj h t = α t := by simp only [compProj_apply, projIcc_val]

lemma compProj_of_mem {α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L} {t : ℝ}
    (ht : t ∈ Icc tmin tmax) : α.compProj h t = α ⟨t, ht⟩ := by
  rw [compProj_apply, projIcc_of_mem]

@[continuity, fun_prop]
lemma continuous_compProj (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) :
    Continuous (α.compProj h) :=
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
protected lemma mem_closedBall (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L)
    (h' : L * (tmax - tmin) ≤ a - r)
    {t : Icc tmin tmax} :
    α t ∈ closedBall x₀ a :=
  ODEWithin.FunSpaceWithin.mem_closedBall' h  _ α.lipschitzWith α.mem_closedBall₀ h'

lemma compProj_mem_closedBall
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) (h' : L * (tmax - tmin) ≤ a - r) {t : ℝ} :
    α.compProj h t ∈ closedBall x₀ a :=
  α.mem_closedBall h h'

lemma compProj_mem_set
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) {t : ℝ} :
    α.compProj h t ∈ s :=
  α.range_subset <| mem_range_self _

end

/-! ## Contracting map on the space of Lipschitz functions -/

section

variable [NormedSpace ℝ E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {x₀ x y : E} {a r L K : ℝ≥0} {s : Set E} {s' : E → Set E}
  {hx₀ : x₀ ∈ s}
  (h : tmin ≤ tmax)

/-- The integrand in `next` is continuous. -/
lemma continuousOn_comp_compProj (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) :
    ContinuousOn (fun t' ↦ f t' (α.compProj h t')) (Icc tmin tmax) :=
  continuousOn_comp
    (continuousOn_prod_of_continuousOn_lipschitzOnWith' (uncurry f) K hf.lipschitzOnWith
      hf.continuousOn)
    (α.continuous_compProj h).continuousOn
    fun _ _ ↦ ⟨compProj_mem_closedBall h α hf.mul_max_le, compProj_mem_set h α⟩

/-- The integrand in `next` is integrable. -/
lemma intervalIntegrable_comp_compProj (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) (t : Icc tmin tmax) :
    IntervalIntegrable (fun t' ↦ f t' (α.compProj h t')) volume tmin t := by
  apply ContinuousOn.intervalIntegrable
  apply α.continuousOn_comp_compProj h hf |>.mono
  exact uIcc_subset_Icc (left_mem_Icc.mpr h) t.2

lemma lipschitzWith_picard (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) :
    LipschitzWith L (fun t ↦ picard f tmin x (compProj h α) t : Icc tmin tmax → _) :=
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

lemma mem_derivableCone_compProj (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s)
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) (t : Icc tmin tmax) (t' : ℝ)
    (ht' : t' ∈ Icc tmin t) :
    f t' (compProj h α t') ∈ derivableCone x (hf.convex' x hx) := by
  apply inwardPointing.derivableWithinAt
  apply hf.isInwardPointing _ _ hx
  use t', ⟨ht'.1, ht'.2.trans t.2.2⟩
  have hf' := hf.lipschitzOnWith t' ⟨ht'.1, ht'.2.trans t.2.2⟩
  rw [lipschitzOnWith_iff_norm_sub_le] at hf'
  have h1 : x₀ ∈ closedBall x₀ a ∩ s := by simp [hx₀]
  have h2 : (compProj h α t') ∈ closedBall x₀ a ∩ s :=
    ⟨compProj_mem_closedBall h α hf.mul_max_le, compProj_mem_set h α⟩
  specialize hf' h1 h2
  apply hf'.trans
  apply mul_le_mul_of_nonneg_left ?_ K.2
  rw [← mem_closedBall_iff_norm']
  exact h2.1

variable [CompleteSpace E]

lemma range_picard_subset (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s)
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) :
    (range fun (t : (Icc tmin tmax)) ↦ picard f tmin x (compProj h α) t) ⊆ s := by
  rw [range_subset_iff]
  intro t
  by_cases ht : t = tmin
  · simp [ht, hx.2]
  apply hf.mem_of_derivableWithinAt x hx
  · rw [← one_smul ℝ (∫ (τ : ℝ) in tmin..t, f τ (compProj h α τ) : E),
      ← GroupWithZero.mul_inv_cancel (t - tmin) (sub_ne_zero.mpr ht), mul_smul,
      ← interval_average_eq, ← mem_derivableCone_iff _ (hf.convex' x hx)]
    apply (derivableCone x (hf.convex' x hx)).smul_mem (by simp [lt_of_le_of_ne t.2.1 (Ne.symm ht)])
    apply (derivableCone x (hf.convex' x hx)).convex.set_average_mem
      (isClosed_derivableCone (hf.convex' x hx) (hf.mem_set x hx))
    · simp [sub_ne_zero.mpr ht]
    · simp
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
      intro y hy
      rw [uIoc_of_le t.2.1] at hy
      rw [SetLike.mem_coe]
      exact mem_derivableCone_compProj h hf hx α t y (Ioc_subset_Icc_self hy)
    · rw [← intervalIntegrable_iff]
      exact intervalIntegrable_comp_compProj h hf α t
  · suffices picard f tmin x (compProj h α) t ∈ closedBall x a by simpa
    exact ODEWithin.FunSpaceWithin.mem_closedBall' h
      (picard f tmin x (compProj h α) ∘ Subtype.val)
      (α.lipschitzWith_picard h hf) (by simp) (hf.mul_max_le)

/-- The map on `FunSpace` defined by `picard`, some `n`-th iterate of which will be a contracting
map -/
noncomputable def next
    (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K) (hx : x ∈ closedBall x₀ r ∩ s)
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) : FunSpaceWithin s tmin tmax x₀ hx₀ h r L where
  toFun t := picard f tmin x α.compProj t
  lipschitzWith := lipschitzWith_picard h hf α
  mem_closedBall₀ := by simp [hx.1]
  range_subset := range_picard_subset h hf hx α

@[simp]
lemma next_apply (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s)
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) {t : Icc tmin tmax} :
    next h hf hx α t = picard f tmin x α.compProj t := rfl

lemma next_apply₀ (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s)
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) : next h hf hx α ⟨tmin, ⟨le_refl _, h⟩⟩ = x := by
  simp

/-- `α` is a fixed point of `next` if and only if it satisfies the integral equation
`α t = x + ∫_{t₀}^t f τ (α τ) dτ` for all `t`. -/
lemma isFixedPt_next_iff (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s)
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) :
    IsFixedPt (next h hf hx) α ↔ ∀ t, α t = picard f tmin x α.compProj t := by
  constructor
  · exact fun hα t ↦ congrArg (· t) hα |>.symm
  · intro h
    ext t
    rw [h, next_apply]

/-- A key step in the inductive case of `dist_iterate_next_apply_le` -/
lemma dist_comp_iterate_next_le (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s)
    (n : ℕ) (t : Icc tmin tmax)
    {α β : FunSpaceWithin s tmin tmax x₀ hx₀ h r L}
    (h' : dist ((next h hf hx)^[n] α t) ((next h hf hx)^[n] β t) ≤
      (K * |t - tmin|) ^ n / n ! * dist α β) :
    dist (f t ((next h hf hx)^[n] α t)) (f t ((next h hf hx)^[n] β t)) ≤
      K ^ (n + 1) * |t - tmin| ^ n / n ! * dist α β :=
  calc
    _ ≤ K * dist ((next h hf hx)^[n] α t) ((next h hf hx)^[n] β t) := by
      apply (hf.lipschitzOnWith t.1 t.2).dist_le_mul
      · exact ⟨(FunSpaceWithin.mem_closedBall h _ hf.mul_max_le), range_subset _ (mem_range_self _)⟩
      · exact ⟨(FunSpaceWithin.mem_closedBall h _ hf.mul_max_le), range_subset _ (mem_range_self _)⟩
    _ ≤ K ^ (n + 1) * |t - tmin| ^ n / n ! * dist α β := by
      rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
      gcongr
      rwa [← mul_pow]

/-- A time-dependent bound on the distance between the `n`-th iterates of `next` on two curves -/
lemma dist_iterate_next_apply_le (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s)
    (α β : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) (n : ℕ) (t : Icc tmin tmax) :
    dist ((next h hf hx)^[n] α t) ((next h hf hx)^[n] β t) ≤
      (K * |t.1 - tmin|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using!
      ContinuousMap.dist_apply_le_dist (f := toContinuousMap α) (g := toContinuousMap β) _
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply,
      next_apply, picard_apply, picard_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (intervalIntegrable_comp_compProj h hf _ t)
        (intervalIntegrable_comp_compProj h hf _ t)]
    calc
      _ ≤ ∫ τ in uIoc tmin t.1, K ^ (n + 1) * |τ - tmin| ^ n / n ! * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro t' ht'
        -- Can `grind` do this in the future?
        have ht' : t' ∈ Icc tmin tmax :=
          subset_trans uIoc_subset_uIcc (uIcc_subset_Icc ⟨le_refl _, h⟩ t.2) ht'
        rw [← dist_eq_norm, compProj_of_mem, compProj_of_mem]
        exact dist_comp_iterate_next_le h hf hx _ ⟨t', ht'⟩ (hn _)
      _ ≤ (K * |t.1 - tmin|) ^ (n + 1) / (n + 1) ! * dist α β := by
        apply le_of_abs_le
        -- critical: `integral_pow_abs_sub_uIoc`
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

/-- The `n`-th iterate of `next` is Lipschitz continuous with respect to `FunSpace`, with constant
$(K \max(t_{\mathrm{max}}, t_{\mathrm{min}})^n / n!$. -/
lemma dist_iterate_next_iterate_next_le (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s)
    (α β : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) (n : ℕ) :
    dist ((next h hf hx)^[n] α) ((next h hf hx)^[n] β) ≤
      (K * (tmax - tmin)) ^ n / n ! * dist α β := by
  rw [← MetricSpace.isometry_induced FunSpaceWithin.toContinuousMap
    FunSpaceWithin.toContinuousMap.injective |>.dist_eq, ContinuousMap.dist_le]
  · intro t
    apply le_trans <| dist_iterate_next_apply_le h hf hx α β n t
    gcongr
    exact abs_sub_le_of_le_of_le t.2.1 t.2.2 (le_refl _) h
  · positivity

/-- Some `n`-th iterate of `next` is a contracting map, and its associated Lipschitz constant is
independent of the initial point. -/
lemma exists_contractingWith_iterate_next (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s) :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C
    ((next h hf hx)^[n] :
      FunSpaceWithin s tmin tmax x₀ hx₀ h r L → FunSpaceWithin s tmin tmax x₀ hx₀ h r L) := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * (tmax - tmin))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have : (0 : ℝ) ≤ (K * (tmax - tmin)) ^ n / n ! := by positivity
  refine ⟨n, ⟨_, this⟩, ?_⟩
  exact ⟨hn, LipschitzWith.of_dist_le_mul fun α β ↦ dist_iterate_next_iterate_next_le h hf hx α β n⟩

/-- The map `next` has a fixed point in the space of curves. This will be used to construct a
solution `α : ℝ → E` to the ODE. -/
lemma exists_isFixedPt_next
    (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s) :
    ∃ α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L, IsFixedPt (next h hf hx) α :=
  have := completeSpaceFunSpaceWithin (tmin := tmin) (tmax := tmax) (hx₀ := hx₀) (r := r) (L := L)
    hf.isClosed
  let ⟨_, _, h'⟩ := exists_contractingWith_iterate_next h hf hx
  ⟨_, h'.isFixedPt_fixedPoint_iterate⟩

/-! ## Lipschitz continuity of the solution with respect to the initial condition

The proof relies on the fact that the repeated application of `next` to any curve `α` converges to
the fixed point of `next`, so it suffices to bound the distance between `α` and `next^[n] α`. Since
there is some `m : ℕ` such that `next^[m]` is a contracting map, it further suffices to bound the
distance between `α` and `next^[m]^[n] α`.
-/

lemma dist_iterate_next_le (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s)
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) (n : ℕ) :
    dist α ((next h hf hx)^[n] α) ≤
      (∑ i ∈ Finset.range n, (K * (tmax - tmin)) ^ i / i !)
        * dist α (next h hf hx α) := by
  nth_rw 1 [← iterate_zero_apply (next h hf hx) α]
  rw [Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i ↦ (next h hf hx)^[i] α)
  intro i hi
  rw [iterate_succ_apply]
  exact dist_iterate_next_iterate_next_le h hf hx _ _ i

lemma dist_iterate_iterate_next_le_of_lipschitzWith
    (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s)
    (α : FunSpaceWithin s tmin tmax x₀ hx₀ h r L) {m : ℕ} {C : ℝ≥0}
    (hm : LipschitzWith C ((next h hf hx)^[m] : FunSpaceWithin s tmin tmax x₀ hx₀ h r L → _))
    (n : ℕ) :
    dist α ((next h hf hx)^[m]^[n] α) ≤
      (∑ i ∈ Finset.range m, (K * (tmax - tmin)) ^ i / i !) *
        (∑ i ∈ Finset.range n, (C : ℝ) ^ i) * dist α (next h hf hx α) := by
  nth_rw 1 [← iterate_zero_apply (next h hf hx) α]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i ↦ (next h hf hx)^[m]^[i] α)
  intro i hi
  rw [iterate_succ_apply]
  apply le_trans <| hm.dist_iterate_succ_le_geometric α i
  rw [mul_assoc, mul_comm ((C : ℝ) ^ i), ← mul_assoc]
  gcongr
  exact dist_iterate_next_le h hf hx α m

namespace IsPicardLindelofWithin

/-! ## Properties of `IsPicardLindelof` -/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {s' : E → Set E}
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-
structure IsPicardLindelofWithin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) (s : Set E) (s' : E → Set E) (tmin tmax : ℝ) (x₀ : E) (a r L K : ℝ≥0) :
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
  convex' : ∀ x ∈ closedBall x₀ r ∩ s, Convex ℝ (s' x)
  mem_set : ∀ x ∈ closedBall x₀ r ∩ s, x ∈ s' x
  /-- The vector field is inward pointing within a closed ball. -/
  isInwardPointing: ∀ v, ∀ x ∈ closedBall x₀ r ∩ s, (∃ t ∈ Icc tmin tmax, ‖f t x₀ - v‖ ≤ K * a) →
    inwardPointing (s' x) x v
  --norm_sub_le : ∀ t ∈ Icc tmin tmax, ‖f tmin x₀ - f t x₀‖ ≤ L * a
  mem_of_derivableWithinAt : ∀ x ∈ closedBall x₀ r ∩ s,
    ∀ v, derivableWithinAt (s' x) x v → ‖v‖ ≤ a → (x + v) ∈ s
-/

lemma of_closedBall_subset (f : ℝ → E → E) (hs₁ : Convex ℝ s) (hs₂ : IsClosed s)
    {tmin tmax : ℝ} {x₀ : E} {a r L K : ℝ≥0} (hr : r > 0)
    (hb : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a ∩ s, ‖f t x‖ ≤ L)
    (hc : ∀ x ∈ closedBall x₀ a ∩ s, ContinuousOn (f · x) (Icc tmin tmax))
    (hl : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a ∩ s))
    (hm : L * (tmax - tmin) ≤ a - r)
    (ha : closedBall x₀ (a + r) ⊆ s) :
    (IsPicardLindelofWithin f s (fun x ↦ closedBall x r) tmin tmax x₀ a r L K) where
  lipschitzOnWith := hl
  continuousOn := hc
  norm_le := hb
  mul_max_le := hm
  convex := hs₁
  isClosed := hs₂
  convex' x _ := convex_closedBall x r
  mem_set _ _ := by simp
  isInwardPointing v x _ _ := by
    refine inwardPointing_of_mem_interior (convex_closedBall x r) ?_ v
    rw [interior_closedBall x (by exact Ne.symm (Std.ne_of_lt hr))]
    simp [hr]
  mem_of_derivableWithinAt := by
    intro x ⟨hx, _⟩ hv hxv hva
    apply ha
    rw [mem_closedBall_iff_norm] at hx ⊢
    grw [add_sub_right_comm, norm_add_le, hx, hva, add_comm]


/-- The special case where the vector field is independent of time -/
lemma of_time_independent (hs₁ : Convex ℝ s) (hs₂ : IsClosed s)
    {f : E → E} {tmin tmax : ℝ} {x₀ : E} {a r L K : ℝ≥0}
    (hs'₁ : ∀ x ∈ closedBall x₀ r ∩ s, Convex ℝ (s' x))
    (hs'₂ : ∀ x ∈ closedBall x₀ r ∩ s, x ∈ s' x)
    (hb : ∀ x ∈ closedBall x₀ a ∩ s, ‖f x‖ ≤ L)
    (hl : LipschitzOnWith K f (closedBall x₀ a ∩ s))
    (hm : L * (tmax - tmin) ≤ a - r)
    (hva : ∀ v, ∀ x ∈ closedBall x₀ r ∩ s, ‖f x₀ - v‖ ≤ K * a → inwardPointing (s' x) x v)
    (hsv : ∀ x ∈ closedBall x₀ r ∩ s,
      ∀ v, derivableWithinAt (s' x) x v → ‖v‖ ≤ a → (x + v) ∈ s) :
    (IsPicardLindelofWithin (fun _ ↦ f) s s' tmin tmax x₀ a r L K) where
  lipschitzOnWith _ _ := hl
  continuousOn _ _ := continuousOn_const
  norm_le _ _ := hb
  mul_max_le := hm
  convex := hs₁
  isClosed := hs₂
  convex' := hs'₁
  mem_set := hs'₂
  isInwardPointing := fun _ _ hx ⟨_, _, hvt⟩ ↦ hva _ _ hx hvt
  --norm_sub_le := sorry
  mem_of_derivableWithinAt := hsv



theorem Metric.continuousWithinAt_iff_le {α : Type u} {β : Type v} [PseudoMetricSpace α]
  [PseudoMetricSpace β] {f : α → β} {a : α} {s : Set α} :
    ContinuousWithinAt f s a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, x ∈ s → dist x a ≤ δ → dist (f x) (f a) ≤ ε := by
  sorry

lemma hiwqiqd (hs₁ : Convex ℝ s) (hs₃ : (interior s).Nonempty)
    {f : E → E} {x₀ : E} (hx₀ : x₀ ∈ s \ interior s) (hfx₀ : inwardPointing s x₀ (f x₀))
    (hf : ContDiffWithinAt ℝ 1 f s x₀) :
    letI r' := coneLength hs₁ hs₃ hx₀.1 hfx₀
    let ε := coneWidth hs₁ hs₃ hx₀.1 hfx₀
    ∃ r > 0, r ≤ ε / 12 ∧ ∀ x ∈ closedBall x₀ r ∩ s, dist (f x₀) (f x) ≤ ε / (r' * 6) := by
  let r' := coneLength hs₁ hs₃ hx₀.1 hfx₀
  have hr : r' > 0 := coneLength_pos hs₁ hs₃ hx₀.1 hfx₀
  let ε := coneWidth hs₁ hs₃ hx₀.1 hfx₀
  have hε : ε > 0 := coneWidth_pos hs₁ hs₃ hx₀.1 hfx₀
  have hε' : ε / (r' * 6) > 0 := div_pos hε (mul_pos hr (by norm_num))
  obtain ⟨r, hr, h⟩ := Metric.continuousWithinAt_iff_le.1 hf.continuousWithinAt (ε / (r' * 6))
      hε'
  use r ⊓ ε / 12
  refine ⟨by simp [hr, hε], inf_le_right, ?_⟩
  intro x ⟨hx1, hx2⟩
  rw [dist_comm]
  rw [mem_closedBall] at hx1
  exact h hx2 (hx1.trans inf_le_left)

lemma hoifpq (hs₁ : Convex ℝ s) (hs₃ : (interior s).Nonempty)
    {f : E → E} {x₀ : E} (hx₀ : x₀ ∈ s \ interior s) (hfx₀ : inwardPointing s x₀ (f x₀))
    (hf : ContDiffWithinAt ℝ 1 f s x₀) {K : ℝ≥0} (hK : K > 0) :
    letI r' := coneLength hs₁ hs₃ hx₀.1 hfx₀
    letI ε := coneWidth hs₁ hs₃ hx₀.1 hfx₀
    ∃ a > 0, ∃ r > 0,
      (∀ v, ∀ x ∈ closedBall x₀ r ∩ s, (‖f x₀ - v‖ ≤ K * a) →
        inwardPointing (coneNhdClose f x r' ε) x v) ∧
      (∀ x ∈ closedBall x₀ r ∩ s, ∀ v, derivableWithinAt (coneNhdClose f x r' ε) x v →
        ‖v‖ ≤ a → (x + v) ∈ s) := by
  let r' := coneLength hs₁ hs₃ hx₀.1 hfx₀
  have hr' : r' > 0 := coneLength_pos hs₁ hs₃ hx₀.1 hfx₀
  let ε := coneWidth hs₁ hs₃ hx₀.1 hfx₀
  have hε : ε > 0 := coneWidth_pos hs₁ hs₃ hx₀.1 hfx₀
  obtain ⟨r, hr, hr1, hr2⟩ := hiwqiqd hs₁ hs₃ hx₀ hfx₀ hf
  obtain ⟨a', ha', has⟩ := mem_coneNhdClose_of_lt_of_not_mem_interior f hs₁ hs₃ hx₀ hfx₀
  let a := ε / (r' * 4 * K) ⊓ a' / 2
  have ha : 0 < a := by simp [a, ha', hε, hr', hK]
  use a, ha, r, hr
  constructor
  · intro v x ⟨hx1, hx2⟩ hvx₀
    apply inwardPointing_of_dist
    · rw [mem_closedBall'] at hx1
      exact hx1.trans hr1
    · exact hr2 _ ⟨hx1, hx2⟩
    · rw [← dist_eq_norm'] at hvx₀
      apply lt_of_le_of_lt hvx₀
      change K * a < ε / (r' * 3)
      rw [← lt_div_iff₀' (by exact hK), div_div]
      apply lt_of_le_of_lt inf_le_left
      rw [mul_right_comm r' 4 ↑K, mul_right_comm _ 3 _ , div_mul_eq_div_div,
        div_mul_eq_div_div _ _ 3,
        div_lt_div_iff_of_pos_left (by simp [hε, hr', hK]) four_pos three_pos]
      norm_num
  · intro x ⟨hx1, hx2⟩ v (hv : derivableWithinAt (coneNhdClose f x r' ε) x v) hva
    refine coneNhdClose_subset f hs₁ hs₃ hx₀.1 hfx₀ hx2 ?_ (hr2 _ ⟨hx1, hx2⟩) ?_
    · rw [mem_closedBall'] at hx1
      apply hx1.trans (hr1.trans ?_)
      rw [div_le_div_iff_of_pos_left (coneWidth_pos hs₁ hs₃ hx₀.left hfx₀) (by norm_num)
        (by norm_num)]
      norm_num
    refine has x ?_ _ hv (lt_of_le_of_lt hva (lt_of_le_of_lt inf_le_right (half_lt_self ha')))
    apply (hr2 x ⟨hx1, hx2⟩).trans
    rw [div_mul_eq_div_mul_one_div, div_mul_eq_div_mul_one_div,
      mul_le_mul_iff_right₀ (div_pos (coneWidth_pos hs₁ hs₃ hx₀.left hfx₀)
      (coneLength_pos hs₁ hs₃ hx₀.left hfx₀))]
    norm_num


/-- A time-independent, continuously differentiable ODE satisfies the hypotheses of the
Picard-Lindelöf theorem. -/
lemma of_contDiffWithinAt_one (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (hs₃ : (interior s).Nonempty)
    {f : E → E} {x₀ : E} (hx₀ : x₀ ∈ s \ interior s) (hfx₀ : inwardPointing s x₀ (f x₀))
    (hf : ContDiffWithinAt ℝ 1 f s x₀) :
    letI r' := coneLength hs₁ hs₃ hx₀.1 hfx₀
    letI ε' := coneWidth hs₁ hs₃ hx₀.1 hfx₀
    ∃ (ε : ℝ) (_ : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < r), ∀ (t₀ : ℝ), IsPicardLindelofWithin
      (fun _ ↦ f) s (fun x ↦ (coneNhdClose f x r' ε')) t₀ (t₀ + ε) x₀ a r L K := by
  let r' := coneLength hs₁ hs₃ hx₀.1 hfx₀
  let ε := coneWidth hs₁ hs₃ hx₀.1 hfx₀
  -- Obtain ball of radius `a` within the domain in which f is `K`-lipschitz
  obtain ⟨K', t, ht, hl'⟩ := hf.exists_lipschitzOnWith hs₁
  let K := K' ⊔ 1
  have hl : LipschitzOnWith K f t := LipschitzOnWith.weaken hl' le_sup_left
  have hK : 0 < (K : ℝ) := NNReal.coe_pos.mpr (lt_max_of_lt_right zero_lt_one)
  obtain ⟨a₁, ha₁ : 0 < a₁, has₁⟩ := Metric.mem_nhdsWithin_iff.mp ht
  obtain ⟨a₂, ha₂, has₂⟩ := Metric.isOpen_iff.1
    (isOpen_interior (s := {w | derivableWithinAt s x₀ w})) (f x₀) hfx₀
  obtain ⟨a₃, ha₃, r₁, hr₁, har₁, har₂⟩ := hoifpq hs₁ hs₃ hx₀ hfx₀ hf hK
  set a := a₁ ⊓ (a₂ / K) ⊓ a₃
  have ha : 0 < a := by
    unfold a
    rw [lt_inf_iff, lt_inf_iff]
    exact ⟨⟨ha₁, (div_pos_iff_of_pos_right hK).2 ha₂⟩, ha₃⟩
  have has : ball x₀ a ∩ s ⊆ t := by
    refine subset_trans (inter_subset_inter_left _ (ball_subset_ball ?_)) has₁
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  set L := K * a + ‖f x₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  let r := r₁ ⊓ a / 2
  have hr : 0 < r := by simp [r, hr₁, ha]
  have hb (x : E) (hx : x ∈ closedBall x₀ (a / 2) ∩ s) : ‖f x‖ ≤ L := by
    rw [hL]
    calc
      ‖f x‖ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x - x₀‖ + ‖f x₀‖ := by
        gcongr
        apply hl.norm_sub_le _ (mem_of_mem_nhdsWithin hx₀ (nhdsWithin_mono _ sdiff_subset ht))
        apply subset_trans _ has hx
        apply inter_subset_inter_left s
        exact closedBall_subset_ball <| half_lt_self ha -- this is where we need `a / 2`
      _ ≤ K * a + ‖f x₀‖ := by
        gcongr
        rw [← mem_closedBall_iff_norm]
        exact closedBall_subset_closedBall (half_le_self (le_of_lt ha)) hx.1
      _ ≤ L := le_add_of_nonneg_right zero_le_one
  let ε := a / L / 2 / 2
  have hε0 : 0 < ε := by positivity
  refine ⟨ε, hε0,
    .mk (a / 2) (half_pos ha).le, (.mk r hr.le) / 2,
    .mk L hL0.le, K, half_pos hr, fun t₀ ↦ ?_⟩
  refine of_time_independent hs₁ hs₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact convex_coneNhdClose f hs₁ hs₃ hx₀.left hfx₀
  · intro x hx
    exact mem_coneNhdClose f hs₁ hs₃ hx₀.left hfx₀
  · intro x hx
    apply hb
    simpa using hx
  · exact hl.mono
      (subset_trans (inter_subset_inter_left _ (closedBall_subset_ball (half_lt_self ha))) has)
  · simp only [NNReal.coe_mk, add_sub_cancel_left, mul_div, mul_div_cancel_left₀ a hL0.ne',
      NNReal.coe_div, NNReal.coe_ofNat, le_sub_iff_add_le, ε]
    suffices r ≤ a / 2 by grw [this, add_halves]
    exact inf_le_right
  · intro v x hx hv
    apply har₁
    · refine ⟨?_, hx.2⟩
      exact closedBall_subset_closedBall ((half_le_self hr.le).trans inf_le_left) hx.1
    · apply hv.trans
      rw [mul_le_mul_iff_right₀ hK]
      exact (half_le_self ha.le).trans inf_le_right
  · intro x hx v hv hva
    refine har₂ x ?_ v hv (hva.trans ((half_le_self ha.le).trans inf_le_right))
    refine ⟨?_, hx.2⟩
    exact closedBall_subset_closedBall ((half_le_self hr.le).trans inf_le_left) hx.1

end

end IsPicardLindelofWithin

end

end FunSpaceWithin

end ODEWithin

/-! ## Existence of solutions to ODEs -/

open ODEWithin

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
variable [NormedSpace ℝ E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {x₀ x y : E} {a r L K : ℝ≥0} {s : Set E} {s' : E → Set E}
  {hx₀ : x₀ ∈ s}
  (h : tmin ≤ tmax)

include h hx₀ in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, integral form. This version shows the existence
of a local solution whose initial point `x` may be different from the centre `x₀` of the closed
ball within which the properties of the vector field hold. -/
theorem exists_eq_forall_mem_Icc_eq_picard
    (hf : IsPicardLindelofWithin f s s' tmin tmax x₀ a r L K)
    (hx : x ∈ closedBall x₀ r ∩ s) :
    ∃ α : ℝ → E, α tmin = x ∧
      ∀ t ∈ Icc tmin tmax, α t = ODEWithin.picard f tmin x α t ∧ α t ∈ s := by
  obtain ⟨α, hα⟩ := FunSpaceWithin.exists_isFixedPt_next h hf (hx₀ := hx₀) hx
  refine ⟨(FunSpaceWithin.next h hf hx α).compProj, by simp, fun t ht ↦ ⟨?_, ?_⟩⟩
  · rw [FunSpaceWithin.compProj_apply, FunSpaceWithin.next_apply, hα, projIcc_of_mem _ ht]
  · rw [FunSpaceWithin.compProj_apply]
    exact (FunSpaceWithin.next h hf hx α).range_subset (mem_range_self _)

end

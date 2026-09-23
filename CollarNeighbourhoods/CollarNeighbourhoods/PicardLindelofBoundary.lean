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
  isInwardPointing: ∀ v, (∃ t ∈ Icc tmin tmax, ‖f t x₀ - v‖ ≤ K * a) →
    inwardPointing ℝ s x₀ v
  --norm_sub_le : ∀ t ∈ Icc tmin tmax, ‖f tmin x₀ - f t x₀‖ ≤ L * a
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

lemma mem_tangentCone_compProj (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) (t : Icc tmin tmax) (x : ℝ) (hx : x ∈ Icc tmin t) :
    f x (compProj h α x) ∈ posTangentConeAt s x₀ := by
  rw [← hf.convex.derivableWithinAt_iff_mem_posTangentConeAt hx₀]
  apply inwardPointing.derivableWithinAt
  apply hf.isInwardPointing
  use x
  refine ⟨⟨hx.1, hx.2.trans t.2.2⟩, ?_⟩
  have hf' := hf.lipschitzOnWith x ⟨hx.1, hx.2.trans t.2.2⟩
  rw [lipschitzOnWith_iff_norm_sub_le] at hf'
  have h1 : x₀ ∈ closedBall x₀ a ∩ s := by simp [hx₀]
  have h2 : (compProj h α x) ∈ closedBall x₀ a ∩ s := by
    constructor
    · apply compProj_mem_closedBall h α hf.mul_max_le
    · exact compProj_mem_set h α
  specialize hf' h1 h2
  apply hf'.trans
  apply mul_le_mul_of_nonneg_left ?_ K.2
  rw [← mem_closedBall_iff_norm']
  exact mem_of_mem_inter_left h2

variable [CompleteSpace E]

/-- The map on `FunSpace` defined by `picard`, some `n`-th iterate of which will be a contracting
map -/
noncomputable def next
    (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) : FunSpace s tmin tmax x₀ hx₀ h r L where
  toFun t := picard f tmin x₀ α.compProj t
  lipschitzWith := lipschitzWith_picard h hf α
  mem_closedBall₀ := by simp
  range_subset := by
    unfold picard
    rw [range_subset_iff]
    intro t
    by_cases ht : t = tmin
    · simp [ht, hx₀]
    apply hf.mem_of_derivableWithinAt (v := ∫ τ in tmin..t, f τ (compProj h α τ))
    · rw [Convex.derivableWithinAt_iff_mem_posTangentConeAt hf.convex hx₀]
      rw [← one_smul ℝ (∫ (τ : ℝ) in tmin..t, f τ (compProj h α τ) : E)]
      rw [← GroupWithZero.mul_inv_cancel (t - tmin) (sub_ne_zero.mpr ht)]
      rw [mul_smul]
      rw [← interval_average_eq]
      apply smul_mem_posTangentCone hf.convex hx₀ (↑t - tmin)
        (lt_of_le_of_ne (sub_nonneg_of_le t.2.1) (sub_ne_zero.mpr ht).symm)
      apply Convex.set_average_mem
      · rw [← ConvexCone.tangentCone_eq hf.convex hx₀]
        exact ConvexCone.convex _
      · rw [← ConvexCone.tangentCone_eq hf.convex hx₀]
        exact isClosed_closure
      · simp [sub_ne_zero.mpr ht]
      · simp
      · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
        intro x hx
        rw [uIoc_of_le t.2.1] at hx
        exact mem_tangentCone_compProj (t.2.1.trans t.2.2) hf α t x (mem_Icc_of_Ioc hx)
      · rw [← intervalIntegrable_iff]
        exact intervalIntegrable_comp_compProj h hf α t
    · suffices picard f tmin x₀ (compProj h α) t ∈ closedBall x₀ a by simpa
      exact ODE.FunSpace.mem_closedBall' h (picard f tmin x₀ (compProj h α) ∘ Subtype.val)
        (α.lipschitzWith_picard h hf) (by simp) (hf.mul_max_le)

@[simp]
lemma next_apply (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) {t : Icc tmin tmax} :
    next h hf α t = picard f tmin x₀ α.compProj t := rfl

lemma next_apply₀ (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) : next h hf α ⟨tmin, ⟨le_refl _, h⟩⟩ = x₀ := by simp

/-- `α` is a fixed point of `next` if and only if it satisfies the integral equation
`α t = x + ∫_{t₀}^t f τ (α τ) dτ` for all `t`. -/
lemma isFixedPt_next_iff (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) :
    IsFixedPt (next h hf) α ↔ ∀ t, α t = picard f tmin x₀ α.compProj t := by
  constructor
  · exact fun hα t ↦ congrArg (· t) hα |>.symm
  · intro h
    ext t
    rw [h, next_apply]

/-- A key step in the inductive case of `dist_iterate_next_apply_le` -/
lemma dist_comp_iterate_next_le (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (n : ℕ) (t : Icc tmin tmax)
    {α β : FunSpace s tmin tmax x₀ hx₀ h r L}
    (h' : dist ((next h hf)^[n] α t) ((next h hf)^[n] β t) ≤
      (K * |t - tmin|) ^ n / n ! * dist α β) :
    dist (f t ((next h hf)^[n] α t)) (f t ((next h hf)^[n] β t)) ≤
      K ^ (n + 1) * |t - tmin| ^ n / n ! * dist α β :=
  calc
    _ ≤ K * dist ((next h hf)^[n] α t) ((next h hf)^[n] β t) := by
      apply (hf.lipschitzOnWith t.1 t.2).dist_le_mul
      · exact ⟨(FunSpace.mem_closedBall h _ hf.mul_max_le), range_subset _ (mem_range_self _)⟩
      · exact ⟨(FunSpace.mem_closedBall h _ hf.mul_max_le), range_subset _ (mem_range_self _)⟩
    _ ≤ K ^ (n + 1) * |t - tmin| ^ n / n ! * dist α β := by
      rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
      gcongr
      rwa [← mul_pow]

/-- A time-dependent bound on the distance between the `n`-th iterates of `next` on two curves -/
lemma dist_iterate_next_apply_le (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α β : FunSpace s tmin tmax x₀ hx₀ h r L) (n : ℕ) (t : Icc tmin tmax) :
    dist ((next h hf)^[n] α t) ((next h hf)^[n] β t) ≤
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
        exact dist_comp_iterate_next_le h hf _ ⟨t', ht'⟩ (hn _)
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
lemma dist_iterate_next_iterate_next_le (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α β : FunSpace s tmin tmax x₀ hx₀ h r L) (n : ℕ) :
    dist ((next h hf)^[n] α) ((next h hf)^[n] β) ≤
      (K * (tmax - tmin)) ^ n / n ! * dist α β := by
  rw [← MetricSpace.isometry_induced FunSpace.toContinuousMap FunSpace.toContinuousMap.injective
    |>.dist_eq, ContinuousMap.dist_le]
  · intro t
    apply le_trans <| dist_iterate_next_apply_le h hf α β n t
    gcongr
    exact abs_sub_le_of_le_of_le t.2.1 t.2.2 (le_refl _) h
  · positivity

/-- Some `n`-th iterate of `next` is a contracting map, and its associated Lipschitz constant is
independent of the initial point. -/
lemma exists_contractingWith_iterate_next (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K) :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C
    ((next h hf)^[n] : FunSpace s tmin tmax x₀ hx₀ h r L → FunSpace s tmin tmax x₀ hx₀ h r L) := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * (tmax - tmin))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have : (0 : ℝ) ≤ (K * (tmax - tmin)) ^ n / n ! := by positivity
  refine ⟨n, ⟨_, this⟩, ?_⟩
  exact ⟨hn, LipschitzWith.of_dist_le_mul fun α β ↦ dist_iterate_next_iterate_next_le h hf α β n⟩

/-- The map `next` has a fixed point in the space of curves. This will be used to construct a
solution `α : ℝ → E` to the ODE. -/
lemma exists_isFixedPt_next
    (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K) :
    ∃ α : FunSpace s tmin tmax x₀ hx₀ h r L, IsFixedPt (next h hf) α :=
  have := completeSpaceFunSpace (tmin := tmin) (tmax := tmax) (hx₀ := hx₀) (r := r) (L := L)
    hf.isClosed
  let ⟨_, _, h'⟩ := exists_contractingWith_iterate_next h hf
  ⟨_, h'.isFixedPt_fixedPoint_iterate⟩


/-! ## Lipschitz continuity of the solution with respect to the initial condition

The proof relies on the fact that the repeated application of `next` to any curve `α` converges to
the fixed point of `next`, so it suffices to bound the distance between `α` and `next^[n] α`. Since
there is some `m : ℕ` such that `next^[m]` is a contracting map, it further suffices to bound the
distance between `α` and `next^[m]^[n] α`.
-/

lemma dist_iterate_next_le (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) (n : ℕ) :
    dist α ((next h hf)^[n] α) ≤
      (∑ i ∈ Finset.range n, (K * (tmax - tmin)) ^ i / i !)
        * dist α (next h hf α) := by
  nth_rw 1 [← iterate_zero_apply (next h hf) α]
  rw [Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i ↦ (next h hf)^[i] α)
  intro i hi
  rw [iterate_succ_apply]
  exact dist_iterate_next_iterate_next_le h hf _ _ i

lemma dist_iterate_iterate_next_le_of_lipschitzWith
    (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (α : FunSpace s tmin tmax x₀ hx₀ h r L) {m : ℕ} {C : ℝ≥0}
    (hm : LipschitzWith C ((next h hf)^[m] : FunSpace s tmin tmax x₀ hx₀ h r L → _)) (n : ℕ) :
    dist α ((next h hf)^[m]^[n] α) ≤
      (∑ i ∈ Finset.range m, (K * (tmax - tmin)) ^ i / i !) *
        (∑ i ∈ Finset.range n, (C : ℝ) ^ i) * dist α (next h hf α) := by
  nth_rw 1 [← iterate_zero_apply (next h hf) α]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply dist_le_range_sum_of_dist_le (f := fun i ↦ (next h hf)^[m]^[i] α)
  intro i hi
  rw [iterate_succ_apply]
  apply le_trans <| hm.dist_iterate_succ_le_geometric α i
  rw [mul_assoc, mul_comm ((C : ℝ) ^ i), ← mul_assoc]
  gcongr
  exact dist_iterate_next_le h hf α m

end

end FunSpace

/-! ## Properties of the integral equation -/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {t₀ tmin tmax : ℝ}

-- TODO: generalise to open sets and `Ici` and `Iic`
/-- If the time-dependent vector field `f` and the curve `α` are continuous, then `f t (α t)` is the
derivative of `picard f t₀ x₀ α`. -/
lemma hasDerivWithinAt_picard_Icc
    (ht₀ : t₀ ∈ Icc tmin tmax)
    (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (picard f t₀ x₀ α) (f t (α t)) (Icc tmin tmax) t := by
  apply HasDerivWithinAt.const_add
  have : Fact (t ∈ Icc tmin tmax) := ⟨ht⟩ -- needed to synthesise `FTCFilter` for `Icc`
  apply intervalIntegral.integral_hasDerivWithinAt_right _ -- need `CompleteSpace E` and `Icc`
    (continuousOn_comp hf hα hmem |>.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
    (continuousOn_comp hf hα hmem _ ht)
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_comp hf hα hmem |>.mono
  exact uIcc_subset_Icc ht₀ ht

/-- Converse of `hasDerivWithinAt_picard_Icc`: if `f` is the derivative along `α`, then `α`
satisfies the integral equation. -/
lemma picard_eq_of_hasDerivAt {t : ℝ}
    (hf : ContinuousOn (uncurry f) ((uIcc t₀ t) ×ˢ u))
    (hα : ∀ t' ∈ uIcc t₀ t, HasDerivWithinAt α (f t' (α t')) (uIcc t₀ t) t')
    (hmap : MapsTo α (uIcc t₀ t) u) :
    picard f t₀ (α t₀) α t = α t := by
  rw [← add_sub_cancel (α t₀) (α t), picard_apply,
    integral_eq_sub_of_hasDeriv_right (HasDerivWithinAt.continuousOn hα) _
      (continuousOn_comp hf (HasDerivWithinAt.continuousOn hα) hmap |>.intervalIntegrable)]
  intro t' ht'
  apply HasDerivAt.hasDerivWithinAt
  exact hα t' (Ioo_subset_Icc_self ht') |>.hasDerivAt <| Icc_mem_nhds ht'.1 ht'.2

/-- If the time-dependent vector field `f` is $C^n$ and the curve `α` is continuous, then
`picard f t₀ x₀ α` is also $C^n$. This version works for `n : ℕ`. -/
lemma contDiffOn_nat_picard_Icc
    (ht₀ : t₀ ∈ Icc tmin tmax) {n : ℕ}
    (hf : ContDiffOn ℝ n (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Icc tmin tmax, α t = picard f t₀ x₀ α t) :
    ContDiffOn ℝ n (picard f t₀ x₀ α) (Icc tmin tmax) := by
  by_cases hlt : tmin < tmax
  · have (t) (ht : t ∈ Icc tmin tmax) :=
      hasDerivWithinAt_picard_Icc ht₀ hf.continuousOn hα hmem x₀ ht
    induction n with
    | zero =>
      simp only [Nat.cast_zero, contDiffOn_zero] at *
      exact HasDerivWithinAt.continuousOn this
    | succ n hn =>
      simp only [Nat.cast_add, Nat.cast_one] at *
      rw [contDiffOn_succ_iff_derivWithin <| uniqueDiffOn_Icc hlt]
      refine ⟨fun t ht ↦ HasDerivWithinAt.differentiableWithinAt (this t ht), by simp, ?_⟩
      apply contDiffOn_comp hf.of_succ (ContDiffOn.congr (hn hf.of_succ) heqon) hmem |>.congr
      intro t ht
      exact HasDerivWithinAt.derivWithin (this t ht) <| (uniqueDiffOn_Icc hlt).uniqueDiffWithinAt ht
  · rw [(subsingleton_Icc_of_ge (not_lt.mp hlt)).eq_singleton_of_mem ht₀]
    intro t ht
    rw [eq_of_mem_singleton ht]
    exact contDiffWithinAt_singleton

/-- If the time-dependent vector field `f` is $C^n$ and the curve `α` is continuous, then
`picard f t₀ x₀ α` is also $C^n$. This version works for `n : ℕ∞`.

TODO: Extend to the analytic `n = ⊤` case. -/
lemma contDiffOn_enat_picard_Icc
    (ht₀ : t₀ ∈ Icc tmin tmax) {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Icc tmin tmax, α t = picard f t₀ x₀ α t) :
    ContDiffOn ℝ n (picard f t₀ x₀ α) (Icc tmin tmax) := by
  induction n with
  | top =>
    rw [contDiffOn_infty] at *
    exact fun k ↦ contDiffOn_nat_picard_Icc ht₀ (hf k) hα hmem x₀ heqon
  | coe n => exact contDiffOn_nat_picard_Icc ht₀ hf hα hmem x₀ heqon

/-- Solutions to ODEs defined by $C^n$ vector fields are also $C^n$. -/
theorem contDiffOn_enat_Icc_of_hasDerivWithinAt {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t)
    (hmem : MapsTo α (Icc tmin tmax) u) :
    ContDiffOn ℝ n α (Icc tmin tmax) := by
  by_cases hlt : tmin < tmax
  · set t₀ := (tmin + tmax) / 2 with h
    have ht₀ : t₀ ∈ Icc tmin tmax := ⟨by linarith, by linarith⟩
    have : ∀ t ∈ Icc tmin tmax, α t = picard f t₀ (α t₀) α t := by
      intro t ht
      have : uIcc t₀ t ⊆ Icc tmin tmax := uIcc_subset_Icc ht₀ ht
      rw [picard_eq_of_hasDerivAt (hf.continuousOn.mono (prod_subset_prod_left this))
        (fun t' ht' ↦ hα t' (this ht') |>.mono this) (hmem.mono_left this)]
    exact contDiffOn_enat_picard_Icc ht₀ hf (HasDerivWithinAt.continuousOn hα) hmem (α t₀) this
      |>.congr this
  · rw [not_lt, le_iff_lt_or_eq] at hlt
    cases hlt with
    | inl h =>
      intro _ ht
      rw [Icc_eq_empty (not_le.mpr h)] at ht
      exfalso
      exact notMem_empty _ ht
    | inr h =>
      rw [h, Icc_self]
      intro _ ht
      rw [eq_of_mem_singleton ht]
      exact contDiffWithinAt_singleton

end

end ODE

namespace IsPicardLindelofWithin

/-! ## Properties of `IsPicardLindelof` -/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

lemma continuousOn_uncurry (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K) :
    ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ (closedBall x₀ a ∩ s)) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K hf.lipschitzOnWith hf.continuousOn

/-- Shrink the Picard-Lindelöf parameters to a smaller ball and time interval. The new radius `a'`
and initial deviation `r'` can be chosen freely as long as `a' ≤ a` and the time constraint
`L * max (tmax' - t₀') (t₀' - tmin') ≤ a' - r'` is satisfied. -/
lemma shrink {f : ℝ → E → E} {tmin tmax tmax' : ℝ}
    {x₀ : E} {a r L K : ℝ≥0} (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (htmax : tmax' ≤ tmax)
    {a' r' : ℝ≥0} (ha : a' ≤ a)
    (htime : L * (tmax' - tmin) ≤ a' - r') :
    --(hta' : ∀ t ∈ Icc tmin tmax', ‖f tmin x₀ - f t x₀‖ ≤ L * a') :
    IsPicardLindelofWithin f s tmin tmax' x₀ a' r' L K where
  lipschitzOnWith t ht := by
    apply (hf.lipschitzOnWith t ⟨ht.1, ht.2.trans htmax⟩).mono
    exact inter_subset_inter_left s (closedBall_subset_closedBall ha)
  continuousOn x hx := by
    apply (hf.continuousOn x (inter_subset_inter_left s (closedBall_subset_closedBall ha) hx)).mono
    exact fun _ ht ↦ ⟨ht.1, ht.2.trans htmax⟩
  norm_le t ht x hx :=
    hf.norm_le t ⟨ht.1, ht.2.trans htmax⟩ x
      (inter_subset_inter_left s (closedBall_subset_closedBall ha) hx)
  mul_max_le := htime
  convex := hf.convex
  isClosed := hf.isClosed
  nonempty_interior := hf.nonempty_interior
  isInwardPointing := by
    intro v ⟨t, ht, htK⟩
    apply hf.isInwardPointing
    use t, ⟨ht.1, ht.2.trans htmax⟩
    apply htK.trans
    exact mul_le_mul_of_nonneg_left ha K.2
  --norm_sub_le := hta'
  mem_of_derivableWithinAt v hv hva' := hf.mem_of_derivableWithinAt _ hv (hva'.trans ha)

/-- `IsPicardLindelof` is preserved when shrinking the time interval. -/
lemma shrink_time {f : ℝ → E → E} {tmin tmax tmax' : ℝ}
    {x₀ : E} {a r L K : ℝ≥0} (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K)
    (htmax : tmax' ≤ tmax) :
    IsPicardLindelofWithin f s tmin tmax' x₀ a r L K := by
  apply hf.shrink htmax (le_refl _)
  · calc L * (tmax' - tmin)
      _ ≤ L * (tmax - tmin) := by gcongr
      _ ≤ a - r := hf.mul_max_le
  --· intro t ht
  --  exact hf.norm_sub_le _ ⟨ht.1, ht.2.trans htmax⟩

/-- The special case where the vector field is independent of time -/
lemma of_time_independent (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (hs₃ : (interior s).Nonempty)
    {f : E → E} {tmin tmax : ℝ} {x₀ : E} {a r L K : ℝ≥0}
    (hb : ∀ x ∈ closedBall x₀ a ∩ s, ‖f x‖ ≤ L)
    (hl : LipschitzOnWith K f (closedBall x₀ a ∩ s))
    (hm : L * (tmax - tmin) ≤ a - r)
    (hva : ∀ (v : E), ‖f x₀ - v‖ ≤ K * a → inwardPointing ℝ s x₀ v)
    (hsv : ∀ (v : E), derivableWithinAt ℝ s x₀ v → ‖v‖ ≤ ↑a → x₀ + v ∈ s) :
    (IsPicardLindelofWithin (fun _ ↦ f) s tmin tmax x₀ a r L K) where
  lipschitzOnWith _ _ := hl
  continuousOn _ _ := continuousOn_const
  norm_le _ _ := hb
  mul_max_le := hm
  convex := hs₁
  isClosed := hs₂
  nonempty_interior := hs₃
  isInwardPointing := fun _ ⟨_, _, hvt⟩ ↦ hva _ hvt
  --norm_sub_le := sorry
  mem_of_derivableWithinAt := hsv

/-- A time-independent, continuously differentiable ODE satisfies the hypotheses of the
Picard-Lindelöf theorem. -/
lemma of_contDiffAt_one (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (hs₃ : (interior s).Nonempty)
    {f : E → E} {x₀ : E} (hx₀ : x₀ ∈ s) (hfx₀ : inwardPointing ℝ s x₀ (f x₀))
    (hf : ContDiffWithinAt ℝ 1 f s x₀)
    (hsv : ∃ ε > 0, ∀ (v : E), derivableWithinAt ℝ s x₀ v → ‖v‖ ≤ ε → x₀ + v ∈ s) :
    ∃ (ε : ℝ) (_ : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < r), ∀ (t₀ : ℝ), IsPicardLindelofWithin
      (fun _ ↦ f) s t₀ (t₀ + ε) x₀ a r L K := by
  -- Obtain ball of radius `a` within the domain in which f is `K`-lipschitz
  obtain ⟨K', t, ht, hl'⟩ := hf.exists_lipschitzOnWith hs₁
  let K := K' ⊔ 1
  have hl : LipschitzOnWith K f t := LipschitzOnWith.weaken hl' le_sup_left
  have hK : 0 < (K : ℝ) := NNReal.coe_pos.mpr (lt_max_of_lt_right zero_lt_one)
  obtain ⟨a₁, ha₁ : 0 < a₁, has₁⟩ := Metric.mem_nhdsWithin_iff.mp ht
  obtain ⟨a₂, ha₂, has₂⟩ := Metric.isOpen_iff.1
    (isOpen_interior (s := {w | derivableWithinAt ℝ s x₀ w})) (f x₀) hfx₀
  obtain ⟨a₃, ha₃, has₃⟩ := hsv
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
  have hb (x : E) (hx : x ∈ closedBall x₀ (a / 2) ∩ s) : ‖f x‖ ≤ L := by
    rw [hL]
    calc
      ‖f x‖ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x - x₀‖ + ‖f x₀‖ := by
        gcongr
        apply hl.norm_sub_le _ (mem_of_mem_nhdsWithin hx₀ ht)
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
    .mk (a / 2) (half_pos ha).le, (.mk (a / 2) (half_pos ha).le) / 2,
    .mk L hL0.le, K, half_pos <| half_pos ha, fun t₀ ↦ ?_⟩
  refine of_time_independent hs₁ hs₂ hs₃ hb ?_ (by simp [ε, field]; norm_num) ?_ ?_
  · exact hl.mono
      (subset_trans (inter_subset_inter_left _ (closedBall_subset_ball (half_lt_self ha))) has)
  · intro v hv
    apply has₂
    rw [mem_ball_iff_norm']
    apply lt_of_le_of_lt hv
    apply lt_of_lt_of_le (mul_lt_mul_of_pos_left (half_lt_self ha) hK)
    rw [← le_div_iff₀' (by exact hK)]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  · intro v hv hva
    exact has₃ _ hv (le_trans hva (le_trans (half_le_self ha.le) (min_le_right _ _)))

end

/-! ## Existence of solutions to ODEs -/

open ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {h : tmin ≤ tmax} {x₀ : E} {a r L K : ℝ≥0}
  {s : Set E} {hx₀ : x₀ ∈ s}

include h hx₀ in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, integral form. This version shows the existence
of a local solution whose initial point `x` may be different from the centre `x₀` of the closed
ball within which the properties of the vector field hold. -/
theorem exists_eq_forall_mem_Icc_eq_picard
    (hf : IsPicardLindelofWithin f s tmin tmax x₀ a r L K) :
    ∃ α : ℝ → E, α tmin = x₀ ∧ ∀ t ∈ Icc tmin tmax, α t = ODE.picard f tmin x₀ α t ∧ α t ∈ s := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next h hf (hx₀ := hx₀)
  refine ⟨(FunSpace.next h hf α).compProj, by simp, fun t ht ↦ ⟨?_, ?_⟩⟩
  · rw [FunSpace.compProj_apply, FunSpace.next_apply, hα, projIcc_of_mem _ ht]
  · rw [FunSpace.compProj_apply]
    exact (FunSpace.next h hf α).range_subset (mem_range_self _)

end IsPicardLindelofWithin

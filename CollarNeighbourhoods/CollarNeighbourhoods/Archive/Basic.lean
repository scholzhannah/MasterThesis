/-
Copyright (c) 2026 Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Scholz
-/
module

public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Header-/

@[expose] public section

open Set Function Filter Module EuclideanSpace
open scoped Topology Manifold ContDiff

section

-- this is how to say that `M` is a topological manifold
variable {M H : Type*} [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]

-- this is how we say that `M` is a smooth manifold
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

-- this is how you say vector field
variable (V : Π (x : M), TangentSpace I x)

-- this is how we say that it is smooth
variable (hV : CMDiff ∞ (T% V))

-- this is how you say boundary of `M`
#check I.boundary M

variable (p : M)

-- this is how to say that `p` is a boundary point
#check I.IsBoundaryPoint p

-- this is how to say tangent space at `p`
#check TangentSpace I p

#check ModelWithCorners ℝ E H

-- We now want to define what it means for this vector field to be inward pointing.

-- I think this is maybe too many things in one to be `Prop` valued

-- since we don't need that `p` is in the boundary, we should probably not include it

-- I think mapping out of ℝ might be too strict?

-- **This is wrong** counteraxample: parabola
def IsInwardPointing {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (γ : ℝ → M) (ε : ℝ) (_ : ε > 0) (_ : CMDiff[Ico 0 ε] ∞ γ),
    γ 0 = p ∧
    (Ioo 0 ε).MapsTo γ (I.interior M) ∧
    HasMFDerivAt[Ici 0] γ (0 : ℝ)
      (((1 : ℝ →L[ℝ] ℝ).smulRight v).comp (NormedSpace.fromTangentSpace 1).toContinuousLinearMap)

-- **Option 1**

def IsRealizable {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (γ : ℝ → M) (ε : ℝ) (_ : ε > 0) (_ : CMDiff[Ico 0 ε] ∞ γ),
    γ 0 = p ∧ HasMFDerivAt[Ici 0] γ (0 : ℝ)
    ((ContinuousLinearMap.toSpanSingleton ℝ v).comp
      (NormedSpace.fromTangentSpace 1).toContinuousLinearMap)

def IsInwardPointingTry2 {p : M} (v : TangentSpace I p) : Prop :=
  v ∈ interior {v | IsRealizable v}

-- **Option 2 - wrong**
-- this also doesn't include things tangent to the boundary or the zero vector
def IsInwardPointingTry3 {p : M} (v : TangentSpace I p) : Prop :=
  ∀ (f : M → ℝ) (_ : CMDiff ∞ f) (_ : ∀ x, 0 ≤ f x) (_ : ∀ x ∈ I.boundary M, f x = 0),
    0 ≤ d% f p v

-- **Option 3 - also wrong**
-- no tangent vector is inward pointing by this
def IsInwardPointingTry4 {p : M} (v : TangentSpace I p) : Prop :=
  ∀ (f : M → ℝ) (_ : CMDiff ∞ f) (_ : ∀ x ∈ I.interior M, 0 < f x)
    (_ : ∀ x ∈ I.boundary M, f x = 0), 0 < d% f p v


-- **Option 4**
def IsInwardPointingTry5 {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (f : M → ℝ) (_ : CMDiff ∞ f) (_ : ∀ x ∈ I.interior M, 0 < f x)
    (_ : ∀ x ∈ I.boundary M, f x = 0), 0 < d% f p v

-- use the script one `mvfderiv I f p X ≥ 0` use %


#check HasMFDerivAt

/-
def IsInwardPointingAlt {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (ε : ℝ) (hε : ε > 0) (γ : Icc 0 ε → M),
    letI :Fact (ε > 0) := ⟨hε⟩
    letI x := (⟨0, left_mem_Icc.2 hε.le⟩ : Icc 0 ε)
    CMDiff ∞ γ ∧
    γ x = p ∧
    ({x}ᶜ : Set (Icc 0 ε)).MapsTo γ (I.interior M) ∧
    -- I don't know how to get it to see through the defeq here
    HasMFDerivAt% γ (x : Icc 0 ε) ((1 : ℝ →L[ℝ] ℝ).smulRight v : TangentSpace (𝓡∂ 1) x →L[ℝ] TangentSpace I (γ x))
-/
-- this is how to get the maximal atlas
#check IsManifold.maximalAtlas I ∞ M

lemma prop541general {M : Type*}
  [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
  [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointing v ↔ ∀ (f) (hf : f ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M),
      (d% (𝓡∂ n) (f p) (mfderiv (𝓡∂ n) _ f p v)).ofLp 0 > 0 := by
  sorry

#check mvfderiv

end

section

variable {n : ℕ} [NeZero n]



lemma DifferentiableWithinAt.lineDerivWithin_eq_fderiv {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {F : Type u_2}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : Type u_3} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → F} (s : Set E) {x v : E}
  (hf : DifferentiableWithinAt 𝕜 f s x) :
    lineDerivWithin 𝕜 f s x v = fderivWithin 𝕜 f s x v :=
  sorry

lemma modelWithCornersEuclideanHalfSpace_apply {p : EuclideanHalfSpace n} : (𝓡∂ n) p = p.val :=
  rfl

lemma modelWithCornersEuclideanHalfSpace_symm_apply {p : EuclideanSpace ℝ (Fin n)} : (𝓡∂ n).symm p =
    ⟨WithLp.toLp 2 (update p 0 (max (p 0) 0)), by simp⟩ :=
  rfl

lemma modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff {p : EuclideanHalfSpace n} :
    (𝓡∂ n).IsBoundaryPoint p ↔ p.val.ofLp 0 = 0 := by
  simp [ModelWithCorners.isBoundaryPoint_iff, range_modelWithCornersEuclideanHalfSpace n,
    modelWithCornersEuclideanHalfSpace_apply, eq_comm]

lemma ModelWithCorners.IsBoundaryPoint.eq_zero_of_modelWithCornersEuclideanHalfSpace {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) : p.val.ofLp 0 = 0 :=
  modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.mp hp

lemma modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) : (𝓡∂ n).symm p.val = p := by
  rw [modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff] at hp
  have : (update p.val.ofLp 0 0) = p.val.ofLp := by
    rw [update_eq_self_iff, hp]
  simp [modelWithCornersEuclideanHalfSpace_symm_apply, this, hp]

lemma modelWithCornersEuclideanHalfSpace_boundary_eq :
    (𝓡∂ n).boundary (EuclideanHalfSpace n) = {p | p.val.ofLp 0 = 0} := by
  simp_rw [← modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff]
  rfl

lemma modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff {p : EuclideanHalfSpace n} :
    (𝓡∂ n).IsInteriorPoint p ↔ p.val.ofLp 0 > 0 := by
  simp [ModelWithCorners.isInteriorPoint_iff, range_modelWithCornersEuclideanHalfSpace n,
    modelWithCornersEuclideanHalfSpace_apply]

lemma modelWithCornersEuclideanHalfSpace_interior_eq :
    (𝓡∂ n).interior (EuclideanHalfSpace n) = {p | 0 < p.val.ofLp 0} := by
  simp_rw [← modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff]
  rfl

lemma modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) :
    HasMFDerivAt[{ x : EuclideanSpace ℝ (Fin n) | 0 ≤ x 0 }] (𝓡∂ n).symm
      (p.val)
      -- this line below isn't type correct at all
      -- I think writing this as the derivative of the model with corners is already the only
      -- sensible way to write this
      (ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) ( p.val))) := by
  refine ⟨(𝓡∂ n).continuousOn_symm.continuousWithinAt
    (by simp [modelWithCornersEuclideanHalfSpace_apply]), ?_⟩
  apply HasFDerivWithinAt.congr (f := id)
  · apply HasFDerivAt.hasFDerivWithinAt
    exact hasFDerivAt_id p.val
  · intro x hx
    simp_all [modelWithCornersEuclideanHalfSpace_symm_apply,
      modelWithCornersEuclideanHalfSpace_apply]
  · rw [modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff] at hp
    have : (update p.val.ofLp 0 0) = p.val.ofLp := by
        rw [update_eq_self_iff, hp]
    simp [modelWithCornersEuclideanHalfSpace_symm_apply, modelWithCornersEuclideanHalfSpace_apply,
      hp, this]

lemma modelWithCornersEuclideanHalfSpace_symm_mDifferentialbleWithinAt {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) :
    MDiffAt[{ x : EuclideanSpace ℝ (Fin n) | 0 ≤ x 0 }] (𝓡∂ n).symm p.val :=
  HasMFDerivWithinAt.mdifferentiableWithinAt
    (modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt hp)

lemma modelWithCornersEuclideanHalfSpace_hasMFDerivWithinAt {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) :
    HasMFDerivAt% (𝓡∂ n)
      p
      (ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ n) p)) := by
  exact (𝓡∂ n).hasMFDerivAt

-- EuclideanSpace ℝ (Fin n)

example : HasFDerivAt (𝕜 := ℝ) (EuclideanSpace.proj 0) (EuclideanSpace.proj 0)
    (0 : EuclideanSpace ℝ (Fin n)) := by
  exact ContinuousLinearMap.hasFDerivAt (PiLp.proj 2 (fun x ↦ ℝ) 0)

--#check (PiLp.proj 2 (fun x ↦ ℝ) 0).contDiff.contMDiff

#check ModelWithCorners.contMDiff

lemma IsRealizable_of_zero_lt {p : EuclideanHalfSpace n} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 < v.ofLp 0) : IsRealizable v := by
  unfold TangentSpace at v
  -- map γ to EuclideanSpace first, then do the NormedSpace.fromTangentSpace
  let γ : ℝ → EuclideanHalfSpace n := (𝓡∂ n).symm ∘ (fun i ↦ p.1 + i • v)
  have hp' := modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.1 hp
  have hγ : CMDiff[Ico 0 1] ∞ γ := by
    unfold γ
    apply (𝓡∂ n).contMDiffOn_symm.comp
    · rw [contMDiffOn_iff_contDiffOn]
      fun_prop
    · intro x hx
      simp_all [range_modelWithCornersEuclideanHalfSpace n]
  use γ, 1, Real.zero_lt_one, hγ
  constructor
  · have : (update p.val.ofLp 0 0) = p.val.ofLp := by
      rw [update_eq_self_iff, hp']
    simp [γ, modelWithCornersEuclideanHalfSpace_symm_apply, hp', this]
  · unfold γ
    change HasMFDerivAt[Ici 0] (↑(𝓡∂ n).symm ∘ fun i ↦ p.val + i • v : ℝ → EuclideanHalfSpace n)
      (0 : ℝ) ((ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n)
      (0 : EuclideanSpace ℝ (Fin n)))) ∘SL
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v : ℝ →L[ℝ] TangentSpace (𝓡∂ n) p)
    apply HasMFDerivWithinAt.comp (H' := EuclideanSpace ℝ (Fin n))
    · rw [zero_smul ℝ v, add_zero]
      exact modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt hp
    · apply HasFDerivWithinAt.hasMFDerivWithinAt
      fun_prop
    · intro x hx
      simp_all

#check ContinuousAt.eventually_mem

open Set.Notation

/-- If `f x ∈ s ∈ 𝓝 (f x)` for continuous `f`, then `f y ∈ s` near `x`.

This is essentially `Filter.Tendsto.eventually_mem`, but infers in more cases when applied. -/
theorem ContinuousWithinAt.eventually_mem {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y]
    {f : X → Y} {t : Set X} {x : X}
    (hf : ContinuousWithinAt f t x) (ht : x ∈ t) {s : Set Y}
    (hs : s ∈ 𝓝 (f x)) : ∀ᶠ y in 𝓝[t] x, f y ∈ s := by
  rw [continuousWithinAt_iff_continuousAt_restrict _ ht] at hf
  have := hf.eventually_mem (Filter.mem_sets.mp hs)
  rw [eventually_nhds_iff] at this
  rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
  obtain ⟨u, hu1, hu2, hu3⟩ := this
  use Subtype.val '' u
  simp_all []
  sorry

-- I keep getting stuck because

lemma hhh {p : EuclideanHalfSpace n} (v : TangentSpace (𝓡∂ n) p) :
    (fderiv ℝ (fun x ↦ x.ofLp 0) p.val) v = ((d% (𝓡∂ n) p) v).ofLp 0 := by

  sorry

example : ContinuousAdd ℝ := by exact instIsTopologicalAddGroupReal.toContinuousAdd

example : ContinuousAdd (EuclideanSpace ℝ (Fin n)) := by exact
  SeminormedAddCommGroup.toIsTopologicalAddGroup.toContinuousAdd

-- My current thinking ( I have not investigated this further)
-- if you use functions to manifolds in a composition of functions that ultimately are functions
-- between normed spaces (?), then you run into issues with incorrect instances being used (def-eq)

lemma HasMFDerivWithinAt.euclideanHalfSpace {p : EuclideanHalfSpace n}
    {γ : ℝ → EuclideanHalfSpace n} {v : TangentSpace (𝓡∂ n) p}
    (h : HasMFDerivAt[Ici (0 : ℝ)] γ (0 : ℝ) (ContinuousLinearMap.toSpanSingleton ℝ v ∘SL
      (NormedSpace.fromTangentSpace 1).toContinuousLinearMap)) :
  HasMFDerivAt[Ici 0] (↑(𝓡∂ n) ∘ γ) (0 : ℝ) (ContinuousLinearMap.toSpanSingleton ℝ v
    ∘SL (NormedSpace.fromTangentSpace 1).toContinuousLinearMap) := by
  obtain ⟨h1, h2⟩ := h
  simp at h2
  exact h2.hasMFDerivWithinAt

lemma not_isRealizable_of_lt_zero {p : EuclideanHalfSpace n} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : d% (𝓡∂ n) p v 0 < 0) : ¬ IsRealizable v := by
  intro hv'
  unfold IsRealizable at hv'
  obtain ⟨γ, ε, hε, hγ, hγp, hγv⟩ := hv'
  have := hγv.1
  replace hγv := hγv.euclideanHalfSpace
  -- I think this reproduces the def-eq issue:
  -- above do `⟨h, hγv⟩` instead of just `hγv`
  --simp at hγv

  -- I have a def-eq issue here, need to investigate later
  --change HasFDerivWithinAt (↑(𝓡∂ n) ∘ γ) (ContinuousLinearMap.toSpanSingleton ℝ v) (Ici 0) 0 at hγv
  --rw [← hasDerivWithinAt_iff_hasFDerivWithinAt] at hγv
  have h1 : HasMFDerivAt[Ici 0] ((EuclideanSpace.proj 0) ∘ ↑(𝓡∂ n) ∘ γ : ℝ → ℝ) (0 : ℝ)
      (EuclideanSpace.proj 0 ∘SL ContinuousLinearMap.toSpanSingleton ℝ v ∘SL
        (NormedSpace.fromTangentSpace 1).toContinuousLinearMap) := by
    apply (PiLp.proj 2 (fun x ↦ ℝ) 0).hasFDerivAt.hasMFDerivAt.comp_hasMFDerivWithinAt
    exact hγv
    --apply (PiLp.proj 2 (fun x ↦ ℝ) 0).hasFDerivAt.comp_hasFDerivWithinAt
    --exact hγv -- why can't I put this into the apply?
  have h2 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      ((EuclideanSpace.proj 0) ∘ ↑(𝓡∂ n) ∘ γ : ℝ → ℝ) (Ico 0 ε) := by
    apply ContMDiff.comp_contMDiffOn
      (PiLp.proj 2 (fun x ↦ ℝ) 0 : StrongDual ℝ (EuclideanSpace ℝ (Fin n))).contDiff.contMDiff
    exact (𝓡∂ n).contMDiff.comp_contMDiffOn hγ
  simp only [coe_proj] at h1
  --replace h2 := h2.contDiffOn
  --rw [hasDerivWithinAt_iff_tendsto, NormedAddGroup.tendsto_nhds_zero] at h1
  --simp at h1
  -- I need some equivalent of `HasFDerivWithinAt.continuousOn_fderivWithin` here
  --have h3 := h2.continuousOn_fderivWithin (uniqueDiffOn_Ico 0 ε) ENat.LEInfty.out
  have : fderivWithin ℝ (⇑(proj 0) ∘ (𝓡∂ n) ∘ γ) (Ici 0) 0 1 = d% (𝓡∂ n) p v 0 := by
    rw [fderiv_comp_fderivWithin]
    · -- I have some def-eq issue here
      --change HasFDerivWithinAt (↑(𝓡∂ n) ∘ γ) (ContinuousLinearMap.toSpanSingleton ℝ v ∘SL
      --  (NormedSpace.fromTangentSpace 1).toContinuousLinearMap) (Ici 0) 0
      --  at hγv

      --have := @HasFDerivWithinAt.fderivWithin _ _ ℝ _ _ _ _ _ _ _ _ (ContinuousLinearMap.toSpanSingleton ℝ v ∘SL ↑(NormedSpace.fromTangentSpace 1)) _ _ SeminormedAddCommGroup.toIsTopologicalAddGroup.toContinuousAdd _ instIsTopologicalAddGroupReal.toContinuousAdd _ _ hγv (uniqueDiffWithinAt_Ici 0)
      simp [hγp, modelWithCornersEuclideanHalfSpace_apply]
      -- this should be a lemma

      simp [mvfderiv]

      sorry
    · simp only [coe_proj, comp_apply, hγp, modelWithCornersEuclideanHalfSpace_apply]
      fun_prop
    · sorry
      --exact hγv.differentiableWithinAt
    · exact uniqueDiffWithinAt_Ici 0

  --have h4 :=  ContinuousWithinAt.eventually_mem  (h3.continuousWithinAt (left_mem_Ico.mpr hε))

  --have : fderivWithin ℝ (⇑(proj 0) ∘ ↑(𝓡∂ n) ∘ γ) (Ico 0 ε) 0 < 0 := by
  --  sorry
  sorry

lemma prop541euclideanTry2 {p : EuclideanHalfSpace n} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry2 v ↔ 0 < v.ofLp 0 := by
  constructor
  · intro h
    unfold IsInwardPointingTry2 at h
    obtain ⟨γ, ε, hε, hγ, hγp, hγv⟩ := interior_subset h
    sorry
  · intro h
    have : IsRealizable v := IsRealizable_of_zero_lt hp v h
    unfold IsInwardPointingTry2
    rw [mem_interior]
    unfold TangentSpace at v
    use Metric.ball (α := EuclideanSpace ℝ (Fin n)) v (v.ofLp 0)
    refine ⟨?_, Metric.isOpen_ball (α := EuclideanSpace ℝ (Fin n)),
      Metric.mem_ball_self (α := EuclideanSpace ℝ (Fin n)) h⟩
    intro w hw
    unfold TangentSpace at hw
    rw [Metric.mem_ball] at hw
    apply IsRealizable_of_zero_lt hp
    have : dist (v.ofLp 0) (w.ofLp 0) < v.ofLp 0 := by
      rw [dist_eq w v] at hw
      apply lt_of_le_of_lt ?_ hw
      rw [Real.le_sqrt dist_nonneg (Finset.sum_nonneg' fun i ↦ pow_two_nonneg _), dist_comm]
      exact Finset.single_le_sum (f := fun i ↦ dist (w.ofLp i) (v.ofLp i) ^ 2)
        (fun i a ↦ pow_two_nonneg (dist (w.ofLp i) (v.ofLp i)))
        (Finset.mem_univ 0)
    rw [Real.dist_eq (v.ofLp 0) (w.ofLp 0), abs_sub_comm] at this
    simpa using sub_lt_of_abs_sub_lt_left this

lemma prop541euclidean {p : EuclideanHalfSpace n} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointing v ↔ 0 < v.ofLp 0 := by
  constructor
  · intro ⟨γ, ε, hε, hγ, hγp, hγε, ⟨hγ', hγv⟩⟩
    simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
      OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_source,
      OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq, PartialEquiv.refl_trans,
      ModelWithCorners.toPartialEquiv_coe, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialEquiv.refl_symm, PartialEquiv.refl_coe, CompTriple.comp_eq,
      preimage_id_eq, id_eq, modelWithCornersSelf_coe, range_id, inter_univ] at hγv
    --unfold TangentSpace at v
    have h1 : HasFDerivWithinAt ((EuclideanSpace.proj 0) ∘ ↑(𝓡∂ n) ∘ γ : ℝ → ℝ)
        (EuclideanSpace.proj 0 ∘SL ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v) (Ici 0) 0 := by
      apply (PiLp.proj 2 (fun x ↦ ℝ) 0).hasFDerivAt.comp_hasFDerivWithinAt
      exact hγv -- why can't I put this into the apply?
    have h2 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        ((EuclideanSpace.proj 0) ∘ ↑(𝓡∂ n) ∘ γ : ℝ → ℝ) (Ico 0 ε) := by
      apply ContMDiff.comp_contMDiffOn
        (PiLp.proj 2 (fun x ↦ ℝ) 0 : StrongDual ℝ (EuclideanSpace ℝ (Fin n))).contDiff.contMDiff
      exact (𝓡∂ n).contMDiff.comp_contMDiffOn hγ
    simp only [coe_proj, hasFDerivWithinAt_iff_hasDerivWithinAt, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] at h1
    replace h2 := h2.contDiffOn
    rw [hasDerivWithinAt_iff_tendsto, NormedAddGroup.tendsto_nhds_zero] at h1
    simp at h1
    sorry
  · intro h
    unfold TangentSpace at v
    let γ : ℝ → EuclideanHalfSpace n := (𝓡∂ n).symm ∘ (fun i ↦ p.1 + i • v)
    have hp' := modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.1 hp
    have hγ : CMDiff[Ico 0 1] ∞ γ := by
      unfold γ
      apply (𝓡∂ n).contMDiffOn_symm.comp
      · rw [contMDiffOn_iff_contDiffOn]
        fun_prop
      · intro x hx
        simp_all [range_modelWithCornersEuclideanHalfSpace n]
    use γ, 1, Real.zero_lt_one, hγ
    refine ⟨?_, ?_, ?_⟩
    · simp [γ, modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint hp]
    · intro x hx
      simp_all [ModelWithCorners.interior.eq_def (EuclideanHalfSpace n),
        modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff, γ,
        modelWithCornersEuclideanHalfSpace_symm_apply]
    · unfold γ
      change HasMFDerivAt[Ici 0] (↑(𝓡∂ n).symm ∘ fun i ↦ p.val + i • v : ℝ → EuclideanHalfSpace n)
        (0 : ℝ) ((ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n)
        (0 : EuclideanSpace ℝ (Fin n)))) ∘SL
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v : ℝ →L[ℝ] TangentSpace (𝓡∂ n) p)
      apply HasMFDerivWithinAt.comp (H' := EuclideanSpace ℝ (Fin n))
      · rw [zero_smul ℝ v, add_zero]
        exact modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt hp
      · apply HasFDerivWithinAt.hasMFDerivWithinAt
        fun_prop
      · intro x hx
        simp_all

lemma haha (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {F : Type u_6} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (s : Set E) (x : E) (hf : DifferentiableWithinAt 𝕜 f s x) (v : E) :
    fderivWithin 𝕜 f s x v = derivWithin (f ∘ fun i ↦ x + i • v)
      ((fun i ↦ x + i • v) ⁻¹' s) (0 : 𝕜) := by
  rw [← fderivWithin_derivWithin, fderivWithin_comp (t := s)]
  ·
    sorry
  · simp [hf]
  · fun_prop
  · exact mapsTo_preimage (fun i ↦ x + i • v) s
  · -- DifferentiableWithinAt.comp'
    sorry

lemma prop541euclideanTry3 {p : EuclideanHalfSpace n} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry3 v ↔ 0 < v.ofLp 0 := by
  constructor
  · intro h
    have hp' := modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.1 hp
    have h1 : CMDiff ∞ (⇑(proj 0) ∘ ↑(𝓡∂ n)) :=
      ContDiff.comp_contMDiff (by fun_prop) (𝓡∂ n).contMDiff
    have h2 : MDiffAt (proj 0 ∘ ↑(𝓡∂ n)) p :=
      h1.contMDiffAt.mdifferentiableAt (ne_of_beq_false rfl)
    unfold IsInwardPointingTry3 at h

    suffices h' : 0 ≤ (d% ((proj 0) ∘ ↑(𝓡∂ n)) p) v by
      simp [mvfderiv, mfderiv, h2, -coe_proj, range_modelWithCornersEuclideanHalfSpace n,
        modelWithCornersEuclideanHalfSpace_apply] at h'
      have : (fderivWithin ℝ ((⇑(proj 0) ∘ ↑(𝓡∂ n)) ∘ ↑(𝓡∂ n).symm) {y | 0 ≤ y.ofLp 0} p.val)
          = fderivWithin ℝ (⇑(proj 0)) {y | 0 ≤ y.ofLp 0} p.val := by
        refine DifferentiableWithinAt.fderivWithin_congr_mono ?_ ?_ ?_ ?_ ?_
        · fun_prop
        · intro x hx
          suffices x ∈ range ↑(𝓡∂ n) by
            rw [comp_apply, comp_apply, (𝓡∂ n).right_inv this]
          rw [range_modelWithCornersEuclideanHalfSpace]
          exact hx
        · suffices p.val ∈ range ↑(𝓡∂ n) by
            rw [comp_apply, comp_apply, (𝓡∂ n).right_inv this]
          rw [range_modelWithCornersEuclideanHalfSpace]
          exact (modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.1 hp).ge
        · -- extract this
          apply uniqueDiffOn_convex
          · exact EuclideanHalfSpace.convex


          · simp

            sorry
          sorry
        · sorry
      rw [this] at h'

      sorry
    apply h (EuclideanSpace.proj 0 ∘ 𝓡∂ n) h1
    · intro x
      simp [modelWithCornersEuclideanHalfSpace_apply, x.prop]
    · intro x hx
      simpa [modelWithCornersEuclideanHalfSpace_apply,
        modelWithCornersEuclideanHalfSpace_boundary_eq] using hx
  · intro h f hf1 hf2 hf3
    have hf4 : MDiffAt f p := hf1.contMDiffAt.mdifferentiableAt (ne_of_beq_false rfl)
    -- this last proof above surely can be nicer
    -- lemmas for this special case instead of unfolding
    suffices 0 ≤ (NormedSpace.fromTangentSpace (f p) : TangentSpace 𝓘(ℝ, ℝ) (f p) ≃L[ℝ] ℝ)
        ((fderivWithin ℝ (f ∘ ↑(𝓡∂ n).symm) {y | 0 ≤ y.ofLp 0} ((𝓡∂ n) p)) v) by
      simpa [mvfderiv, mfderiv, range_modelWithCornersEuclideanHalfSpace n, hf4]
    have hp' := modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.1 hp
    unfold TangentSpace at v
    -- this should also really be an extra lemma
    have h' :
        0 ≤ ((fderivWithin ℝ (f ∘ ↑(𝓡∂ n).symm ∘ fun (i : ℝ) ↦ p.val + i • v) (Ioi 0) 0)) 1 := by
      apply IsLocalMinOn.fderivWithin_nonneg
      · apply IsLocalMin.on
        apply IsMinOn.isLocalMin ?_ univ_mem
        rw [isMinOn_univ_iff]
        intro x
        have : (↑(𝓡∂ n).symm ∘ fun (i : ℝ) ↦ p.val + i • v) 0 ∈
            (𝓡∂ n).boundary (EuclideanHalfSpace n) := by
          simp [modelWithCornersEuclideanHalfSpace_boundary_eq,
            modelWithCornersEuclideanHalfSpace_symm_apply, hp']
        rw [comp_apply, hf3 _ this]
        exact hf2 _
      · simp [one_mem_posTangentConeAt_iff_mem_closure]
    have : (fderivWithin ℝ (fun i ↦ p.val + i • v) (Ioi 0) 0) (1 : ℝ) = v := by
      simp [fderivWithin_smul_const (uniqueDiffWithinAt_Ioi 0) (differentiableWithinAt_fun_id) v,
        fderivWithin_fun_id (uniqueDiffWithinAt_Ioi 0)]
    change 0 ≤ (fderivWithin ℝ (f ∘ ↑(𝓡∂ n).symm) {y | 0 ≤ y.ofLp 0} p.val) v
    rw [← comp_assoc, fderivWithin_comp (s := Ioi 0) (t := {y | 0 ≤ y.ofLp 0}) _ ?_ (by fun_prop)
      ( fun x hx ↦ by simp_all [h.le]) (uniqueDiffWithinAt_Ioi 0),
      ContinuousLinearMap.comp_apply, this, zero_smul, add_zero] at h'
    · exact h'
    · simp only [zero_smul, add_zero]
      rw [← mdifferentiableWithinAt_iff_differentiableWithinAt]
      apply hf4.comp_mdifferentiableWithinAt_of_eq
      · exact (modelWithCornersEuclideanHalfSpace_symm_mDifferentialbleWithinAt hp)
      · simp [modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint hp]
lemma prop541euclideanTry4 {p : EuclideanHalfSpace n} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry4 v ↔ 0 < v.ofLp 0 := by
  constructor
  · intro h
    have hp' := modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.1 hp
    have h1 : CMDiff ∞ (⇑(proj 0) ∘ ↑(𝓡∂ n)) :=
      ContDiff.comp_contMDiff (by fun_prop) (𝓡∂ n).contMDiff
    have h2 : MDiffAt (proj 0 ∘ ↑(𝓡∂ n)) p :=
      h1.contMDiffAt.mdifferentiableAt (ne_of_beq_false rfl)
    unfold IsInwardPointingTry3 at h

    suffices h' : 0 < (d% ((proj 0) ∘ ↑(𝓡∂ n)) p) v by
      simp [mvfderiv, mfderiv, h2, -coe_proj, range_modelWithCornersEuclideanHalfSpace n,
        modelWithCornersEuclideanHalfSpace_apply] at h'
      have : (fderivWithin ℝ ((⇑(proj 0) ∘ ↑(𝓡∂ n)) ∘ ↑(𝓡∂ n).symm) {y | 0 ≤ y.ofLp 0} p.val)
          = fderivWithin ℝ (⇑(proj 0)) {y | 0 ≤ y.ofLp 0} p.val := by
        refine DifferentiableWithinAt.fderivWithin_congr_mono ?_ ?_ ?_ ?_ ?_
        · fun_prop
        · intro x hx
          suffices x ∈ range ↑(𝓡∂ n) by
            rw [comp_apply, comp_apply, (𝓡∂ n).right_inv this]
          rw [range_modelWithCornersEuclideanHalfSpace]
          exact hx
        · suffices p.val ∈ range ↑(𝓡∂ n) by
            rw [comp_apply, comp_apply, (𝓡∂ n).right_inv this]
          rw [range_modelWithCornersEuclideanHalfSpace]
          exact (modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.1 hp).ge
        · -- extract this
          apply uniqueDiffOn_convex
          · exact EuclideanHalfSpace.convex


          · simp

            sorry
          sorry
        · sorry
      rw [this] at h'

      sorry
    apply h (EuclideanSpace.proj 0 ∘ 𝓡∂ n) h1
    · intro x
      simp [modelWithCornersEuclideanHalfSpace_interior_eq, modelWithCornersEuclideanHalfSpace_apply]
    · intro x hx
      simpa [modelWithCornersEuclideanHalfSpace_apply,
        modelWithCornersEuclideanHalfSpace_boundary_eq] using hx
  · intro h f hf1 hf2 hf3
    have hf4 : MDiffAt f p := hf1.contMDiffAt.mdifferentiableAt (ne_of_beq_false rfl)
    -- this last proof above surely can be nicer
    -- lemmas for this special case instead of unfolding
    suffices 0 < (NormedSpace.fromTangentSpace (f p) : TangentSpace 𝓘(ℝ, ℝ) (f p) ≃L[ℝ] ℝ)
        ((fderivWithin ℝ (f ∘ ↑(𝓡∂ n).symm) {y | 0 ≤ y.ofLp 0} ((𝓡∂ n) p)) v) by
      simpa [mvfderiv, mfderiv, range_modelWithCornersEuclideanHalfSpace n, hf4]
    have hp' := modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.1 hp
    unfold TangentSpace at v
    -- this should also really be an extra lemma
    have h' :
        0 < ((fderivWithin ℝ (f ∘ ↑(𝓡∂ n).symm ∘ fun (i : ℝ) ↦ p.val + i • v) (Ioi 0) 0)) 1 := by

      sorry
    have : (fderivWithin ℝ (fun i ↦ p.val + i • v) (Ioi 0) 0) (1 : ℝ) = v := by
      simp [fderivWithin_smul_const (uniqueDiffWithinAt_Ioi 0) (differentiableWithinAt_fun_id) v,
        fderivWithin_fun_id (uniqueDiffWithinAt_Ioi 0)]
    change 0 < (fderivWithin ℝ (f ∘ ↑(𝓡∂ n).symm) {y | 0 ≤ y.ofLp 0} p.val) v
    rw [← comp_assoc, fderivWithin_comp (s := Ioi 0) (t := {y | 0 ≤ y.ofLp 0}) _ ?_ (by fun_prop)
      ( fun x hx ↦ by simp_all [h.le]) (uniqueDiffWithinAt_Ioi 0),
      ContinuousLinearMap.comp_apply, this, zero_smul, add_zero] at h'
    · exact h'
    · simp only [zero_smul, add_zero]
      rw [← mdifferentiableWithinAt_iff_differentiableWithinAt]
      apply hf4.comp_mdifferentiableWithinAt_of_eq
      · exact (modelWithCornersEuclideanHalfSpace_symm_mDifferentialbleWithinAt hp)
      · simp [modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint hp]

set_option linter.tacticCheckInstances true
--#defeq_abuse in
set_option backward.isDefEq.respectTransparency false in
lemma prop541euclideanTry5 {p : EuclideanHalfSpace n} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5 v ↔ 0 < ((d% (𝓡∂ n) p) v).ofLp 0 := by
  constructor
  · intro ⟨f, hf1, hf2, hf3, hf4⟩
    by_contra! hv
    let x := (mfderiv% (𝓡∂ n) p) v
    let y := (d% (𝓡∂ n) p) v
    have yay1 : d[Ici (0 : ℝ)] (f ∘ (𝓡∂ n).symm ∘ fun (i : ℝ) ↦ p.val - i • y) 0 1 < 0 := by
      unfold mvfderivWithin
      have h1 :  MDiffAt f p := hf1.mdifferentiableAt (ne_of_beq_false rfl)
      have hh : MDiffAt[{x | 0 ≤ x.ofLp 0}] (𝓡∂ n).symm (p.val - (0 : ℝ) • y) := by
        simp only [zero_smul, sub_zero]
        exact modelWithCornersEuclideanHalfSpace_symm_mDifferentialbleWithinAt hp
      have h2'' : MDiffAt[Ici 0] (fun (i : ℝ) ↦ p.val - i • y) 0 := by
          refine DifferentiableWithinAt.mdifferentiableWithinAt ?_
          fun_prop
      have h2''' : Ici 0 ⊆ (fun (i : ℝ) ↦ p.val - i • y) ⁻¹' {x | 0 ≤ x.ofLp 0} := by
        intro x hx
        simp [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, y,
          mul_nonpos_of_nonneg_of_nonpos hx hv]
      have h2 : MDiffAt[Ici 0] ((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ p.val - i • y) 0 := hh.comp 0 h2'' h2'''
      have h3 : UniqueMDiffAt[Ici (0 : ℝ)] 0 := by
        rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
        exact uniqueDiffWithinAt_Ici 0
      have h4 : (↑(𝓡∂ n).symm ∘ fun (i : ℝ) ↦ p.val - i • y) 0 = p := by
        simp [modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint hp]
      rw [mfderiv_comp_mfderivWithin_of_eq h1 h2 h3 h4, ← ContinuousLinearMap.comp_assoc]
      rw [ContinuousLinearMap.comp_apply]
      suffices h : (mfderiv[Ici (0 : ℝ)] ((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ p.val - i • y) 0) 1 =  - v by
        have : (d% f p) (-v) < 0 := by simp [hf4]
        exact h ▸ this
      rw [mfderivWithin_comp 0 hh h2'' h2''' h3]
      rw [zero_smul ℝ y]
      rw [sub_zero]
      rw [HasMFDerivWithinAt.mfderivWithin (modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt hp)]
      · simp only [comp_apply, mfderivWithin_eq_fderivWithin, ContinuousLinearMap.id_comp]
        change (fderivWithin ℝ (fun (i : ℝ) ↦ p.val - i • y) (Ici 0) 0) 1 = -v
        rw [fderivWithin_derivWithin (𝕜 := ℝ) (f := fun (i : ℝ) ↦ p.val - i • y) (s := Ici 0) (x := 0)]
        rw [derivWithin_const_sub]
        rw [derivWithin_smul_const differentiableWithinAt_fun_id y]
        rw [derivWithin_id' 0 (Ici 0) (uniqueDiffWithinAt_Ici 0)]
        simp only [mvfderiv, (𝓡∂ n).hasMFDerivAt.mfderiv (x := p), ContinuousLinearMap.comp_id,
          ContinuousLinearEquiv.coe_coe, one_smul, neg_inj, y]
        rfl
      rw [← range_modelWithCornersEuclideanHalfSpace n]
      change UniqueMDiffAt[range (𝓡∂ n)] ((𝓡∂ n) p)
      exact (𝓡∂ n).uniqueMDiffOn _ (mem_range_self p)
    unfold mvfderivWithin at yay1
    simp [comp_apply, mfderivWithin_eq_fderivWithin, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] at yay1
    rw [zero_smul, sub_zero] at yay1
    -- this is major def-eq abuse caused by `mfderiv_eq_fderiv`
    simp [NormedSpace.fromTangentSpace] at yay1
    -- this uses the assumptions hv and hf3
    have yay2 : 0 ≤ (fderivWithin ℝ (f ∘ ↑(𝓡∂ n).symm ∘ fun i ↦ p.val - i • y) (Ici (0 : ℝ)) 0) 1 := by
      apply IsLocalMinOn.fderivWithin_nonneg
      · apply IsMinOn.localize
        intro x hx
        simp only [comp_apply, zero_smul, sub_zero, mem_setOf_eq]
        rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint hp, hf3 p hp]
        by_cases! hx' : x = 0 ∨ ((d% (𝓡∂ n) p) v).ofLp 0 = 0
        · apply ge_of_eq
          apply hf3
          simp [modelWithCornersEuclideanHalfSpace_boundary_eq,
            modelWithCornersEuclideanHalfSpace_symm_apply, y,
            hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, mul_nonpos_of_nonneg_of_nonpos hx hv,
            hx']
        · apply le_of_lt
          apply hf2
          simp [modelWithCornersEuclideanHalfSpace_interior_eq,
            modelWithCornersEuclideanHalfSpace_symm_apply, y,
            hp.eq_zero_of_modelWithCornersEuclideanHalfSpace]
          apply mul_neg_of_pos_of_neg (lt_of_le_of_ne hx hx'.1.symm) (lt_of_le_of_ne hv hx'.2)
      · simp [one_mem_posTangentConeAt_iff_mem_closure,
          inter_eq_self_of_subset_left Ioi_subset_Ici_self]
    apply not_lt_of_ge yay2 yay1
  · intro h
    have h1 : ∀ x ∈ (𝓡∂ n).interior (EuclideanHalfSpace n), 0 < (proj 0 ∘ 𝓡∂ n) x := by
      intro x hx
      simpa [modelWithCornersEuclideanHalfSpace_apply,
        modelWithCornersEuclideanHalfSpace_interior_eq] using hx
    have h2 : ∀ x ∈ (𝓡∂ n).boundary (EuclideanHalfSpace n), (proj 0 ∘ 𝓡∂ n) x = 0 := by
      intro x hx
      simpa [modelWithCornersEuclideanHalfSpace_apply,
        modelWithCornersEuclideanHalfSpace_boundary_eq] using hx
    use proj 0 ∘ 𝓡∂ n, ContDiff.comp_contMDiff (by fun_prop) (𝓡∂ n).contMDiff, h1, h2
    unfold mvfderiv
    -- **Def-eq issues reproducer**:
    -- if you turn the line below into a `simp only`, this causes def-eq issues not caught by
    -- `linter.tacticCheckInstances`, this is especially bad, because this lemma is a
    -- `simp` lemma
    rw [Function.comp_apply]
    have h3 : MDiffAt (proj 0 : StrongDual ℝ (EuclideanSpace ℝ (Fin n))) ((𝓡∂ n) p) := by
      apply DifferentiableAt.mdifferentiableAt
      fun_prop
    rw [mfderiv_comp p h3 (𝓡∂ n).mdifferentiableAt,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.mfderiv_eq (proj 0 : StrongDual ℝ (EuclideanSpace ℝ (Fin n)))]
    exact h

--#check mfderiv

-- a version with an existential

-- a version for the preferred chart

-- a model with corners that is star shaped should have an inward pointing
-- vector field

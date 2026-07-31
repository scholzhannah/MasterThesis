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
public import Mathlib.Geometry.Convex.Cone.Basic
public import CollarNeighbourhoods.IsInwardPointing

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

noncomputable def MDerivAlong (f : M → ℝ) {p : M} (v : TangentSpace I p) :=
  letI y := (mvfderiv I (extChartAt I p) p) v
  d% (f ∘ (extChartAt I p).symm ∘ fun (i : ℝ) ↦ (extChartAt I p p) + i • y)

noncomputable def MDerivAlongWithin (f : M → ℝ) {p : M} (v : TangentSpace I p) (s : Set ℝ) :=
  letI y := (mvfderiv I (extChartAt I p) p) v
  d[s] (f ∘ (extChartAt I p).symm ∘ fun (i : ℝ) ↦ (extChartAt I p p) + i • y)

theorem mvfderivWithin_comp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type u_6} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {f : M → M'} (x : M) {s : Set M} {g : M' → F} {u : Set M'}
    (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x) (h : s ⊆ f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) :
    d[s] (g ∘ f) x = (d[u] g (f x)).comp (mfderiv[s] f x) := by
  unfold mvfderivWithin
  rw [mfderivWithin_comp x hg hf h hxs, ContinuousLinearMap.comp_assoc]
  rfl

theorem mvfderiv_comp_mvfderivWithin
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type u_6} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {f : M → M'} (x : M) {s : Set M} {g : M' → F}
    (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x)
    (hxs : UniqueMDiffAt[s] x) :
    d[s] (g ∘ f) x = (d% g (f x)).comp (mfderiv[s] f x) := by
  unfold mvfderivWithin
  rw [mfderiv_comp_mfderivWithin x hg hf hxs, ← ContinuousLinearMap.comp_assoc]
  rfl

omit [IsManifold I ∞ M] in
lemma helper1 {p : M} (v : TangentSpace I p) :
    letI y := (mvfderiv I (extChartAt I p) p) v
    ((extChartAt I p).symm ∘ fun (i : ℝ) ↦ (extChartAt I p) p + i • y) 0 = p := by
  simp [(extChartAt I p).left_inv (mem_extChartAt_source p), -extChartAt]

#check MDifferentiableOn.mdifferentiableAt

-- use this instead probabaly
#check mdifferentiableWithinAt_extChartAt_symm

lemma jsdoa {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 < (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0) :
    MDiffAt[Ici 0] (fun (i : ℝ) ↦
      ((chartAt (EuclideanHalfSpace n) p).extend (𝓡∂ n)) p +
        i • (mvfderiv (𝓡∂ n) ((chartAt (EuclideanHalfSpace n) p).extend (𝓡∂ n)) p) v) 0 := by
  apply MDifferentiableWithinAt.add
  · exact mdifferentiableWithinAt_const
  · apply mdifferentiableWithinAt_id.smul
    exact mdifferentiableWithinAt_const


lemma thinkofnamelater {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 < (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) (𝓡∂ n) ((extChartAt (𝓡∂ n) p).symm ∘
      fun (i : ℝ) ↦ (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v)
        (Ici (0 : ℝ)) (0 : ℝ) := by
  have h1 : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ n)
      (extChartAt (𝓡∂ n) p).symm (extChartAt (𝓡∂ n) p).target
      ((extChartAt (𝓡∂ n) p) p + (0 : ℝ) • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) := by
    apply MDifferentiableWithinAt.mono (extChartAt_target_subset_range p)
    apply mdifferentiableWithinAt_extChartAt_symm
    simp [mem_extChartAt_target p, -extChartAt]
  have h2 : MDiffAt[Ici 0] (fun (i : ℝ) ↦
      (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) 0 :=
    mdifferentiableWithinAt_const.add (mdifferentiableWithinAt_id.smul
      mdifferentiableWithinAt_const)
  let V := (fun (i : ℝ) ↦
      (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) ⁻¹'
      (extChartAt (𝓡∂ n) p).target
  apply MDifferentiableWithinAt.congr_nhds (s := V ∩ Ici 0)
  · apply h1.comp 0 (h2.mono inter_subset_right)
    exact inter_subset_left
  · refine nhdsWithin_inter_of_mem ?_
    apply ContinuousWithinAt.preimage_mem_nhdsWithin'
    · fun_prop
    · rw [zero_smul, add_zero]
      apply nhdsWithin_mono (t := {x | 0 ≤ x.ofLp 0})
      · rw [image_subset_iff]
        intro x hx
        rw [mem_preimage]
        simp only [mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        apply add_nonneg
        · apply le_of_eq
          simpa [ModelWithCorners.isBoundaryPoint_iff, range_modelWithCornersEuclideanHalfSpace,
            frontier_halfSpace, modelWithCornersEuclideanHalfSpace_apply,
            -modelWithCornersEuclideanHalfSpace_toFun] using hp
        · change 0 ≤ x • ((mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v).ofLp 0
          exact smul_nonneg hx hv.le
      · rw [extChartAt_coe p]
        rw [extChartAt_target (𝓡∂ n) p]
        simp only [comp_apply, inter_mem_iff]
        refine ⟨?_, ?_⟩
        · apply (𝓡∂ n).continuousWithinAt_symm.preimage_mem_nhdsWithin
          rw [ModelWithCorners.left_inv]
          exact chart_target_mem_nhds (EuclideanHalfSpace n) p
        · rw [range_modelWithCornersEuclideanHalfSpace n]
          exact self_mem_nhdsWithin

theorem ContinuousLinearMap.zero_add (R₁ : Type u_1) [Semiring R₁] (M₁ : Type u_4)
    [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁] [ContinuousAdd M₁]
    (M₂ : Type u_4) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₁ M₂] [ContinuousAdd M₂]
    (f : M₁ →L[R₁] M₂) :
    (0 : M₁ →L[R₁] M₂) + f = f := by
  simp

set_option backward.isDefEq.respectTransparency false in
lemma MDerivAlong_eq {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 < (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (f : M → ℝ)
    (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f p) :
    MDerivAlongWithin f v (Ici 0) 0 1 = mvfderiv (𝓡∂ n) f p v := by
  unfold MDerivAlongWithin
  letI y := (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v
  rw [mvfderiv_comp_mvfderivWithin 0 ((helper1 v).symm ▸ hf)]
  · simp only [comp_apply, ContinuousLinearMap.comp_apply]
    rw [zero_smul, add_zero]
    rw [PartialEquiv.left_inv (extChartAt (𝓡∂ n) p) (mem_extChartAt_source p)]
    refine Eq.symm (DFunLike.congr rfl ?_)
    have h1 : mfderiv[Ici (0 : ℝ)] (fun (i : ℝ) ↦
        (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) 0 1
        = (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v := by
      rw [mfderivWithin_eq_fderivWithin]
      simp only [fderivWithin_const_add]
      rw [fderivWithin_smul_const (uniqueDiffWithinAt_Ici 0) differentiableWithinAt_fun_id,
        fderivWithin_fun_id (uniqueDiffWithinAt_Ici 0)]
      rw [zero_smul, add_zero]
      -- avoiding some mysterious defeq issues
      change ((ContinuousLinearMap.id ℝ ℝ).smulRight
        ((mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v)) 1 = _
      rw [ContinuousLinearMap.smulRight_apply]
      simp
    have : MDiffAt[Ici (0 : ℝ)] (fun (i : ℝ) ↦
        (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) 0 := by
      sorry
    -- I again have major defeq issues here, investigate this later
    change v = (mfderivWithin _ (𝓡∂ n) ((extChartAt (𝓡∂ n) p).symm ∘
      fun (i : ℝ) ↦ (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) (Ici 0) 0) 1
    --rw [mfderivWithin_comp 1]

    sorry
  · exact thinkofnamelater (E := E) hp v hv
  · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffWithinAt_Ici 0

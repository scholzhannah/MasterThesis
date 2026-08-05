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

section

variable {n : ℕ} [NeZero n]

lemma modelWithCornersEuclideanHalfSpace_apply {p : EuclideanHalfSpace n} : (𝓡∂ n) p = p.val :=
  rfl

@[simp]
lemma modelWithCornersEuclideanHalfSpace_symm_val_apply {p : EuclideanHalfSpace n} :
    (𝓡∂ n).symm p.val = p := by
  rw [← modelWithCornersEuclideanHalfSpace_apply, ModelWithCorners.left_inv (𝓡∂ n) p]

lemma modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff {p : EuclideanHalfSpace n} :
    (𝓡∂ n).IsBoundaryPoint p ↔ ((𝓡∂ n) p).ofLp 0 = 0 := by
  simp [ModelWithCorners.isBoundaryPoint_iff, eq_comm,
    range_modelWithCornersEuclideanHalfSpace, chartAt_self_eq,
    -modelWithCornersEuclideanHalfSpace_toFun]

lemma ModelWithCorners.IsBoundaryPoint.eq_zero_of_modelWithCornersEuclideanHalfSpace
    {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) : ((𝓡∂ n) p).ofLp 0 = 0 :=
  modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.mp hp

lemma modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint {p : EuclideanHalfSpace n}
    : (𝓡∂ n).symm ((𝓡∂ n) p) = p := by
  simp [-modelWithCornersEuclideanHalfSpace_toFun]

lemma modelWithCornersEuclideanHalfSpace_boundary_eq :
    (𝓡∂ n).boundary (EuclideanHalfSpace n) = {p | ((𝓡∂ n) p).ofLp 0 = 0} := by
  simp_rw [← modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff]
  rfl

lemma modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff {p : EuclideanHalfSpace n} :
    (𝓡∂ n).IsInteriorPoint p ↔ ((𝓡∂ n) p).ofLp 0 > 0 := by
  simp [ModelWithCorners.isInteriorPoint_iff, range_modelWithCornersEuclideanHalfSpace,
    chartAt_self_eq, -modelWithCornersEuclideanHalfSpace_toFun]

lemma modelWithCornersEuclideanHalfSpace_interior_eq :
    (𝓡∂ n).interior (EuclideanHalfSpace n) = {p | 0 < ((𝓡∂ n) p).ofLp 0} := by
  simp_rw [← modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff]
  rfl

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

theorem mvfderiv_comp_mfderivWithin
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

lemma mvfderiv_eq_fderiv {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {E' : Type u_3} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {f : E → E'} {x : E} :
    d% f x = fderiv 𝕜 f x :=
  mfderiv_eq_fderiv

theorem mvfderivWithin_eq_fderivWithin {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {E' : Type u_3} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {f : E → E'} {s : Set E} {x : E} :
    mfderiv[s] f x = fderivWithin 𝕜 f s x :=
  mfderivWithin_eq_fderivWithin

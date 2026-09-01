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

lemma ModelWithCorners.IsBoundaryPoint.eq_zero_of_modelWithCornersEuclideanHalfSpace'
    {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) : ((𝓡∂ n) p).ofLp 0 = 0 :=
  modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.mp hp

lemma modelWithCornersEuclideanHalfSpace_target (n : ℕ) [NeZero n] :
    (𝓡∂ n).target = { y | 0 ≤ y 0 } := by
  rw [(𝓡∂ n).target_eq, range_modelWithCornersEuclideanHalfSpace]


lemma ModelWithCorners.IsBoundaryPoint.eq_zero_of_modelWithCornersEuclideanHalfSpace
    {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M}
    (hp : (𝓡∂ n).IsBoundaryPoint p) : ((extChartAt (𝓡∂ n) p) p).ofLp 0 = 0 :=
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

-- **PR**
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

-- **PR**
theorem mvfderiv_comp_mfderivWithin
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {f : M → M'} (x : M) {s : Set M} {g : M' → F}
    (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x)
    (hxs : UniqueMDiffAt[s] x) :
    d[s] (g ∘ f) x = (d% g (f x)).comp (mfderiv[s] f x) := by
  unfold mvfderivWithin
  rw [mfderiv_comp_mfderivWithin x hg hf hxs, ← ContinuousLinearMap.comp_assoc]
  rfl

-- **PR by Michael**
lemma mvfderiv_eq_fderiv {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {E' : Type u_3} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {f : E → E'} {x : E} :
    d% f x = fderiv 𝕜 f x :=
  mfderiv_eq_fderiv

-- **PR by Michael**
theorem mvfderivWithin_eq_fderivWithin {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {E' : Type u_3} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {f : E → E'} {s : Set E} {x : E} :
    d[s] f x = fderivWithin 𝕜 f s x :=
  mfderivWithin_eq_fderivWithin

/-- The manifold derivative of `extChartAt` at the basepoint is the identity. -/
lemma mvfderiv_extChartAt_self {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type u_4} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {x : M} :
    d% (extChartAt I x) x = ContinuousLinearMap.id 𝕜 E :=
  mfderiv_extChartAt_self

-- **PR**
theorem mvfderiv_comp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {f : M → M'} (x : M) {g : M' → F} (hg : MDiffAt g (f x)) (hf : MDiffAt f x) :
    d% (g ∘ f) x = (d% g (f x)).comp (mfderiv% f x) := by
  unfold mvfderiv
  rw [mfderiv_comp x hg hf]
  rfl

-- **To-Do**: Zulip discussion about having `PartialHomeomorph` be public API

def Manifold.PartialDiffeomorphOfMaximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) : PartialDiffeomorph I I M H ∞ where
  toPartialEquiv := f.toPartialEquiv
  open_source := f.open_source
  open_target := f.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hf
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hf

omit [IsManifold I ∞ M] in
lemma Manifold.localDiffeomorphOn_of_mem_maximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) : IsLocalDiffeomorphOn I I ∞ f f.source:= by
  intro x
  apply (Manifold.PartialDiffeomorphOfMaximalAtlas hf).isLocalDiffeomorphAt
  exact x.2

omit [IsManifold I ∞ M] in
lemma Manifold.localDiffeomorphOn_symm_of_mem_maximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) : IsLocalDiffeomorphOn I I ∞ f.symm f.target := by
  intro x
  apply (Manifold.PartialDiffeomorphOfMaximalAtlas hf).symm.isLocalDiffeomorphAt
  exact x.2

omit [IsManifold I ∞ M] in
lemma Manifold.isBoundaryPoint_iff_of_mem_maximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) {p : M} (hpf : p ∈ f.source) :
    I.IsBoundaryPoint p ↔ I.IsBoundaryPoint (f p) :=
  ((Manifold.localDiffeomorphOn_of_mem_maximalAtlas hf) ⟨p, hpf⟩).isBoundaryPoint_iff
      (ne_of_beq_false rfl)

omit [IsManifold I ∞ M] in
lemma Manifold.isInteriorPoint_iff_of_mem_maximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) {p : M} (hpf : p ∈ f.source) :
    I.IsInteriorPoint p ↔ I.IsInteriorPoint (f p) :=
  ((Manifold.localDiffeomorphOn_of_mem_maximalAtlas hf) ⟨p, hpf⟩).isInteriorPoint_iff
    (ne_of_beq_false rfl)

omit [IsManifold I ∞ M] in
lemma PartialDiffeomorph.isOpen_image_source_inter {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H M'] {n : ℕ∞ω} (e : PartialDiffeomorph I I M M' n) {s : Set M} (hs : IsOpen s) :
    IsOpen (↑e '' (e.source ∩ s)) :=
  e.toOpenPartialHomeomorph.isOpen_image_source_inter hs

theorem nhdsWithin_of_mem_of_subset {α : Type u_1} [TopologicalSpace α] {a : α} {s t : Set α}
    (h : s ∈ nhdsWithin a t) (h1 : s ⊆ t) :
    nhdsWithin a s = nhdsWithin a t := by
  rw [← inter_eq_self_of_subset_left h1]
  exact nhdsWithin_inter_of_mem h

theorem mvfderiv_congr {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f f' : M → F} {x : M} (h : f = f') :
    d% f x = d% f' x := by subst h; rfl

theorem mvfderivWithin_congr {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f f' : M → F} {x : M} {s : Set M} (hL : ∀ x ∈ s, f' x = f x)
    (hx : f' x = f x) : d[s] f' x = d[s] f x :=
  (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL).mfderivWithin_eq hx

theorem MDifferentiableWithinAt.mvfderivWithin_mono {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : M → F} {x : M} {s t : Set M} (h : MDiffAt[s] f x)
    (hxt : UniqueMDiffAt[t] x) (h₁ : t ⊆ s) :
    d[t] f x = d[s] f x :=
  h.mfderivWithin_mono hxt h₁

theorem mvfderiv_id_comp_mfderivWithin {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : M → F} {x : M} {s : Set M} (h : MDiffAt[s] f x)
    (hxs : UniqueMDiffAt[s] x) :
    d% (id : F → F) (f x) ∘SL mfderiv[s] f x = d[s] f x := by
  rw [← mvfderiv_comp_mfderivWithin x mdifferentiableAt_id h hxs, id_comp f]

omit [IsManifold I ∞ M] in
theorem extChartAt_target_subset {p : M} : (extChartAt I p).target ⊆ I.target := by simp

theorem mfderivWithin_target_extChartAt_symm {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {M : Type u_4} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {x : M} :
    mfderiv[(extChartAt I x).target] (extChartAt I x).symm ((extChartAt I x) x) =
    ContinuousLinearMap.id 𝕜 (TangentSpace 𝓘(𝕜, E) ((extChartAt I x) x)) := by
  rw [mfderivWithin_congr_set (t := range I) ?_, mfderivWithin_range_extChartAt_symm]
  rw [← nhdsWithin_eq_iff_eventuallyEq, nhdsWithin_extChartAt_target_eq]

theorem Convex.add_smul_mem_icc {𝕜 E : Type*} [Field 𝕜] [PartialOrder 𝕜] [PosMulReflectLT 𝕜]
    [AddCommGroup E]
    [Module 𝕜 E] {s : Set E} [AddRightMono 𝕜] (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s) {r : 𝕜}
    (hr : 0 < r)
    (hy : x + r • y ∈ s) {t : 𝕜} (ht : t ∈ Set.Icc 0 r) : x + t • y ∈ s := by
  rw [← div_mul_cancel₀ t hr.ne.symm, mul_smul]
  apply hs.add_smul_mem hx hy
  refine ⟨div_nonneg ht.1 hr.le, (div_le_one hr).mpr ht.2⟩

theorem ModelWithCorners.mfderivWithin_symm {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {x : E} (hx : x ∈ Set.range ↑I) :
    mfderivWithin 𝓘(𝕜, E) I I.symm (range I) x =
      (ContinuousLinearMap.id 𝕜 (TangentSpace (modelWithCornersSelf 𝕜 E) x)) := by
  apply (hasMFDerivWithinAt_symm I hx).mfderivWithin
  exact I.uniqueMDiffOn x hx

theorem ModelWithCorners.mfderiv {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {x : H} :
    mfderiv I 𝓘(𝕜, E) I x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) :=
   I.hasMFDerivAt.mfderiv

theorem ModelWithCorners.mvfderiv {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {x : H} :
    mvfderiv I I x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) :=
   I.hasMFDerivAt.mfderiv

omit [NormedSpace ℝ E] in
lemma Topology.IsInducing.mvfderiv [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {p : H} :
    IsInducing (d% I p) := by
  rw [I.mvfderiv]
  apply IsHomeomorph.isInducing
  exact IsHomeomorph.id

noncomputable instance [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {p : H} :
    PseudoMetricSpace (TangentSpace I p) :=
  Topology.IsInducing.comapPseudoMetricSpace Topology.IsInducing.mvfderiv

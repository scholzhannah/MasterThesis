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

@[simp]
lemma modelWithCornersEuclideanHalfSpace_symm_val_apply {p : EuclideanHalfSpace n} :
    (𝓡∂ n).symm p.val = p := by
  rw [← modelWithCornersEuclideanHalfSpace_apply, ModelWithCorners.left_inv (𝓡∂ n) p]

lemma modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff {p : EuclideanHalfSpace n} :
    (𝓡∂ n).IsBoundaryPoint p ↔ ((𝓡∂ n) p).ofLp 0 = 0 := by
  simp [ModelWithCorners.isBoundaryPoint_iff, eq_comm,
    range_modelWithCornersEuclideanHalfSpace, chartAt_self_eq]

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

lemma modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint {p : EuclideanHalfSpace n} :
    (𝓡∂ n).symm ((𝓡∂ n) p) = p := by
  simp

lemma modelWithCornersEuclideanHalfSpace_boundary_eq :
    (𝓡∂ n).boundary (EuclideanHalfSpace n) = {p | ((𝓡∂ n) p).ofLp 0 = 0} := by
  simp_rw [← modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff]
  rfl

lemma modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff {p : EuclideanHalfSpace n} :
    (𝓡∂ n).IsInteriorPoint p ↔ ((𝓡∂ n) p).ofLp 0 > 0 := by
  simp [ModelWithCorners.isInteriorPoint_iff, range_modelWithCornersEuclideanHalfSpace,
    chartAt_self_eq]

lemma modelWithCornersEuclideanHalfSpace_interior_eq :
    (𝓡∂ n).interior (EuclideanHalfSpace n) = {p | 0 < ((𝓡∂ n) p).ofLp 0} := by
  simp_rw [← modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff]
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

@[simp]
lemma Manifold.isBoundaryPoint_chartAt_iff {p : M} :
    I.IsBoundaryPoint (chartAt H p p) ↔ I.IsBoundaryPoint p :=
  (Manifold.isBoundaryPoint_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p)
    (mem_chart_source H p)).symm

omit [IsManifold I ∞ M] in
lemma Manifold.isInteriorPoint_iff_of_mem_maximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) {p : M} (hpf : p ∈ f.source) :
    I.IsInteriorPoint p ↔ I.IsInteriorPoint (f p) :=
  ((Manifold.localDiffeomorphOn_of_mem_maximalAtlas hf) ⟨p, hpf⟩).isInteriorPoint_iff
    (ne_of_beq_false rfl)

@[simp]
lemma Manifold.isInteriorPoint_chartAt_iff {p : M} :
    I.IsInteriorPoint (chartAt H p p) ↔ I.IsInteriorPoint p :=
  (Manifold.isInteriorPoint_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p)
    (mem_chart_source H p)).symm

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
  rw [← nhdsWithin_eq_iff_eventuallyEqSet, nhdsWithin_extChartAt_target_eq]

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

noncomputable def TangentSpace.ofEq (I : ModelWithCorners ℝ E H) {p q : M} (h : p = q) :
    TangentSpace I p ≃ₜ TangentSpace I q := Homeomorph.refl (TangentSpace I p)

variable {M' : Type*} {H' : Type*} [TopologicalSpace H']
    [TopologicalSpace M'] [ChartedSpace H' M'] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {I' : ModelWithCorners ℝ E' H'} [ChartedSpace H M']

@[simps]
noncomputable def PartialDiffeomorph.mfderiv (p : M) (f : PartialDiffeomorph I I' M M' ∞)
    (hp : p ∈ f.source) : Homeomorph (TangentSpace I p) (TangentSpace I' (f p)) where
  toFun := mfderiv% f p
  invFun := TangentSpace.ofEq I (f.leftInvOn hp) ∘ mfderiv% f.symm (f p)
  left_inv v := by
    change (mfderiv% f.symm (f p)) ((mfderiv% f.toPartialEquiv p) v) = v
    rw [← mfderiv_comp_apply p ?_ (f.mdifferentiableAt (ne_of_beq_false rfl) hp) v]
    · rw [← mfderivWithin_of_isOpen f.open_source hp, mfderivWithin_congr_of_mem (f := id) ?_ hp]
      · rw [mfderivWithin_of_isOpen f.open_source hp, comp_apply, mfderiv_id]
        rfl
      exact f.leftInvOn
    · apply f.symm.mdifferentiableAt (ne_of_beq_false rfl)
      exact f.map_source' hp
  right_inv v := by
    change (mfderiv% f p) ((mfderiv% f.symm (f p)) v) = v
    have : f.symm (f p) = p := f.leftInvOn hp
    have : (mfderiv% f p) ((mfderiv% f.symm (f p)) v) = mfderiv% (f ∘ f.symm) (f p) v := by
      rw [mfderiv_comp_apply (f p) ?_
        (f.symm.mdifferentiableAt (ne_of_beq_false rfl) (f.map_source' hp)), symm_toPartialEquiv,
        f.leftInvOn hp]
      rw [symm_toPartialEquiv, f.leftInvOn hp]
      exact f.mdifferentiableAt (ne_of_beq_false rfl) hp
    rw [this]
    rw [← mfderivWithin_of_isOpen f.open_target (f.map_source' hp)]
    rw [mfderivWithin_congr_of_mem (f := id) ?_ (f.map_source' hp)]
    · rw [mfderivWithin_of_isOpen f.open_target (f.map_source' hp), comp_apply, mfderiv_id]
      rfl
    · exact f.symm.leftInvOn
  continuous_toFun := (mfderiv% f p).continuous
  continuous_invFun := (mfderiv% f.symm (f p)).continuous

omit [IsManifold I ∞ M] [ChartedSpace H M'] in
lemma PartialDiffeomorph.leftInverse_mfderiv_symm (p : M) (f : PartialDiffeomorph I I' M M' ∞)
    (hp : p ∈ f.source) : LeftInverse (mfderiv% f.symm (f p)) (mfderiv% f p) :=
  (f.mfderiv p hp).left_inv

omit [IsManifold I ∞ M] [ChartedSpace H M'] in
lemma PartialDiffeomorph.rightInverse_mfderiv_symm (p : M) (f : PartialDiffeomorph I I' M M' ∞)
    (hp : p ∈ f.source) : RightInverse (mfderiv% f.symm (f p)) (mfderiv% f p) :=
  (f.mfderiv p hp).right_inv

omit [IsManifold I ∞ M] [ChartedSpace H M'] in
lemma PartialDiffeomorph.isHomeomorph_mfderiv (p : M) (f : PartialDiffeomorph I I' M M' ∞)
    (hp : p ∈ f.source) : IsHomeomorph (mfderiv% f p) :=
  (mfderiv p f hp).isHomeomorph

omit [IsManifold I ∞ M] [ChartedSpace H M'] in
lemma PartialDiffeomorph.bijective_mfderiv (p : M) (f : PartialDiffeomorph I I' M M' ∞)
    (hp : p ∈ f.source) : Bijective (mfderiv% f p) :=
  (mfderiv p f hp).toEquiv.bijective

variable (I) in
@[simps]
noncomputable def mvfderivModelWithCorners (p : H) :
    Homeomorph (TangentSpace I p) E where
  toFun := d% I p
  invFun := mfderiv[range I] I.symm (I p) ∘ (NormedSpace.fromTangentSpace (𝕜 := ℝ) <| I p)
  left_inv v := by
    rw [I.mfderivWithin_symm (mem_range_self p), I.mvfderiv]
    rfl
  right_inv v := by
    rw [I.mfderivWithin_symm (mem_range_self p), I.mvfderiv]
    rfl
  continuous_toFun := (mfderiv% I p).continuous
  continuous_invFun := (mfderiv[range I] I.symm (I p)).continuous

variable (I) in
omit [IsManifold I ∞ M] [ChartedSpace H M'] in
lemma isHomeomorph_mvfderiv_modelWithCorners (p : H) : IsHomeomorph (d% I p) :=
  (mvfderivModelWithCorners I p).isHomeomorph

variable (I) in
omit [IsManifold I ∞ M] [ChartedSpace H M'] in
lemma bijective_mvfderiv_modelWithCorners (p : H) : Bijective (d% I p) :=
  (mvfderivModelWithCorners I p).toEquiv.bijective

lemma isLocalDiffeomorphAt_iff {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type u_3} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {H₁ : Type u_5}
    [TopologicalSpace H₁] {H₂ : Type u_6} [TopologicalSpace H₂] (I : ModelWithCorners 𝕜 E H₁)
    (J : ModelWithCorners 𝕜 F H₂) {M : Type u_8} [TopologicalSpace M] [ChartedSpace H₁ M]
    {N : Type u_9}
    [TopologicalSpace N] [ChartedSpace H₂ N] (n : WithTop ℕ∞) (f : M → N) (x : M) :
    IsLocalDiffeomorphAt I J n f x ↔
      ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source := by
 sorry

theorem closure_iInter_subset {X : Type*} [TopologicalSpace X] {ι : Sort*} (s : ι → Set X) :
     closure (⋂ i, s i) ⊆ ⋂ i, closure (s i) :=
  subset_iInter fun i ↦ closure_mono (iInter_subset s i)

@[simp]
theorem closure_quadrant {n : ℕ} (p : ENNReal) (a : ℝ) :
    closure { y : PiLp p (fun _ : Fin n ↦ ℝ) | ∀ i, a ≤ y i } = { y | ∀ i, a ≤ y i } := by
  rw [ofPred_forall]
  refine subset_antisymm ?_ subset_closure
  apply (closure_iInter_subset _).trans
  simp

/-- The model space used to define `n`-dimensional real manifolds with boundary. -/
scoped[Manifold]
  notation3 "𝓡∠ " n =>
    (modelWithCornersEuclideanQuadrant n :
      ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanQuadrant n))

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
public import CollarNeighbourhoods.ToMathlib

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

-- I think I also need this also for v = 0
-- use smooth embedding instead
-- and write a smooth embedding precomposition lemma
-- or potentially immersion
noncomputable def PartialEquivAlong {E : Type u_7}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (p v : E) (hv : ‖v‖ ≠ 0) : PartialEquiv ℝ E where
  toFun i := p + i • v
  invFun x := ‖x - p‖ / ‖v‖
  source := Ici 0
  target := (fun (i : ℝ) ↦ p + i • v) '' Ici 0
  map_source' x hx := mem_image_of_mem (fun i ↦ p + i • v) hx
  map_target' := by
    rw [forall_mem_image]
    intro x hx
    simp [norm_smul_of_nonneg hx v, mul_div_assoc, div_self hv, hx]
  left_inv' i hi := by simp [norm_smul_of_nonneg hi v, mul_div_assoc, div_self hv]
  right_inv' := by
    rw [forall_mem_image]
    intro x hx
    simp [norm_smul_of_nonneg hx v, mul_div_assoc, div_self hv]

noncomputable def AlongFunNe {p : M} (v : TangentSpace I p)
    (hv : (mvfderiv I (extChartAt I p) p) v ≠ 0) :
    PartialEquiv ℝ M  :=
  (PartialEquivAlong ((extChartAt I p) p) ((mvfderiv I (extChartAt I p) p) v)
    (norm_ne_zero_iff.mpr hv)).trans (extChartAt I p).symm

noncomputable def AlongFun {p : M} (v : TangentSpace I p) :=
  letI y := (mvfderiv I (extChartAt I p) p) v
  (extChartAt I p).symm ∘ fun (i : ℝ) ↦ (extChartAt I p p) + i • y

omit [IsManifold I ∞ M] in
lemma alongFun_eq_alongFunNe {p : M} (v : TangentSpace I p)
    (hv : (mvfderiv I (extChartAt I p) p) v ≠ 0) :
    AlongFunNe v hv = AlongFun v := by
  simp [AlongFunNe, AlongFun, PartialEquivAlong]

def AlongFunPreimIn {p : M} (v : TangentSpace I p) (s : Set M) :=
  letI y := (mvfderiv I (extChartAt I p) p) v
  AlongFun v ⁻¹' s ∩ (fun (i : ℝ) ↦ (extChartAt I p p) + i • y) ⁻¹' (extChartAt I p).target

omit [IsManifold I ∞ M] in
lemma alongFunPreimIn_extChartAt_source_eq {p : M} (v : TangentSpace I p) :
    letI y := (mvfderiv I (extChartAt I p) p) v
    AlongFunPreimIn v (extChartAt I p).source =
      (fun (i : ℝ) ↦ (extChartAt I p p) + i • y) ⁻¹' (extChartAt I p).target := by
  unfold AlongFunPreimIn AlongFun
  rw [preimage_comp, inter_eq_right]
  apply preimage_mono
  exact (extChartAt I p).target_subset_preimage_source

noncomputable def MDerivAlong (f : M → ℝ) {p : M} (v : TangentSpace I p) :=
  fderiv ℝ (f ∘ AlongFun v)

noncomputable def MDerivAlongWithin (f : M → ℝ) {p : M} (v : TangentSpace I p) (s : Set ℝ) :=
  fderivWithin ℝ (f ∘ AlongFun v) s

omit [IsManifold I ∞ M] in
theorem MDerivAlongWithin_subset {p : M} (v : TangentSpace I p) (f : M → ℝ) {s t : Set ℝ}
    (st : s ⊆ t) (ht : UniqueDiffWithinAt ℝ s 0)
    (h : DifferentiableWithinAt ℝ (f ∘ AlongFun v) t 0) :
    MDerivAlongWithin f v s 0 = MDerivAlongWithin f v t 0 :=
  fderivWithin_subset st ht h

omit [IsManifold I ∞ M] in
@[simp]
lemma alongFun_apply_zero {p : M} (v : TangentSpace I p) : AlongFun v 0 = p := by
  simp [AlongFun]

omit [IsManifold I ∞ M] in
lemma alongFun_zero {p : M} : AlongFun (0 : TangentSpace I p) = Function.const ℝ p := by
  unfold AlongFun
  rw [ContinuousLinearMap.map_zero]
  simp [-extChartAt, comp_def, (extChartAt I p).left_inv (mem_extChartAt_source p), const_def]

omit [IsManifold I ∞ M] in
lemma zero_mem_AlongFunPreimIn {p : M} (v : TangentSpace I p) :
    0 ∈ AlongFunPreimIn v (extChartAt I p).source := by
  simp [AlongFunPreimIn, AlongFun]

theorem contMDiffOn_alongFun {p : M} (v : TangentSpace I p) :
    CMDiff[AlongFunPreimIn v (extChartAt I p).source] ∞ (AlongFun v) := by
  unfold AlongFun
  apply (contMDiffOn_extChartAt_symm p).comp ?_ inter_subset_right
  rw [contMDiffOn_iff_contDiffOn]
  fun_prop

theorem mdifferentiableOn_alongFun {p : M} (v : TangentSpace I p) :
    MDiff[AlongFunPreimIn v (extChartAt I p).source] (AlongFun v) :=
  (contMDiffOn_alongFun v).mdifferentiableOn (ne_of_beq_false rfl)

-- I think this is probably the correct condition that we should be imposing
-- I don't think this is the correct notion because a model with corners which
-- is the shape of a circle doesn't fulfill this
-- so we actually just need the notion of something walking in the manifold for a bit
example {p : M} (v : TangentSpace I p)
    (hv : v ∈ tangentConeAt ℝ I.target ((extChartAt I p) p)) :
    ((fun (i : ℝ) ↦ (extChartAt I p) p + i • (mvfderiv I (extChartAt I p) p) v) ⁻¹'
        I.target).Nontrivial := by

  obtain ⟨α, l, hl, c, d, hdl, hld, hdlv⟩ := exists_fun_of_mem_tangentConeAt hv

  sorry

omit [IsManifold I ∞ M] in
lemma uniqueDiffWithinAt_preimage_modelWithCorners_target {p : M} (v : TangentSpace I p)
    (h : ((fun (i : ℝ) ↦ (extChartAt I p) p + i • (mvfderiv I (extChartAt I p) p) v) ⁻¹'
        I.target).Nontrivial) :
    letI y := (mvfderiv I (extChartAt I p) p) v
    UniqueDiffWithinAt ℝ ((fun (i : ℝ) ↦ (extChartAt I p) p + i • y) ⁻¹' I.target) 0 := by
  let y := (mvfderiv I (extChartAt I p) p) v
  have h' : Convex ℝ ((fun (i : ℝ) ↦ (extChartAt I p) p + i • y) ⁻¹' I.target) := by
    intro a ha b hb s t hs ht h
    rw [mem_preimage, I.target_eq] at ha hb ⊢
    rw [add_smul, ← add_assoc, smul_assoc, smul_assoc, ← one_smul (M := ℝ) ((extChartAt I p) p),
      ← h, add_smul, add_right_comm _ _ (s • a • y), add_assoc, ← smul_add, ← smul_add]
    exact convex_iff_add_mem.1 I.convex_range ha hb hs ht h
  apply uniqueDiffWithinAt_convex h'
  · rw [← h'.nontrivial_iff_nonempty_interior]
    exact h
  · apply subset_closure
    simp [mem_preimage]

omit [IsManifold I ∞ M] in
lemma preimage_extChartAt_target_mem_nhdsWithin {p : M} (v : TangentSpace I p) :
    (fun (i : ℝ) ↦ (extChartAt I p) p + i • (d% (extChartAt I p) p) v) ⁻¹' (extChartAt I p).target ∈
    𝓝[(fun i ↦ (extChartAt I p) p + i • (d% (extChartAt I p) p) v) ⁻¹' I.target] 0 := by
  apply ContinuousWithinAt.preimage_mem_nhdsWithin'' (by fun_prop) (y := (extChartAt I p) p)
  · rw [ModelWithCorners.target_eq I]
    exact extChartAt_target_mem_nhdsWithin p
  · rw [zero_smul, add_zero]

omit [IsManifold I ∞ M] in
lemma uniqueDiffWithinAt_alongFunPreimIn {p : M} (v : TangentSpace I p)
    (h : ((fun (i : ℝ) ↦ (extChartAt I p) p + i • (mvfderiv I (extChartAt I p) p) v) ⁻¹'
        I.target).Nontrivial) :
    UniqueDiffWithinAt ℝ (AlongFunPreimIn v (extChartAt I p).source) 0 := by
  rw [alongFunPreimIn_extChartAt_source_eq v, ← inter_eq_right.2 (extChartAt_target_subset_range p),
    ← ModelWithCorners.target_eq I, preimage_inter]
  apply (uniqueDiffWithinAt_preimage_modelWithCorners_target v h).inter'
  exact preimage_extChartAt_target_mem_nhdsWithin v

omit [IsManifold I ∞ M] in
lemma mfderiv_along_eq {p : M} (v : TangentSpace I p)
    (h : ((fun (i : ℝ) ↦ (extChartAt I p) p + i • (mvfderiv I (extChartAt I p) p) v) ⁻¹'
        I.target).Nontrivial) :
    mfderiv[AlongFunPreimIn v (extChartAt I p).source] (fun (i : ℝ) ↦
        (extChartAt I p) p + i • (d% (extChartAt I p) p) v) 0 1
      = (mvfderiv I (extChartAt I p) p) v := by
  --simp [-extChartAt]
  rw [mfderivWithin_eq_fderivWithin, fderivWithin_const_add, fderivWithin_smul_const
    (uniqueDiffWithinAt_alongFunPreimIn v h) differentiableWithinAt_fun_id, fderivWithin_fun_id
    (uniqueDiffWithinAt_alongFunPreimIn v h),
    ← ContinuousLinearMap.one_def, ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  change (ContinuousLinearMap.toSpanSingleton ℝ ((d% (extChartAt I p) p) v)) 1 =
    (d% (extChartAt I p) p) v
  rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]

lemma mvfderivWithin_alongFun {p : M} (v : TangentSpace I p)
    (h : ((fun (i : ℝ) ↦ (extChartAt I p) p + i • (mvfderiv I (extChartAt I p) p) v) ⁻¹'
        I.target).Nontrivial) :
    mfderiv[AlongFunPreimIn v (extChartAt I p).source] (AlongFun v) 0 1 = v := by
  let y := (mvfderiv I (extChartAt I p) p) v
  unfold AlongFun
  rw [mfderivWithin_comp 0 (mdifferentiableOn_extChartAt_symm ((extChartAt I p) p + 0 • y)
    (by simp))]
  · rw [ContinuousLinearMap.comp_apply, mfderiv_along_eq v h, zero_smul, add_zero,
      mfderivWithin_target_extChartAt_symm, mvfderiv_extChartAt_self]
    rfl
  · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    fun_prop
  · exact inter_subset_right
  · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffWithinAt_alongFunPreimIn v h

omit [IsManifold I ∞ M] in
theorem alongFunPreimIn_extChartAt_target_mem_nhdsWithin {p : M} (v : TangentSpace I p) :
    letI y := (mvfderiv I (extChartAt I p) p) v
    AlongFunPreimIn v (extChartAt I p).source ∈
    𝓝[(fun (i : ℝ) ↦ (extChartAt I p p) + i • y) ⁻¹' I.target] 0 := by
  rw [alongFunPreimIn_extChartAt_source_eq v]
  apply ContinuousWithinAt.preimage_mem_nhdsWithin' (by fun_prop)
  apply nhdsWithin_mono _ (image_preimage_subset _ _)
  rw [extChartAt_coe p, extChartAt_target, comp_apply, inter_mem_iff]
  refine ⟨?_, I.target_eq ▸  self_mem_nhdsWithin⟩
  apply I.continuousWithinAt_symm.preimage_mem_nhdsWithin
  simp [chart_target_mem_nhds]

theorem alongFunPreimIn_extChartAt_source {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 < ((mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v).ofLp 0) :
    letI y := (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v
    (fun (i : ℝ) ↦ (extChartAt (𝓡∂ n) p p) + i • y) ⁻¹' (𝓡∂ n).target = Ici 0 := by
  ext x
  rw [mem_preimage]
  constructor
  · contrapose!
    rw [modelWithCornersEuclideanHalfSpace_target n]
    simp only [mem_Ici, not_le, mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    intro hx
    simp [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, mul_neg_of_neg_of_pos hx hv,
      -extChartAt]
  · intro hx
    rw [(𝓡∂ n).target_eq, range_modelWithCornersEuclideanHalfSpace n]
    simp [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, mul_nonneg hx hv.le, -extChartAt]

theorem alongFunPreimIn_extChartAt_source_of_eq_zero {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : ((mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v).ofLp 0 = 0) :
    letI y := (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v
    (fun (i : ℝ) ↦ (extChartAt (𝓡∂ n) p p) + i • y) ⁻¹' (𝓡∂ n).target = univ := by
  rw [preimage_eq_univ_iff, modelWithCornersEuclideanHalfSpace_target n]
  simp [range_subset_iff, hv, hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, -extChartAt]

omit [IsManifold I ∞ M] in
lemma alongFunPreimIn_subset {p : M} (v : TangentSpace I p) (U : Set M) :
    letI y := (mvfderiv I (extChartAt I p) p) v
    AlongFunPreimIn v U ⊆ (fun (i : ℝ) ↦ (extChartAt I p p) + i • y) ⁻¹' I.target :=
  inter_subset_right.trans (preimage_mono extChartAt_target_subset)

lemma mdifferentiableWithinAt_alongFun {p : M} (v : TangentSpace I p) :
    letI y := (mvfderiv I (extChartAt I p) p) v
    MDiffAt[(fun (i : ℝ) ↦ (extChartAt I p p) + i • y) ⁻¹' I.target] (AlongFun v) (0 : ℝ) := by
  let y := (mvfderiv I (extChartAt I p) p) v
  apply ((mdifferentiableOn_alongFun v) 0 (zero_mem_AlongFunPreimIn v)).congr_nhds
  apply nhdsWithin_of_mem_of_subset
  · exact alongFunPreimIn_extChartAt_target_mem_nhdsWithin v
  · exact alongFunPreimIn_subset v (extChartAt I p).source

lemma mdifferentiableWithinAt_alongFun_alongFunPreimIn {p : M} (v : TangentSpace I p) (U : Set M) :
    MDiffAt[AlongFunPreimIn v U] (AlongFun v) (0 : ℝ) :=
  (mdifferentiableWithinAt_alongFun v).mono (alongFunPreimIn_subset v U)

lemma mdifferentiableAt_alongFun {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0 = 0) :
    MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡∂ n) (AlongFun v) (0 : ℝ) := by
  rw [← mdifferentiableWithinAt_univ, ← alongFunPreimIn_extChartAt_source_of_eq_zero hp v hv]
  exact mdifferentiableWithinAt_alongFun v

theorem mdifferentiableOn_alongFun_of_subset {p : M} (v : TangentSpace I p) (s : Set ℝ)
    (hs : (fun i ↦ (extChartAt I p) p + i • (d% (extChartAt I p) p) v) '' s ⊆
      (extChartAt I p).target) :
    MDiff[s] (AlongFun v) := by
  unfold AlongFun
  apply mdifferentiableOn_extChartAt_symm.comp ?_ (image_subset_iff.1 hs)
  rw [mdifferentiableOn_iff_differentiableOn]
  fun_prop

lemma MDifferentiableWithinAt_of_comp_partialDiffeomorph {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
    {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {M : Type u_4} [TopologicalSpace M] [ChartedSpace H M] {E' : Type u_5} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type u_6} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type u_7} [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type u_8}
    [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type u_9} [TopologicalSpace H'']
    {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type u_10} [TopologicalSpace M'']
    [ChartedSpace H'' M''] {f : PartialEquiv M M'} (x : M) {g : M' → M''}
    (hgf : MDiffAt[f.source] (g ∘ f) x) (hf : MDiffAt[f.symm.source] f.symm (f x))
    (hx : x ∈ f.source) :
    MDiffAt[f.target] g (f x) := by
  apply MDifferentiableWithinAt.congr (f := g ∘ f ∘ f.symm)
  · rw [← comp_assoc]
    apply hgf.comp_of_eq
    · rw [← f.symm_source]
      apply hf
    · rw [← image_subset_iff, ← f.symm_source, ← f.symm_target]
      exact f.symm.image_source_subset
    · exact (f.symm.eq_symm_apply (by simp [hx]) hx).mp rfl
  · intro y hy
    simp [f.right_inv hy]
  · simp only [comp_apply]
    rw [f.right_inv]
    exact f.map_source' hx

omit [IsManifold I ∞ M] in
lemma helper1 {p : M} (v : TangentSpace I p) :
    letI y := (mvfderiv I (extChartAt I p) p) v
    ((extChartAt I p).symm ∘ fun (i : ℝ) ↦ (extChartAt I p) p + i • y) 0 = p := by
  simp [(extChartAt I p).left_inv (mem_extChartAt_source p), -extChartAt]

-- don't use manifold derivs
lemma jsdoa {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M}
    (v : TangentSpace (𝓡∂ n) p) :
    MDiffAt[Ici 0] (fun (i : ℝ) ↦
      (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) 0 := by
  rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
  fun_prop
  --apply MDifferentiableWithinAt.add
  --· exact mdifferentiableWithinAt_const
  --· apply mdifferentiableWithinAt_id.smul
  --  exact mdifferentiableWithinAt_const

lemma mdifferentiableWithinAt_alongFun_euclideanHalfSpace {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) (𝓡∂ n) (AlongFun v) (Ici (0 : ℝ)) (0 : ℝ) := by
  rw [le_iff_lt_or_eq] at hv
  rcases hv with hv | hv
  · rw [← alongFunPreimIn_extChartAt_source hp v hv]
    exact mdifferentiableWithinAt_alongFun v
  · apply MDifferentiableWithinAt.mono (subset_univ _)
    rw [← alongFunPreimIn_extChartAt_source_of_eq_zero hp v hv.symm]
    exact mdifferentiableWithinAt_alongFun v

omit [IsManifold I ∞ M] in
lemma mfderivWithin_preimage_target_eq_mvfderiv_extChartAt {p : M} (v : TangentSpace I p)
    (h : ((fun (i : ℝ) ↦ (extChartAt I p) p + i • (mvfderiv I (extChartAt I p) p) v) ⁻¹'
        I.target).Nontrivial) :
    letI y := (mvfderiv I (extChartAt I p) p) v
    mfderiv[(fun i ↦ (extChartAt I p) p + i • y) ⁻¹' I.target]
        (fun (i : ℝ) ↦ (extChartAt I p) p + i • y) 0 1
      = (mvfderiv I (extChartAt I p) p) v := by
  rw [mfderivWithin_eq_fderivWithin]
  simp only [fderivWithin_const_add]
  rw [fderivWithin_smul_const (uniqueDiffWithinAt_preimage_modelWithCorners_target v h)
    differentiableWithinAt_fun_id,
    fderivWithin_fun_id (uniqueDiffWithinAt_preimage_modelWithCorners_target v h)]
  rw [zero_smul, add_zero]
  -- avoiding some mysterious defeq issues
  change ((ContinuousLinearMap.id ℝ ℝ).smulRight
    ((mvfderiv I (extChartAt I p) p) v)) 1 = _
  rw [ContinuousLinearMap.smulRight_apply]
  simp

lemma mvfderivWithin_alongFun' {p : M} (v : TangentSpace I p)
    (h : ((fun (i : ℝ) ↦ (extChartAt I p) p + i • (mvfderiv I (extChartAt I p) p) v) ⁻¹'
        I.target).Nontrivial) :
    mfderiv[(fun i ↦ (extChartAt I p) p + i • (d% (extChartAt I p) p) v) ⁻¹' I.target]
      (AlongFun v) 0 1 = v := by
  unfold AlongFun
  let y := (mvfderiv I (extChartAt I p) p) v
  -- we also use these above, lemmas?
  have h1 : MDiffAt[(extChartAt I p).target] (extChartAt I p).symm
      ((extChartAt I p) p + (0 : ℝ) • (mvfderiv I (extChartAt I p) p) v) := by
    apply MDifferentiableWithinAt.mono (extChartAt_target_subset_range p)
    apply mdifferentiableWithinAt_extChartAt_symm
    simp [mem_extChartAt_target p, -extChartAt]
  have h2 : MDiffAt[((fun (i : ℝ) ↦ (extChartAt I p p) + i • y) ⁻¹' I.target)] (fun (i : ℝ) ↦
      (extChartAt I p) p + i • (mvfderiv I (extChartAt I p) p) v) 0 :=
    mdifferentiableWithinAt_const.add (mdifferentiableWithinAt_id.smul
      mdifferentiableWithinAt_const)
  rw [mfderivWithin_comp_of_preimage_mem_nhdsWithin 0 h1 h2]
  · rw [ContinuousLinearMap.comp_apply, mfderivWithin_preimage_target_eq_mvfderiv_extChartAt v h,
      zero_smul, add_zero, mfderivWithin_target_extChartAt_symm, mvfderiv_extChartAt_self]
    rfl
  · exact preimage_extChartAt_target_mem_nhdsWithin v
  · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffWithinAt_preimage_modelWithCorners_target v h

lemma MDerivAlong_eq' {p : M} (v : TangentSpace I p) (f : M → ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p)
    (h : ((fun (i : ℝ) ↦ (extChartAt I p) p + i • (mvfderiv I (extChartAt I p) p) v) ⁻¹'
        I.target).Nontrivial) :
    letI y := (mvfderiv I (extChartAt I p) p) v
    MDerivAlongWithin f v ((fun (i : ℝ) ↦ (extChartAt I p p) + i • y) ⁻¹' I.target) 0 1 =
      mvfderiv I f p v := by
  unfold MDerivAlongWithin
  let y := (mvfderiv I (extChartAt I p) p) v
  rw [← mvfderivWithin_eq_fderivWithin]
  change (d[(fun (i : ℝ ) ↦ (extChartAt I p) p + i • y) ⁻¹' I.target] (f ∘ AlongFun v) 0) 1 =
    (d% f p) v
  --rw [mvfderiv_comp_mfderivWithin 0]
  set U := (fun (i : ℝ) ↦ (extChartAt I p p) + i • y) ⁻¹' I.target
  have := ((alongFun_apply_zero v).symm ▸ hf)
  rw [mvfderiv_comp_mfderivWithin 0 ((alongFun_apply_zero v).symm ▸ hf)
    (mdifferentiableWithinAt_alongFun v)]
  · rw [ContinuousLinearMap.comp_apply, alongFun_apply_zero v]
    congr
    exact mvfderivWithin_alongFun' v h
  · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffWithinAt_preimage_modelWithCorners_target v h

lemma MDerivAlong_eq'' {p : M} (v : TangentSpace I p) (f : M → ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p)
    (h : ((fun (i : ℝ) ↦ (extChartAt I p) p + i • (mvfderiv I (extChartAt I p) p) v) ⁻¹'
        I.target).Nontrivial) :
    MDerivAlongWithin f v (AlongFunPreimIn v (extChartAt I p).source) 0 1 = mvfderiv I f p v := by
  rw [← MDerivAlong_eq' v f hf h]
  unfold MDerivAlongWithin
  rw [fderivWithin_congr_set]
  refine nhdsWithin_eq_iff_eventuallyEq.mp ?_
  apply nhdsWithin_of_mem_of_subset
  · exact alongFunPreimIn_extChartAt_target_mem_nhdsWithin v
  · exact alongFunPreimIn_subset v (extChartAt I p).source

example {p : M} (v : TangentSpace I p) (f : M → ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p)
    (h : ((fun (i : ℝ) ↦ (extChartAt I p) p + i • (mvfderiv I (extChartAt I p) p) v) ⁻¹'
        I.target).Nontrivial) :
    MDerivAlongWithin f v (Ici (0 : ℝ)) 0 1 = mvfderiv I f p v := by
  rw [← MDerivAlong_eq' v f hf h]
  unfold MDerivAlongWithin
  rw [fderivWithin_congr_set]
  refine nhdsWithin_eq_iff_eventuallyEq.mp ?_
  refine Eq.symm (nhdsWithin_of_mem_of_subset ?_ ?_)
  · sorry
  · sorry

lemma differentiableWithinAt_precomp_alongFun {p : M}
    (v : TangentSpace I p)
    (f : M → ℝ) (hf : MDiffAt f p) (U : Set M) :
    DifferentiableWithinAt ℝ (f ∘ AlongFun v) (AlongFunPreimIn v U) 0 := by
  rw [← mdifferentiableWithinAt_iff_differentiableWithinAt]
  apply MDifferentiableWithinAt.comp 0 ?_ (mdifferentiableWithinAt_alongFun_alongFunPreimIn v U)
    subset_preimage_univ
  rw [alongFun_apply_zero v]
  exact hf.mdifferentiableWithinAt

lemma differentiableAt_precomp_alongFun_of_eq_zero {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0 = 0)
    (f : M → ℝ) (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f p) :
    DifferentiableAt ℝ (f ∘ AlongFun v) 0 := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  apply MDifferentiableAt.comp 0 ?_ (mdifferentiableAt_alongFun hp v hv)
  rw [alongFun_apply_zero v]
  exact hf.mdifferentiableWithinAt

lemma MDerivAlong_eq {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (f : M → ℝ) (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f p) :
    MDerivAlongWithin f v (Ici 0) 0 1 = mvfderiv (𝓡∂ n) f p v := by
  rw [le_iff_eq_or_lt] at hv
  rcases hv with hv | hv
  · rw [MDerivAlongWithin_subset v f (t := univ) (subset_univ _) (uniqueDiffWithinAt_Ici 0)
      (differentiableAt_precomp_alongFun_of_eq_zero hp v hv.symm f hf).differentiableWithinAt]
    rw [← alongFunPreimIn_extChartAt_source_of_eq_zero hp v hv.symm]
    apply MDerivAlong_eq' v f hf
    rw [alongFunPreimIn_extChartAt_source_of_eq_zero hp v hv.symm]
    exact nontrivial_univ
  · rw [← alongFunPreimIn_extChartAt_source hp v hv]
    apply MDerivAlong_eq' v f hf
    rw [alongFunPreimIn_extChartAt_source hp v hv]
    -- lemma?
    use 1, by simp, 0, self_mem_Ici, zero_ne_one.symm

-- this would give us a generalisation below but is kind of annoying to show...
lemma mderivAlongWithin_eq_zero_of_not_mdifferentiableAt {p : M} (v : TangentSpace I p)
    (f : M → ℝ) (hf : ¬ MDiffAt f p) (hv : v ≠ 0) :
    (MDerivAlongWithin f v (Ici 0) 0) = 0 := by
  unfold MDerivAlongWithin

  sorry

lemma idhoa {p : M}
    (v : TangentSpace I p)
    (hv : 1 ∈ posTangentConeAt (AlongFunPreimIn v (extChartAt I p).source) 0) : ∃ ε > 0,
    (fun (i : ℝ) ↦ (extChartAt I p) p + i • (d% (extChartAt I p) p) v) '' Icc 0 ε ⊆ I.target := by
  simp_rw [image_subset_iff]
  suffices
      (fun (i : ℝ) ↦ (extChartAt I p) p + i • (d% (extChartAt I p) p) v) ⁻¹' I.target ∈ 𝓝[≥] 0 from
    mem_nhdsGE_iff_exists_Icc_subset.mp this
  apply ContinuousWithinAt.preimage_mem_nhdsWithin' (by fun_prop)
  -- really I only need this part

  sorry

lemma mem_nds {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (s : Set M) (hs : s ∈ nhds p) :
    AlongFun v ⁻¹' s ∈ 𝓝[≥] 0 := by
  apply ContinuousWithinAt.preimage_mem_nhdsWithin
  · apply ContinuousWithinAt.comp_of_mem_nhdsWithin_image
    · apply (continuousOn_extChartAt_symm p).continuousWithinAt
      rw [zero_smul, add_zero]
      exact mem_extChartAt_target p
    · fun_prop
    · rw [zero_smul, add_zero]
      apply nhdsWithin_mono (t := {x | 0 ≤ x.ofLp 0 })
      · rw [image_subset_iff]
        rw [ModelWithCorners.isBoundaryPoint_iff,
          frontier_range_modelWithCornersEuclideanHalfSpace n, mem_ofPred] at hp
        intro x hx
        simp [-extChartAt, ← hp, mul_nonneg hx hv]
      · rw [← range_modelWithCornersEuclideanHalfSpace n]
        exact extChartAt_target_mem_nhdsWithin p
  rw [alongFun_apply_zero v]
  exact hs

omit [IsManifold I ∞ M] in
lemma mem_nhds' {p : M} (v : TangentSpace I p)
    (s : Set M) (hps : p ∈ s) (hv : AlongFunPreimIn v s ∈ 𝓝[>] 0) :
    AlongFunPreimIn v s ∈ 𝓝[≥] 0 := by
  rw [← Ioi_union_left, nhdsWithin_union]
  refine ⟨hv, ?_⟩
  simp [AlongFunPreimIn, hps]

lemma mem_nhds_ici {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (s : Set M) (hs : s ∈ nhds p) :
    AlongFunPreimIn v s ∈ 𝓝[≥] 0 := by
  unfold AlongFunPreimIn
  apply inter_mem
  · exact mem_nds hp v hv s hs
  · apply ContinuousWithinAt.preimage_mem_nhdsWithin' (by fun_prop)
    rw [zero_smul, add_zero]
    -- I also use this whole rest of the proof above
    -- write a lemma
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
        exact smul_nonneg hx hv
    · rw [extChartAt_coe p]
      rw [extChartAt_target (𝓡∂ n) p]
      simp only [comp_apply, inter_mem_iff]
      refine ⟨?_, ?_⟩
      · apply (𝓡∂ n).continuousWithinAt_symm.preimage_mem_nhdsWithin
        rw [ModelWithCorners.left_inv]
        exact chart_target_mem_nhds (EuclideanHalfSpace n) p
      · rw [range_modelWithCornersEuclideanHalfSpace n]
        exact self_mem_nhdsWithin

lemma mem_nhds_ioi {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (s : Set M) (hs : s ∈ nhds p) :
    AlongFunPreimIn v s ∈ 𝓝[>] 0 :=
  nhdsWithin_mono _ Ioi_subset_Ici_self (mem_nhds_ici hp v hv s hs)

-- I'm not sure that `hv` is the best assumption
-- maybe one should assume that there is a positive element in AlongFunPreimIn
theorem MDerivAlongWithin_alongFunPreimIn' {p : M}
    (v : TangentSpace I p)
    (f : M → ℝ) (U : Set M) (hU : p ∈ U) (hv : AlongFunPreimIn v U ∈ 𝓝[>] 0)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p) :
    MDerivAlongWithin f v (AlongFunPreimIn v U) 0 =
      MDerivAlongWithin f v (Ici (0 : ℝ)) 0 := by
  symm
  refine fderivWithin_of_mem_nhdsWithin ?_ ?_ ?_
  · exact mem_nhds' v U hU hv
  · exact uniqueDiffWithinAt_Ici 0
  · exact differentiableWithinAt_precomp_alongFun v f hf U

theorem MDerivAlongWithin_alongFunPreimIn {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (f : M → ℝ) (U : Set M) (hU : U ∈ 𝓝 p)
    (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f p) :
    MDerivAlongWithin f v (AlongFunPreimIn v U) 0 =
      MDerivAlongWithin f v (Ici (0 : ℝ)) 0 :=
  MDerivAlongWithin_alongFunPreimIn' v f U (mem_of_mem_nhds hU) (mem_nhds_ioi hp v hv U hU) hf

-- we need to say that `v` is inward pointing (or tangent to the boundary I think) somehow.
-- I am not sure how to best state this
-- at this point
omit [IsManifold I ∞ M] in
theorem IsLocalMinOn.mderivAlongWithin_nonneg_alongFunPreimIn' {p : M}
    (v : TangentSpace I p) (f : M → ℝ)
    (s : Set M) (hv : AlongFunPreimIn v s ∈ 𝓝[>] 0)
    (h : IsLocalMinOn f s p)
    (hs : s ∈ nhds p) :
    letI t := AlongFunPreimIn v s
    (0 : ℝ) ≤ MDerivAlongWithin f v t 0 1 := by
  apply IsLocalMinOn.fderivWithin_nonneg ?_ ?_
  · apply IsLocalMinOn.comp_continuousOn
    · simpa [AlongFun] using h
    · exact inter_subset_left
    · apply (continuousOn_extChartAt_symm p).comp
      · fun_prop
      · intro
        simp [AlongFunPreimIn]
    · simp [AlongFunPreimIn, alongFun_apply_zero, mem_of_mem_nhds hs]
  · simp [one_mem_posTangentConeAt_iff_mem_closure, mem_closure_iff_nhdsWithin_neBot,
      nhdsWithin_inter_of_mem' hv, ← mem_closure_iff_nhdsWithin_neBot (s := Ioi (0 : ℝ))]

omit [IsManifold I ∞ M] in
theorem IsLocalMin.mderivAlongWithin_nonneg_alongFunPreimIn' {p : M}
    (v : TangentSpace I p) (f : M → ℝ)
    (hv : AlongFunPreimIn v (extChartAt I p).source ∈ 𝓝[>] 0)
    (h : IsLocalMin f p) :
    letI t := (AlongFunPreimIn v (extChartAt I p).source)
    (0 : ℝ) ≤ MDerivAlongWithin f v t 0 1 :=
  (h.on (extChartAt I p).source).mderivAlongWithin_nonneg_alongFunPreimIn' _ _ _ hv
    (extChartAt_source_mem_nhds p)

omit [IsManifold I ∞ M] in
theorem IsLocalMinOn.mderivAlongWithin_nonneg_preimage_modelWithCorners_target {p : M}
    (v : TangentSpace I p) (f : M → ℝ)
    (s : Set M) (hv : AlongFunPreimIn v s ∈ 𝓝[>] 0)
    (h : IsLocalMinOn f s p)
    (hs : s ∈ nhds p) :
    letI t := (fun i ↦ (extChartAt I p) p + i • (d% (extChartAt I p) p) v) ⁻¹' I.target
    (0 : ℝ) ≤ MDerivAlongWithin f v t 0 1 := by
  sorry

theorem IsLocalMinOn.mderivAlongWithin_nonneg_alongFunPreimIn {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (f : M → ℝ)
    (s : Set M) (h : IsLocalMinOn f s p) (hs : s ∈ nhds p) :
    letI t := AlongFunPreimIn v s
    (0 : ℝ) ≤ MDerivAlongWithin f v t 0 1 :=
  h.mderivAlongWithin_nonneg_alongFunPreimIn' v f s (mem_nhds_ioi hp v hv s hs) hs

theorem IsLocalMin.mderivAlongWithin_nonneg' {p : M}
    (v : TangentSpace I p) (hv : AlongFunPreimIn v univ ∈ 𝓝[>] 0)
    (f : M → ℝ) (hf : MDiffAt f p) (hfp : IsLocalMin f p) :
    (0 : ℝ) ≤ MDerivAlongWithin f v (Ici 0) 0 1 := by
  rw [← MDerivAlongWithin_alongFunPreimIn' v f univ (mem_univ _) hv hf]
  exact (hfp.on univ).mderivAlongWithin_nonneg_alongFunPreimIn' v f univ hv univ_mem

-- we should also be able to prove this for the case where `hf` doesn't hold
-- but this is quite a bit of work
theorem IsLocalMin.mderivAlongWithin_nonneg {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (f : M → ℝ) (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f p) (hfp : IsLocalMin f p) :
    (0 : ℝ) ≤ MDerivAlongWithin f v (Ici 0) 0 1 := by
  rw [← MDerivAlongWithin_alongFunPreimIn hp v hv f univ univ_mem hf]
  exact (hfp.on univ).mderivAlongWithin_nonneg_alongFunPreimIn hp v hv f univ univ_mem

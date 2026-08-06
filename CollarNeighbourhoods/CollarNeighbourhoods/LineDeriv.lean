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

theorem alongFunPreimIn_extChartAt_source_of_eq {M : Type*}
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
  have h1 : MDiffAt[(extChartAt I p).target] (extChartAt I p).symm
      ((extChartAt I p) p + (0 : ℝ) • (mvfderiv I (extChartAt I p) p) v) := by
    apply MDifferentiableWithinAt.mono (extChartAt_target_subset_range p)
    apply mdifferentiableWithinAt_extChartAt_symm
    simp [mem_extChartAt_target p, -extChartAt]
  have h2 : MDiffAt[((fun (i : ℝ) ↦ (extChartAt I p p) + i • y) ⁻¹' I.target)] (fun (i : ℝ) ↦
      (extChartAt I p) p + i • (mvfderiv I (extChartAt I p) p) v) 0 :=
    mdifferentiableWithinAt_const.add (mdifferentiableWithinAt_id.smul
      mdifferentiableWithinAt_const)
  apply ((mdifferentiableOn_alongFun v) 0 (zero_mem_AlongFunPreimIn v)).congr_nhds
  apply nhdsWithin_of_mem_of_subset
  · exact alongFunPreimIn_extChartAt_target_mem_nhdsWithin v
  · exact alongFunPreimIn_subset v (extChartAt I p).source

lemma mdifferentiableWithinAt_alongFun_alongFunPreimIn {p : M} (v : TangentSpace I p) (U : Set M) :
    MDiffAt[AlongFunPreimIn v U] (AlongFun v) (0 : ℝ) :=
  (mdifferentiableWithinAt_alongFun v).mono (alongFunPreimIn_subset v U)

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

lemma jsdoa {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M}
    (v : TangentSpace (𝓡∂ n) p) :
    MDiffAt[Ici 0] (fun (i : ℝ) ↦
      (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) 0 := by
  apply MDifferentiableWithinAt.add
  · exact mdifferentiableWithinAt_const
  · apply mdifferentiableWithinAt_id.smul
    exact mdifferentiableWithinAt_const

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
    rw [← alongFunPreimIn_extChartAt_source_of_eq hp v hv.symm]
    exact mdifferentiableWithinAt_alongFun v

lemma MDerivAlong_eq' {p : M} (hp : I.IsBoundaryPoint p)
    (v : TangentSpace I p)
    (f : M → ℝ) (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p)
    (hI : ∀ x y (_ : x ∈ range I) (_ : y ∈ range I), x + y ∈ (range I)) :
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
  · sorry
  · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    apply UniqueDiffOn.uniqueDiffWithinAt ?_ (by simp)
    apply uniqueDiffOn_convex
    · -- find some condition to impose to make this be convex



      intro x hx y hy s t hs ht h

      rw [mem_preimage, I.target_eq] at hx hy ⊢

      rw [add_smul, ← add_assoc]
      rw [smul_assoc]
      rw [smul_assoc]

      apply I.convex_range.add_smul_mem ?_ ?_ ⟨ht, by linarith⟩
      · apply I.convex_range.add_smul_mem (mem_range_self _) hx ⟨hs, by linarith⟩
      · rw [add_right_comm]
        apply I.convex_range.add_smul_mem
        · exact hy
        ·
          sorry
        · sorry
    · apply Nonempty.mono (preimage_interior_subset_interior_preimage (by fun_prop))
      rw [nonempty_preimage_iff]

      sorry


set_option backward.isDefEq.respectTransparency false in
lemma MDerivAlong_eq {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (f : M → ℝ) (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f p) :
    MDerivAlongWithin f v (Ici 0) 0 1 = mvfderiv (𝓡∂ n) f p v := by
  unfold MDerivAlongWithin
  let y := (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v
  rw [← mvfderivWithin_eq_fderivWithin]
  -- defeq fix
  change (d[Ici (0 : ℝ)] (f ∘ ↑(extChartAt (𝓡∂ n) p).symm ∘
      fun (i : ℝ) ↦ (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) 0)
      1 =
      (mvfderiv (𝓡∂ n) f p) v
  rw [mvfderiv_comp_mfderivWithin 0 ((helper1 v).symm ▸ hf)]
  · simp only [comp_apply, ContinuousLinearMap.comp_apply]
    rw [zero_smul, add_zero]
    rw [PartialEquiv.left_inv (extChartAt (𝓡∂ n) p) (mem_extChartAt_source p)]
    refine Eq.symm (DFunLike.congr rfl ?_)
    -- write a lemma
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
    rw [mfderivWithin_comp 0 (mdifferentiableWithinAt_extChartAt_symm (by simp)) (jsdoa v)]
    · -- the first rewrites fix defeq issues
      rw [comp_apply, zero_smul, add_zero, extChartAt_to_inv p, ContinuousLinearMap.comp_apply]
      -- fix more defeq issues
      change v =
        (mfderivWithin _ (𝓡∂ n) (extChartAt (𝓡∂ n) p).symm (range (𝓡∂ n)) ((extChartAt (𝓡∂ n) p) p))
          (((mfderivWithin _ _ fun i ↦ (extChartAt (𝓡∂ n) p) p + i •
              (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) (Ici 0) 0) 1)
      rw [h1, mfderivWithin_range_extChartAt_symm, mvfderiv_extChartAt_self]
      rfl
    · intro x hx
      simp [ModelWithCorners.isBoundaryPoint_iff,
        frontier_range_modelWithCornersEuclideanHalfSpace, -extChartAt,
        -modelWithCornersEuclideanHalfSpace_toFun] at hp
      simp [range_modelWithCornersEuclideanHalfSpace, ← hp, zero_add, mul_nonneg hx hv,
        -extChartAt, -modelWithCornersEuclideanHalfSpace_toFun, -mem_range]
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffWithinAt_Ici 0
  · exact mdifferentiableWithinAt_alongFun_euclideanHalfSpace hp v hv
  · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffWithinAt_Ici 0

-- keep working here
lemma mderivAlongWithin_eq_zero_of_not_mdifferentiableAt {p : M} (v : TangentSpace I p)
    (f : M → ℝ) (hf : ¬ MDiffAt f p) (hv : v ≠ 0) :
    (MDerivAlongWithin f v (Ici 0) 0) = 0 := by
  unfold MDerivAlongWithin

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
      · -- this should be a lemma
        rw [extChartAt_target (𝓡∂ n) p]
        rw [range_modelWithCornersEuclideanHalfSpace]
        apply inter_mem ?_ self_mem_nhdsWithin
        rw [← range_modelWithCornersEuclideanHalfSpace n]
        apply ContinuousWithinAt.preimage_mem_nhdsWithin
        · apply (𝓡∂ n).continuousOn_symm.continuousWithinAt
          exact mem_range_self _
        · simp [chart_target_mem_nhds]
  rw [alongFun_apply_zero v]
  exact hs

lemma mem_nhds {M : Type*}
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

theorem MDerivAlongWithin_alongFunPreimIn {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (f : M → ℝ) (U : Set M) (hU : U ∈ 𝓝 p)
    (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f p) :
    MDerivAlongWithin f v (AlongFunPreimIn v U) 0 =
      MDerivAlongWithin f v (Ici (0 : ℝ)) 0 := by
  unfold MDerivAlongWithin
  symm
  refine fderivWithin_of_mem_nhdsWithin ?_ ?_ ?_
  · exact mem_nhds hp v hv U hU
  · exact uniqueDiffWithinAt_Ici 0
  · -- make this a lemma
    rw [← mdifferentiableWithinAt_iff_differentiableWithinAt]
    apply MDifferentiableWithinAt.comp 0 ?_ (mdifferentiableWithinAt_alongFun_alongFunPreimIn v U)
      subset_preimage_univ
    rw [alongFun_apply_zero v]
    exact hf.mdifferentiableWithinAt

theorem IsLocalMinOn.mderivAlongWithin_nonneg_alongFunPreimIn {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (f : M → ℝ)
    (s : Set M) (h : IsLocalMinOn f s p) (hs : s ∈ nhds p) :
    letI t := AlongFunPreimIn v s
    (0 : ℝ) ≤ MDerivAlongWithin f v t 0 1 := by
  apply IsLocalMinOn.fderivWithin_nonneg
  · apply IsLocalMinOn.comp_continuousOn
    · simpa [AlongFun] using h
    · exact inter_subset_left
    · apply (continuousOn_extChartAt_symm p).comp
      · fun_prop
      · intro
        simp [AlongFunPreimIn]
    · simp [AlongFunPreimIn, mem_of_mem_nhds hs, alongFun_apply_zero]
  · simp [one_mem_posTangentConeAt_iff_mem_closure, mem_closure_iff_nhdsWithin_neBot,
      nhdsWithin_inter_of_mem' (nhdsWithin_mono 0
      Ioi_subset_Ici_self (mem_nhds hp v hv s hs))]
    simp [← mem_closure_iff_nhdsWithin_neBot]

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

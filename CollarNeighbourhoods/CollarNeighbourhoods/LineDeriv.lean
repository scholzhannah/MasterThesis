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
noncomputable def PartialEquivAlong {𝕜 : Type u_6} {E : Type u_7} [NormedField 𝕜]
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

noncomputable def AlongFun' {p : M} (v : TangentSpace I p) :
    PartialDiffeomorph 𝓘(ℝ, ℝ) I ℝ M ∞ where
  toFun :=
    (extChartAt I p).symm ∘ fun (i : ℝ) ↦ (extChartAt I p p) + i • (mvfderiv I (extChartAt I p) p) v
  invFun x := ‖(extChartAt I p) x - (extChartAt I p p)‖
  source := (fun (i : ℝ) ↦ (extChartAt I p p) + i • (mvfderiv I (extChartAt I p) p) v)
    ⁻¹' (extChartAt I p).target
  target := sorry
  map_source' := sorry
  map_target' := sorry
  left_inv' := sorry
  right_inv' := sorry
  open_source := sorry
  open_target := sorry
  contMDiffOn_toFun := sorry
  contMDiffOn_invFun := sorry

noncomputable def AlongFun {p : M} (v : TangentSpace I p) :=
  letI y := (mvfderiv I (extChartAt I p) p) v
  (extChartAt I p).symm ∘ fun (i : ℝ) ↦ (extChartAt I p p) + i • y

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
lemma alongFun_zero {p : M} (v : TangentSpace I p) : AlongFun v 0 = p := by
  simp [AlongFun]

#check mdifferentiableOn_extChartAt
#check mdifferentiableOn_extChartAt_symm

theorem mdifferentiableWithinAt_alongFun {p : M} (v : TangentSpace I p) (s : Set ℝ)
    (hs : (fun i ↦ (extChartAt I p) p + i • (d% (extChartAt I p) p) v) '' s ⊆
      (extChartAt I p).target) :
    MDiff[s] (AlongFun v) := by
  unfold AlongFun
  apply mdifferentiableOn_extChartAt_symm.comp ?_ (image_subset_iff.1 hs)
  rw [mdifferentiableOn_iff_differentiableOn]
  fun_prop


theorem MDerivAlongWithin_subset' {p : M} (v : TangentSpace I p) (f : M → ℝ) {s t : Set M}
    (st : s ⊆ t) (ht : UniqueDiffWithinAt ℝ (AlongFun v ⁻¹' s) 0) (h : MDiffAt[t] f p) :
    MDerivAlongWithin f v (AlongFun v ⁻¹' s) 0 = MDerivAlongWithin f v (AlongFun v ⁻¹' t) 0 := by
  apply fderivWithin_subset (preimage_mono st) ht
  rw [← mdifferentiableWithinAt_iff_differentiableWithinAt]
  rw [← alongFun_zero v] at h
  apply h.comp 0 ?_ (subset_of_eq rfl)
  apply mdifferentiableWithinAt_alongFun
  ·
    rw [image_subset_iff]
    unfold AlongFun
    rw [preimage_comp]
    apply preimage_mono

    sorry
  · rw [mem_preimage, alongFun_zero]
    sorry

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
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M}
    (v : TangentSpace (𝓡∂ n) p) :
    MDiffAt[Ici 0] (fun (i : ℝ) ↦
      (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) 0 := by
  apply MDifferentiableWithinAt.add
  · exact mdifferentiableWithinAt_const
  · apply mdifferentiableWithinAt_id.smul
    exact mdifferentiableWithinAt_const

lemma thinkofnamelater {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) (𝓡∂ n) (AlongFun v) (Ici (0 : ℝ)) (0 : ℝ) := by
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

/-- The manifold derivative of `extChartAt` at the basepoint is the identity. -/
lemma mvfderiv_extChartAt_self {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type u_4} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {x : M} :
    d% (extChartAt I x) x = ContinuousLinearMap.id 𝕜 E :=
  mfderiv_extChartAt_self

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

set_option backward.isDefEq.respectTransparency false in
lemma MDerivAlong_eq {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (f : M → ℝ)
    (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f p) :
    MDerivAlongWithin f v (Ici 0) 0 1 = mvfderiv (𝓡∂ n) f p v := by
  unfold MDerivAlongWithin
  letI y := (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v
  rw [← mvfderivWithin_eq_fderivWithin]
  -- defeq fix
  change (d[Ici (0 : ℝ)] (f ∘ ↑(extChartAt (𝓡∂ n) p).symm ∘
      fun (i : ℝ) ↦ (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) 0)
      1 =
      (mvfderiv (𝓡∂ n) f p) v
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
    have h2 : MDiffAt[Ici (0 : ℝ)] (fun (i : ℝ) ↦
        (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) 0 := by
      exact jsdoa (E := E) v
    rw [mfderivWithin_comp 0 (mdifferentiableWithinAt_extChartAt_symm (by simp)) h2]
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
  · exact thinkofnamelater (E := E) hp v hv
  · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffWithinAt_Ici 0

-- this is wrong
lemma continuousOn_alongFun_euclideanHalfSpace [TopologicalSpace M] {n : ℕ} [NeZero n]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (f : M → ℝ)
    (s : Set M) (h : IsLocalMinOn f s p) (hs : s ∈ nhds p) :
    ContinuousWithinAt (AlongFun v) (Ici 0) 0 := by
  unfold AlongFun


  sorry

lemma mem_nds {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
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
      apply nhdsWithin_mono (t := {x | 0 ≤x.ofLp 0 })
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
  rw [alongFun_zero v]
  exact hs

theorem IsLocalMinOn.mvfderivWithin_nonneg {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 ≤ (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (f : M → ℝ)
    (s : Set M) (h : IsLocalMinOn f s p) (hs : s ∈ nhds p) :
    letI t := AlongFun v ⁻¹' s
    (0 : ℝ) ≤ MDerivAlongWithin f v t 0 1 := by
  letI y := (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v
  let t' := AlongFun v ⁻¹'
    (s ∩ (extChartAt (𝓡∂ n) p).source)
  apply IsLocalMinOn.fderivWithin_nonneg
  · apply IsLocalMinOn.comp_continuousOn
    · simpa [AlongFun] using h
    · exact subset_of_eq rfl
    · apply (continuousOn_extChartAt_symm p).comp
      · fun_prop
      · intro x

        sorry
    · simp [mem_of_mem_nhds hs, alongFun_zero]
  · rw [one_mem_posTangentConeAt_iff_mem_closure]

    sorry

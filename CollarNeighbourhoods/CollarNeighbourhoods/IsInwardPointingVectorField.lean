/-
Copyright (c) 2026 Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Scholz
-/
module

public import CollarNeighbourhoods.IsInwardPointingNew
public import Mathlib.Geometry.Convex.Star
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Header-/

@[expose] public section

open Set Function Filter Module EuclideanSpace Convexity
open scoped Topology Manifold ContDiff

section

variable {M H : Type*} [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]

-- this is how we say that `M` is a smooth manifold
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {I : ModelWithCorners ℝ E H} {n : ℕ∞} [NeZero n] [IsManifold I n M]

variable (I M) in
include n in
lemma IsManifold_one_of_neZero : IsManifold I 1 M := by
  apply IsManifold.of_le (n := n)
  suffices n ≠ 0 by
    rw [ENat.one_le_iff_ne_zero_withTop]
    norm_cast
  exact NeZero.ne n

instance : NeZero (n : ℕ∞ω) where
  out := by
    norm_cast
    exact NeZero.out

-- `default - p`
variable (E) in
noncomputable def InwardPointingVec' (x : H) : TangentSpace I x :=
  letI y := (I.nonempty_interior.preimage' interior_subset).choose
  tangentSpaceCast I (I.symm (I x)) x (mfderiv[range I] I.symm (I x)
     ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (I x)).symm (I y - I x)))

variable (I E) in
noncomputable def InwardPointingVec (x : H) : TangentSpace I x :=
  letI y := (I.nonempty_interior.preimage' interior_subset).choose
  (mvfderivModelWithCorners I x).symm (I y - I x)

lemma mvfderiv_modelWithCorners_inwardPointingVec (x : H) :
    letI y := (I.nonempty_interior.preimage' interior_subset).choose
    d% I x (InwardPointingVec E I x) = I y - I x := by
  unfold InwardPointingVec
  rw [← comp_apply (f := mvfderiv I I x) (g := (mvfderivModelWithCorners I x).symm),
    coe_mvfderiv_modelWithCorners, Homeomorph.self_comp_symm, id_eq]

include n in
lemma IsInwardPointing_inwardPointingVec (x : H) :
    IsInwardPointingMinimal (I := I) (InwardPointingVec E I x) := by
  let y := (I.nonempty_interior.preimage' interior_subset).choose
  let hy : y ∈ I ⁻¹' interior (range I) :=
    (I.nonempty_interior.preimage' interior_subset).choose_spec
  suffices I y - I x ∈ interior (posTangentConeAt (range I) (I x)) by
    simpa [isInwardPointing_iff_extChartAt_mem_interior_posTangentConeAt (n := n),
      chartAt_self_eq, InwardPointingVec, -mvfderivModelWithCorners_symm_apply,
      coe_mvfderiv_modelWithCorners]
  apply I.convex_range.subset_interior_posTangentCone (mem_range_self x)
  use 1, one_pos
  simpa using hy

lemma Bundle.TotalSpace.coe_chart_tangentSpace {p : H} {v : TangentSpace I p}
    (x : H) (xv : TangentSpace I x) :
    (chartAt (ModelProd H E) (⟨p, v⟩ : Bundle.TotalSpace E (TangentSpace I))) ⟨x, xv⟩ =
      (x, (d% I x) xv) := by
  simp [Bundle.TotalSpace.toProd, I.mvfderiv_I]
  rfl

lemma extChartAt_tangent_inwardPointingVec (x : H) {p : H} {v : TangentSpace I p} :
    letI y := (I.nonempty_interior.preimage' interior_subset).choose
    (extChartAt I.tangent (⟨p, v⟩ : Bundle.TotalSpace E (TangentSpace I)))
      (T% (InwardPointingVec (I := I) E x)) = ⟨I x, I y - I x⟩ := by
  rw [extChartAt_coe, comp_apply]
  simp [Bundle.TotalSpace.coe_chart_tangentSpace, mvfderiv_modelWithCorners_inwardPointingVec x]

lemma contMDiff_inwardPointVec : CMDiff ∞ (T% (InwardPointingVec (I := I) E)) := by
  let y := (I.nonempty_interior.preimage' interior_subset).choose
  rw [contMDiff_iff_target]
  constructor
  · rw [← (tangentBundleModelSpaceHomeomorph (I := I)).comp_continuous_iff, comp_def,
      tangentBundleModelSpaceHomeomorph_coe, Bundle.TotalSpace.toProd]
    apply continuous_id'.prodMk
    refine Continuous.clm_apply ?_ ((continuous_sub_left (I y)).comp' I.continuous)
    rw [I.mfderivWithin_symm']
    exact continuous_of_const fun x y ↦ rfl
  · intro ⟨p, v⟩
    simp_rw [comp_def, extChartAt_tangent_inwardPointingVec]
    exact (I.contMDiff.prodMk_space (contMDiff_const.sub I.contMDiff)).contMDiffOn

variable (M I) in
noncomputable def InwardPointingVecWithinAt (p : M) : (q : M) → TangentSpace I q :=
    VectorField.mpullbackWithin I I (chartAt H p) (InwardPointingVec E I) (chartAt H p).source

include n in
lemma IsInwardPointing_inwardPointingVecWithinAt (p : M) (q : M) (hq : q ∈ (chartAt H p).source) :
    IsInwardPointingMinimal (InwardPointingVecWithinAt M I p q) := by
  unfold InwardPointingVecWithinAt VectorField.mpullbackWithin
  rw [mfderiv_chart_inverse_eq (n := n) p q hq]
  rw [isInwardPointing_iff_chartAt' hq (n := n)]
  rw [← coe_chartAtMFderiv (n := n) p hq]
  suffices IsInwardPointingMinimal (InwardPointingVec E I ((chartAt H p) q)) by
    convert this
    exact (chartAtMFderiv n p hq).apply_symm_apply (c := InwardPointingVec E I ((chartAt H p) q))
  exact IsInwardPointing_inwardPointingVec (n := n) _

-- **Question**: is this assumption okay?

lemma contMDiffOn_inwardPointingWithinVecAt [CompleteSpace E] [IsManifold I (n + 1) M] (p : M) :
    letI := IsManifold_one_of_neZero M I (n := n)
    CMDiff[(chartAt H p).source] n (T% (InwardPointingVecWithinAt M I p)) := by
  let := IsManifold_one_of_neZero M I (n := n)
  have : (chartAt H p).source = (chartAt H p).source ∩ (chartAt H p) ⁻¹' (chartAt H p).target := by
    rw [left_eq_inter]
    exact (chartAt H p).source_preimage_target
  rw [this]
  apply ContMDiffOn.mpullbackWithin_vectorField_inter (m := n) (n := n + 1)
  · exact (contMDiff_inwardPointVec.of_le ENat.LEInfty.out).contMDiffOn
  · exact contMDiffOn_chart
  · intro x ⟨hx, _⟩
    rw [mfderivWithin_of_isOpen (chartAt H p).open_source hx]
    use chartAtMFderiv n p hx
    exact coe_chartAtMFderiv p hx
  · exact (chartAt H p).open_source.uniqueMDiffOn
  · norm_cast

lemma contMDiffOn_inwardPointingWithinVecAt_infty [CompleteSpace E] [IsManifold I ∞ M] (p : M) :
    CMDiff[(chartAt H p).source] ∞ (T% (InwardPointingVecWithinAt M I p)) := by
  have : IsManifold I (∞ + 1) M := by
    rw [ENat.coe_top_add_one]
    infer_instance
  have : NeZero (⊤ :  ℕ∞) := by
    constructor
    exact ENat.top_ne_zero
  exact contMDiffOn_inwardPointingWithinVecAt _

-- **Question** : are these assumptions okay?
variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

-- I need to take a partition of unity that is positive on the sets
variable (M I) in
noncomputable def SmoothInwardPointingVec (p : M) : TangentSpace I p :=
  letI f := (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose
  ∑ᶠ (i : M), (f i) p • (InwardPointingVecWithinAt M I) i p

-- I should probably write a general lemma that one can combine vector field in this way

lemma contMDiff_smoothInwardPointingVec : CMDiff ∞ (T% (SmoothInwardPointingVec M I)) := by
  let f := (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose
  have hf : f.IsSubordinate fun x ↦ (chartAt H x).source :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose_spec
  apply ContMDiff.finsum_section_of_locallyFinite (f.locallyFinite.smul_left _)
  intro i
  exact (f i).contMDiff.contMDiffOn.smul_section_of_tsupport (chartAt H i).open_source (hf i)
    (contMDiffOn_inwardPointingWithinVecAt_infty i)

include n in
lemma isInwardPointing_smoothInwardPointingVec (p : M) :
    IsInwardPointingMinimal (SmoothInwardPointingVec M I p) := by
  let f := (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose
  let hf : f.IsSubordinate fun x ↦ (chartAt H x).source :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose_spec
  unfold SmoothInwardPointingVec
  apply SmoothPartitionOfUnity.finsum_smul_mem_convex _ (mem_univ _) ?_
    (convex_isInwardPointing (n := n))
  intro i (hi : f i p ≠ 0)
  apply IsInwardPointing_inwardPointingVecWithinAt (n := n)
  contrapose hi
  exact image_eq_zero_of_notMem_tsupport (notMem_subset (hf i) hi)

variable (I) in
noncomputable def InwardPointingFlow (i : ℝ) (x : H) : H :=
  letI y := (I.nonempty_interior.preimage' interior_subset).choose
  I.symm (I x + (i • (I y - I x)))

noncomputable def InwardPointingFlow' : PartialDiffeomorph (𝓘(ℝ, ℝ).prod I) I (ℝ × H) H n where
  toFun :=
    letI y := (I.nonempty_interior.preimage' interior_subset).choose
    fun ⟨i, x⟩ ↦ I.symm ((1 - i) • I x + i • I y)
  invFun :=
    letI y := (I.nonempty_interior.preimage' interior_subset).choose
    letI j := sorry
    sorry
  source := (Ico 0 1) ×ˢ (I.boundary H)
  target := sorry
  map_source' := sorry
  map_target' := sorry
  left_inv' := sorry
  right_inv' := sorry
  open_source := sorry
  open_target := sorry
  contMDiffOn_toFun := sorry
  contMDiffOn_invFun := sorry

omit [NeZero n] [FiniteDimensional ℝ E] in
lemma contMDiffOn_inwardPointingFlow :
    CMDiff[(Icc 0 1) ×ˢ (I.boundary H)] n (Function.uncurry (InwardPointingFlow I)) := by
  let y := (I.nonempty_interior.preimage' interior_subset).choose
  unfold InwardPointingFlow
  rw [uncurry_def]
  simp_rw [← comp_def (f := I.symm)]
  apply I.contMDiffOn_symm.comp
  · exact ((I.contMDiff.comp contMDiff_snd).add
      (contMDiff_fst.smul (contMDiff_const.sub (I.contMDiff.comp contMDiff_snd)))).contMDiffOn
  rw [prod_sub_preimage_iff]
  intro i x hi hx
  nth_rw 1 [smul_sub, ← add_comm_sub, ← one_smul ℝ (I x), ← sub_smul]
  exact I.convex_range (mem_range_self x) (mem_range_self y)
    (by simp [hi.2]) hi.1 (sub_add_cancel 1 i)



lemma isImmersion_inwardPointingFlow (i : ℝ) (x : H) (hi : i ∈ Icc 0 1) (hx : x ∈ I.boundary H) :
    Manifold.IsImmersionAt (𝓘(ℝ, ℝ).prod I) I n
      (Function.uncurry (InwardPointingFlow I)) ⟨i, x⟩ := by
  let y := (I.nonempty_interior.preimage' interior_subset).choose
  unfold InwardPointingFlow
  rw [uncurry_def]
  simp_rw [← comp_def (f := I.symm)]

  sorry

omit [FiniteDimensional ℝ E] in
lemma inwardPointingFlow_apply_boundary (x : H) : InwardPointingFlow I 0 x = x := by
  simp [InwardPointingFlow]



noncomputable def LocalInwardPointingFlowout (i : ℝ) (p q : M) : M :=
  (chartAt H p).symm (InwardPointingFlow I i (chartAt H p q))

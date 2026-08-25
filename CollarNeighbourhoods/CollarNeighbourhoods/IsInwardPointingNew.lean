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
public import CollarNeighbourhoods.LineDeriv

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

-- should this be `HasMFDerivAt[Ici 0]` or `HasMFDerivAt[Ico 0 ε]`
def IsRealizable {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (γ : ℝ → M) (ε : ℝ) (_ : ε > 0) (_ : CMDiff[Ico 0 ε] ∞ γ),
    γ 0 = p ∧ mfderiv[Ici 0] γ (0 : ℝ) 1 = v

-- should this be `HasMFDerivAt[Ici 0]` or `HasMFDerivAt[Ico 0 ε]`
def IsRealizableMinimal {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (γ : ℝ → M) (_ : MDiffAt[Ici 0] γ 0), γ 0 = p ∧ mfderiv[Ici 0] γ (0 : ℝ) 1 = v

-- should this be `HasMFDerivAt[Ici 0]` or `HasMFDerivAt[Ico 0 ε]`
def IsRealizable' {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (γ : ℝ → M) (ε : ℝ) (_ : ε > 0) (_ : CMDiff[Ico 0 ε] ∞ γ),
    γ 0 = p ∧ HasMFDerivAt[Ici 0] γ (0 : ℝ)
    ((ContinuousLinearMap.toSpanSingleton ℝ v).comp
      (NormedSpace.fromTangentSpace 1).toContinuousLinearMap)

def IsInwardPointing {p : M} (v : TangentSpace I p) : Prop :=
  v ∈ interior {v | IsRealizable v}

def IsInwardPointingMinimal {p : M} (v : TangentSpace I p) : Prop :=
  v ∈ interior {v | IsRealizableMinimal v}

def IsTangent {p : M} (v : TangentSpace I p) : Prop :=
  v ∈ frontier {v | IsRealizable v}

def IsOutwardPointing {p : M} (v : TangentSpace I p) : Prop :=
  ¬ IsRealizable v

omit [IsManifold I ∞ M] in
lemma PartialDiffeomorph.isRealizable_apply {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (v : TangentSpace I p) (f : PartialDiffeomorph I I M M' ∞)
    (hp : p ∈ f.source) (hv : IsRealizableMinimal v) :
    IsRealizableMinimal (mfderiv% f p v) := by
  obtain ⟨γ, hγ, hγp, hγv⟩ := hv
  have hf := f.mdifferentiableAt (ne_of_beq_false rfl) (hγp ▸ hp)
  use f ∘ γ, hf.comp_mdifferentiableWithinAt 0 hγ, by simp [hγp]
  rw [mfderiv_comp_mfderivWithin 0 hf hγ ?_, ContinuousLinearMap.comp_apply, hγv, hγp]
  rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
  exact uniqueDiffWithinAt_Ici 0

@[simps!]
noncomputable def TangentSpace.of_eq (I : ModelWithCorners ℝ E H) {p q : M} (h : p = q) : TangentSpace I p ≃ₜ TangentSpace I q :=
    Homeomorph.refl (TangentSpace I p)

@[simps]
noncomputable def PartialDiffeomorph.mfderiv {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (f : PartialDiffeomorph I I M M' ∞)
    (hp : p ∈ f.source) : Homeomorph (TangentSpace I p) (TangentSpace I (f p)) where
  toFun := mfderiv% f p
  invFun := TangentSpace.of_eq I (f.symm.leftInvOn (f.map_source' hp)) ∘ mfderiv% f.symm (f p)
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

omit [IsManifold I ∞ M] in
lemma PartialDiffeomorph.leftInverse_mfderiv_symm {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H M'] (p : M) (f : PartialDiffeomorph I I M M' ∞)
    (hp : p ∈ f.source) : LeftInverse (mfderiv% f.symm (f p)) (mfderiv% f p) :=
  (f.mfderiv p hp).left_inv

omit [IsManifold I ∞ M] in
lemma PartialDiffeomorph.rightInverse_mfderiv_symm {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H M'] (p : M) (f : PartialDiffeomorph I I M M' ∞)
    (hp : p ∈ f.source) : RightInverse (mfderiv% f.symm (f p)) (mfderiv% f p) :=
  (f.mfderiv p hp).right_inv

omit [IsManifold I ∞ M] in
lemma PartialDiffeomorph.isHomeomorph_mfderiv {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (f : PartialDiffeomorph I I M M' ∞)
    (hp : p ∈ f.source) : IsHomeomorph (mfderiv% f p) :=
  (mfderiv p f hp).isHomeomorph

-- not sure if this is even true
-- might be some conditions missing
lemma IsHomeomorph.isRealizable_iff {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (q : M') (v : TangentSpace I p) (h : TangentSpace I p ≃ₜ TangentSpace I q) :
    IsRealizableMinimal v ↔ IsRealizableMinimal (h v) := by

  sorry

omit [IsManifold I ∞ M] in
lemma PartialDiffeomorph.isRealizable_iff {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (v : TangentSpace I p) (f : PartialDiffeomorph I I M M' ∞)
    (hp : p ∈ f.source) :
    IsRealizableMinimal v ↔ IsRealizableMinimal (mfderiv% f p v) := by
  refine ⟨fun hv ↦ isRealizable_apply p v f hp hv, ?_⟩
  have : v = (mfderiv% f.symm (f p)) ((mfderiv% f p) v) := by
    -- use proof def above to proof this
    rw [← mfderiv_comp_apply p ?_ (f.mdifferentiableAt (ne_of_beq_false rfl) hp) v]
    · rw [← mfderivWithin_of_isOpen f.open_source hp, mfderivWithin_congr_of_mem (f := id) ?_ hp]
      · rw [mfderivWithin_of_isOpen f.open_source hp, comp_apply, mfderiv_id]
        rfl
      exact f.leftInvOn
    · apply f.symm.mdifferentiableAt (ne_of_beq_false rfl)
      exact f.map_source' hp
  intro hv
  rw [this]
  nth_rw 1 [← f.left_inv hp]
  apply f.symm.isRealizable_apply _ _ ?_ hv
  simp [f.map_source' hp]

lemma PartialDiffeomorph.interior_isRealizable_eq {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (v : TangentSpace I p) (f : PartialDiffeomorph I I M M' ∞)
    (hp : p ∈ f.source) :
    interior {v | IsRealizableMinimal v} =
      (mfderiv% f p) '' interior {v | IsRealizableMinimal v} := by
  rw [(isHomeomorph_mfderiv p f hp).image_interior]
  congrm interior ?_
  ext w
  rw [mem_ofPred, f.symm.isRealizable_iff (f p) w (f.map_source' hp)]
  rw [show mfderiv% f p = ⇑(mfderiv p f hp).toEquiv from rfl,
    mem_image_equiv (f := (mfderiv p f hp).toEquiv)]
  rw [mem_ofPred]
  change IsRealizableMinimal ((mfderiv% f.symm (f p)) w) ↔
    IsRealizableMinimal ((mfderiv p f hp).symm w)
  rw [f.mfderiv_symm_apply p hp w]
  sorry

lemma PartialDiffeomorph.isInwardPointing_iff {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (v : TangentSpace I p) (f : PartialDiffeomorph I I M M' ∞)
    (hp : p ∈ f.source) :
    IsInwardPointingMinimal v ↔ IsInwardPointingMinimal (mfderiv% f p v) := by
  unfold IsInwardPointingMinimal
  have : {v | IsRealizableMinimal v} = {v | IsRealizableMinimal (mfderiv% f p v)} := by
    ext v
    simp [f.isRealizable_iff p v hp]
  rw [this]

  constructor
  · sorry
  · sorry

theorem Convex.add_smul_mem_icc {𝕜 E : Type*} [Field 𝕜] [PartialOrder 𝕜] [PosMulReflectLT 𝕜]
    [AddCommGroup E]
    [Module 𝕜 E] {s : Set E} [AddRightMono 𝕜] (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s) {r : 𝕜}
    (hr : 0 < r)
    (hy : x + r • y ∈ s) {t : 𝕜} (ht : t ∈ Set.Icc 0 r) : x + t • y ∈ s := by
  rw [← div_mul_cancel₀ t hr.ne.symm, mul_smul]
  apply hs.add_smul_mem hx hy
  refine ⟨div_nonneg ht.1 hr.le, (div_le_one hr).mpr ht.2⟩

theorem ModelWithCorners.mfderivWithin_symm {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H]
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

omit [NormedSpace ℝ E] in
lemma TangentSpace.dist_eq [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {p : H}
    {v w : TangentSpace I p} : dist v w = dist (d% I p v) (d% I p w) :=
  rfl

lemma isRealizable_of_mem_range {p : H} {v : TangentSpace I p}
    {ε : ℝ} (hε : ε > 0) (h : I p + ε • d% I p v ∈ (range I)) :
    IsRealizable v := by
  unfold IsRealizable
  let γ : ℝ → H := I.symm ∘ fun i ↦ I p + i • mvfderiv I I p v
  have hεI : Ico 0 ε ⊆ (fun i ↦ I p + i • mvfderiv I I p v) ⁻¹' range I := by
    intro i hi
    exact I.convex_range.add_smul_mem_icc (mem_range_self p) hε h
      (Ico_subset_Icc_self hi)
  have : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Ico 0 ε) := by
    apply I.contMDiffOn_symm.comp ?_ hεI
    rw [contMDiffOn_iff_contDiffOn]
    fun_prop
  use γ, ε, hε, this, by simp [γ]
  have h0 := (uniqueDiffOn_Ico 0 ε).uniqueDiffWithinAt (left_mem_Ico.mpr hε)
  unfold γ
  rw [MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin (s := Ico 0 ε)]
  · have hI : MDifferentiableWithinAt 𝓘(ℝ, E) I I.symm (range I) (I p) := by
      exact I.mdifferentiableWithinAt_symm (mem_range_self p)
    rw [mfderivWithin_comp_of_eq hI (u := range I) (g := I.symm)]
    · -- defeq wise pretty broken
      rw [ModelWithCorners.mfderivWithin_symm I (mem_range_self p)]
      change mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (
          fun (i : ℝ) ↦ I p + i • mvfderiv I I p v) (Ico 0 ε) 0 1 = v
      rw [zero_smul, add_zero, mfderivWithin_eq_fderivWithin, fderivWithin_const_add]
      rw [fderivWithin_smul_const h0
        differentiableWithinAt_fun_id]
      rw [fderivWithin_fun_id h0]
      rw [I.mvfderiv]
      rw [ContinuousLinearMap.smulRight_id]
      -- fixing some defeq issue
      change (ContinuousLinearMap.toSpanSingleton ℝ
        ((ContinuousLinearMap.id ℝ (TangentSpace I p)) v)) 1 = v
      rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
      rfl
    · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      fun_prop
    · exact hεI
    · exact h0.uniqueMDiffWithinAt
    · simp
  · exact this.mdifferentiableOn (ne_of_beq_false rfl) 0 (left_mem_Ico.mpr hε)
  · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffWithinAt_Ici 0
  · exact Ico_mem_nhdsGE hε

lemma isInwardPointing_of_mem_interior_range {p : H} {v : TangentSpace I p}
    {ε : ℝ} (hε : ε > 0) (h : I p + ε • d% I p v ∈ interior (range I)) :
    IsInwardPointing v := by
  unfold IsInwardPointing
  rw [mem_interior]
  rw [← IsOpen.mem_nhds_iff isOpen_interior, Metric.mem_nhds_iff] at h
  obtain ⟨δ, hδ, hδI⟩ := h
  use Metric.ball v (δ / ε)
  refine ⟨?_, Metric.isOpen_ball, Metric.mem_ball_self (div_pos hδ hε)⟩
  intro w hw
  apply isRealizable_of_mem_range hε
  apply interior_subset
  apply hδI
  simpa [dist_smul₀, abs_of_pos hε, ← lt_div_iff₀' hε, ← TangentSpace.dist_eq] using hw

lemma isInwardPointing_iff {p : H} (hp : I.IsBoundaryPoint p) (v : TangentSpace I p) :
    IsInwardPointing v ↔ ∃ (ε : ℝ) (_ : ε > 0), I p + ε • d% I p v ∈ interior (range I) := by
  constructor
  · intro h
    by_contra! hv
    unfold IsInwardPointing at h

    sorry
  · intro ⟨ε, hε, h⟩
    unfold IsInwardPointing
    rw [mem_interior]
    rw [← IsOpen.mem_nhds_iff isOpen_interior, Metric.mem_nhds_iff] at h
    obtain ⟨δ, hδ, hδI⟩ := h
    --let f := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (I p))
    --let f := mvfderiv I I p
    use Metric.ball v (δ / ε)
    refine ⟨?_, Metric.isOpen_ball, Metric.mem_ball_self (div_pos hδ hε)⟩
    intro w hw
    apply isRealizable_of_mem_range hε
    apply interior_subset
    apply hδI
    simpa [dist_smul₀, abs_of_pos hε, ← lt_div_iff₀' hε, ← TangentSpace.dist_eq] using hw


-- see `https://arxiv.org/pdf/1810.05999` (only continuous curve :((()
-- I think the backward direction might be really hard to show
lemma isRealizable_iff_posTangentCone {p : H} (hp : I.IsBoundaryPoint p) (v : TangentSpace I p) :
    IsRealizable v ↔ v ∈ posTangentConeAt (range I) (I p) := by
  constructor
  · intro ⟨γ, hγ, ε⟩
    sorry

  · intro h

    sorry

lemma huahoaa {p : H} (hp : I.IsBoundaryPoint p) :
    { v : TangentSpace I p | IsRealizable v } = (fun γ ↦ mfderiv[Ici 0] γ 0 1) ''
    { γ : ℝ → H | γ 0 = p ∧ ∃ x, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Ico 0 x) ∧ 0 < x} := by
  ext x
  simp [IsRealizable]
  sorry

-- this is probably false :((
lemma jid {p : H} : IsClosed
    { γ : ℝ → H | γ 0 = p ∧ ∃ x, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Ico 0 x) ∧ 0 < x} := by

  rw [isClosed_iff_clusterPt]

  sorry

set_option backward.isDefEq.respectTransparency false in
lemma ijiodsaso {p : H} (hp : I.IsBoundaryPoint p) :
    IsClosed { v : TangentSpace I p | IsRealizable v } := by
  --rw [huahoaa hp]
  --rw [isClosed_iff_clusterPt]
  --intro v hv
  rw [huahoaa hp]
  rw [isClosed_iff_clusterPt]

  sorry

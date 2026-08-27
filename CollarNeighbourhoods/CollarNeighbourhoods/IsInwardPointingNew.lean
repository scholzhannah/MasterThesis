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

noncomputable def TangentSpace.ofEq (I : ModelWithCorners ℝ E H) {p q : M} (h : p = q) :
    TangentSpace I p ≃ₜ TangentSpace I q := Homeomorph.refl (TangentSpace I p)

@[simps]
noncomputable def PartialDiffeomorph.mfderiv {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (f : PartialDiffeomorph I I M M' ∞)
    (hp : p ∈ f.source) : Homeomorph (TangentSpace I p) (TangentSpace I (f p)) where
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

omit [IsManifold I ∞ M] in
lemma PartialDiffeomorph.bijective_mfderiv {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (f : PartialDiffeomorph I I M M' ∞)
    (hp : p ∈ f.source) : Bijective (mfderiv% f p) :=
  (mfderiv p f hp).toEquiv.bijective

omit [IsManifold I ∞ M] in
lemma TangentSpace.ofEq_isRealizable_iff {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    {p q : M} (v : TangentSpace I p) (h : p = q) :
    IsRealizableMinimal v ↔ IsRealizableMinimal (TangentSpace.ofEq I h v) := by
  subst p
  rfl

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

-- I think I need this because `PartialDiffeomorph` is private
set_option backward.isDefEq.respectTransparency false in
omit [IsManifold I ∞ M] in
lemma PartialDiffeomorph.interior_isRealizable_eq {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H M'] (p : M) (f : PartialDiffeomorph I I M M' ∞) (hp : p ∈ f.source) :
    interior {v | IsRealizableMinimal v} =
      (mfderiv% f p) '' interior {v | IsRealizableMinimal v} := by
  rw [(isHomeomorph_mfderiv p f hp).image_interior]
  congrm interior ?_
  ext w
  rw [mem_ofPred, f.symm.isRealizable_iff (f p) w (f.map_source' hp),
    show mfderiv% f p = ⇑(mfderiv p f hp).toEquiv from rfl,
    mem_image_equiv (f := (mfderiv p f hp).toEquiv), mem_ofPred]
  change IsRealizableMinimal ((mfderiv% f.symm (f p)) w) ↔
    IsRealizableMinimal ((mfderiv p f hp).symm w)
  rw [f.mfderiv_symm_apply p hp w,
    comp_apply, ← TangentSpace.ofEq_isRealizable_iff _ (f.leftInvOn hp) (M' := M')]

omit [IsManifold I ∞ M] in
lemma PartialDiffeomorph.isInwardPointing_iff {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (v : TangentSpace I p) (f : PartialDiffeomorph I I M M' ∞)
    (hp : p ∈ f.source) :
    IsInwardPointingMinimal v ↔ IsInwardPointingMinimal (mfderiv% f p v) := by
  unfold IsInwardPointingMinimal
  rw [interior_isRealizable_eq p f hp, (bijective_mfderiv p f hp).injective.mem_set_image]

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

omit [IsManifold I ∞ M] in
lemma IsLocalDiffeomorphAt.isInwardPointing_iff {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H M'] (p : M) (v : TangentSpace I p) (f : M → M')
    (hf : IsLocalDiffeomorphAt I I ∞ f p) :
    IsInwardPointingMinimal v ↔ IsInwardPointingMinimal (mfderiv% f p v) := by
  rw [isLocalDiffeomorphAt_iff] at hf
  obtain ⟨φ, hpφ, hφf⟩ := hf
  rw [← mfderivWithin_of_isOpen φ.open_source hpφ, mfderivWithin_congr_of_mem hφf hpφ,
    mfderivWithin_of_isOpen φ.open_source hpφ, φ.isInwardPointing_iff p v hpφ, (hφf hpφ)]

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

open Metric Nat

noncomputable section

-- proof adapted from `https://arxiv.org/pdf/1810.05999`
lemma isClosed_derivable' {s : Set E} (hs : IsClosed s) {p : E} (hp : p ∈ s) :
    IsClosed {v : E |
      ∃ (γ : ℝ → E) (_ : DifferentiableWithinAt ℝ γ (Ici 0) 0), γ 0 = p ∧
      derivWithin γ (Ici 0) (0 : ℝ) = v} := by
  classical
  rw [← isSeqClosed_iff_isClosed]
  -- I need to pick the `v` such that they converge quickly enough
  intro v w h hv
  simp only [exists_and_left, exists_prop, mem_ofPred_eq] at h
  let γ := fun n ↦ Classical.choose (h n)
  have hγp : ∀ n, γ n 0 = p := fun n ↦ (Classical.choose_spec (h n)).1
  have hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0 :=
    fun n ↦ (Classical.choose_spec (h n)).2.1
  have hγv : ∀ n, (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n :=
    fun n ↦ (Classical.choose_spec (h n)).2.2
  have hγnp : ∀ (n : ℕ), ∃ i ∈ Ioi 0, Ioc 0 i ⊆ slope (γ n) 0 ⁻¹' ball (v n) (1 / (n + 1)) := by
    intro n
    have hγn : ball (v n) (1 / (n + 1)) ∈ 𝓝 (v n) := by
      rw [isOpen_ball.mem_nhds_iff]
      exact mem_ball_self one_div_pos_of_nat
    have : Tendsto (slope (γ n) 0) (𝓝[>] 0) (𝓝 (v n)) := by
      rw [← Ici_sdiff_left, ← hasDerivWithinAt_iff_tendsto_slope, ← hγv n]
      exact (hγ n).hasDerivWithinAt
    specialize this hγn
    simp_rw [mem_map, mem_nhdsGT_iff_exists_Ioc_subset] at this
    exact this
  have hγn' : ∀ (n : ℕ), ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)),
      Icc 0 i ⊆ γ n ⁻¹' ball p (1 / (n + 1)) := by
    intro n
    have : ContinuousWithinAt (γ n) (Ici 0) 0 := (hγ n).continuousWithinAt
    have hγn : Metric.ball p (1 / (n + 1)) ∈ 𝓝 (γ n 0) := by
      rw [Metric.isOpen_ball.mem_nhds_iff, hγp]
      exact mem_ball_self one_div_pos_of_nat
    specialize this hγn
    rw [mem_map, mem_nhdsGE_iff_exists_Icc_subset] at this
    obtain ⟨i, hi0, hiγ⟩ := this
    use min i (1 / (n + 1))
    refine ⟨⟨?_, Std.min_le_right⟩, subset_trans (Icc_subset_Icc_right Std.min_le_left) hiγ ⟩
    rw [lt_inf_iff]
    exact ⟨hi0, one_div_pos_of_nat⟩
  have hγn : ∀ (n : ℕ), ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)),
      slope (γ n) 0 i ∈ ball (v n) (1 / (n + 1)) ∧ γ n i ∈  ball p (1 / (n + 1)) := by
    intro n
    obtain ⟨i, hi, hiv⟩ := hγnp n
    obtain ⟨j, hj, hjp⟩ := hγn' n
    use min i j
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨lt_min hi hj.1, (min_le_right _ _).trans hj.2⟩
    · exact hiv ⟨lt_min hi hj.1, min_le_left _ _⟩
    · exact hjp ⟨(lt_min hi hj.1).le, min_le_right _ _⟩
  -- i might have to define this recursively to be decreasing
  -- apparently I need to define this outside of a proof as a separate definition :(
  let rec j' := fun n ↦ match n with
    | 0 => Classical.choose (hγn 0)
    | n + 1 => min (j' n) (Classical.choose (hγn (n + 1)))
  let j := fun n ↦ Classical.choose (hγn n)

  have hj0 : ∀ (n : ℕ), j n ∈ Ioc (0 : ℝ) (1 / (n + 1)) := fun n ↦ (Classical.choose_spec (hγn n)).1
  have hjn : ∀ (n : ℕ), γ n (j n) ∈ ball p (1 / (n + 1)) :=
    fun n ↦ (Classical.choose_spec (hγn n)).2.2
  have hjv : ∀ n, slope (γ n) 0 (j n) ∈ ball (v n) (1 / (n + 1)) :=
    fun n ↦ (Classical.choose_spec (hγn n)).2.1
  let δ : ℝ → E := fun x ↦
      if h : ∃ (n : ℕ), x ∈ Ioc (j (n + 1)) (j n) then
        letI n := (Classical.choose h)
        γ n x
      else p
  use δ
  have hδ0 : δ 0 = p := by
    apply dif_neg
    push Not
    exact fun n ↦ notMem_Ioc_of_le (hj0 (n + 1)).1.le
  suffices HasDerivWithinAt δ w (Ici 0) 0 from
    ⟨this.differentiableWithinAt, hδ0,  this.derivWithin (uniqueDiffWithinAt_Ici 0)⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  unfold slope
  simp only [sub_zero, hδ0, vsub_eq_sub, tendsto_nhdsWithin_nhds, gt_iff_lt, mem_Ioi,
    dist_zero_right, Real.norm_eq_abs]
  intro ε hε
  let N := ⌈1 / ε⌉₊
  use j N, (hj0 N).1
  intro x hx0 hxj
  unfold δ
  -- we also need to show that this `n` is unique
  have h : ∃ n, x ∈ Ioc (j (n + 1)) (j n) := by sorry
  -- use a version of `StrictMono.exists_between_of_tendsto_atTop`
  rw [dif_pos h]

  sorry

-- proof adapted from `https://arxiv.org/pdf/1810.05999`
lemma isClosed_derivable {s : Set E} (hs : IsClosed s) {p : E} (hp : p ∈ s) :
    IsClosed {v : E |
      ∃ (γ : ℝ → E) (_ : DifferentiableWithinAt ℝ γ (Ici 0) 0), γ 0 = p ∧
      derivWithin γ (Ici 0) (0 : ℝ) = v} := by
  classical
  rw [← isSeqClosed_iff_isClosed]
  -- I need to pick the `v` such that they converge quickly enough
  intro v w h hv
  simp only [exists_and_left, exists_prop, mem_ofPred_eq] at h
  let γ := fun n ↦ Classical.choose (h n)
  have hγp : ∀ n, γ n 0 = p := fun n ↦ (Classical.choose_spec (h n)).1
  have hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0 :=
    fun n ↦ (Classical.choose_spec (h n)).2.1
  have hγv : ∀ n, (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n :=
    fun n ↦ (Classical.choose_spec (h n)).2.2
  have hγnp : ∀ (n : ℕ), ∃ i ∈ Ioi 0, Ioc 0 i ⊆ slope (γ n) 0 ⁻¹' ball (v n) (1 / (n + 1)) := by
    intro n
    have hγn : ball (v n) (1 / (n + 1)) ∈ 𝓝 (v n) := by
      rw [isOpen_ball.mem_nhds_iff]
      exact mem_ball_self one_div_pos_of_nat
    have : Tendsto (slope (γ n) 0) (𝓝[>] 0) (𝓝 (v n)) := by
      rw [← Ici_sdiff_left, ← hasDerivWithinAt_iff_tendsto_slope, ← hγv n]
      exact (hγ n).hasDerivWithinAt
    specialize this hγn
    simp_rw [mem_map, mem_nhdsGT_iff_exists_Ioc_subset] at this
    exact this
  have hγn' : ∀ (n : ℕ), ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)),
      Icc 0 i ⊆ γ n ⁻¹' ball p (1 / (n + 1)) := by
    intro n
    have : ContinuousWithinAt (γ n) (Ici 0) 0 := (hγ n).continuousWithinAt
    have hγn : Metric.ball p (1 / (n + 1)) ∈ 𝓝 (γ n 0) := by
      rw [Metric.isOpen_ball.mem_nhds_iff, hγp]
      exact mem_ball_self one_div_pos_of_nat
    specialize this hγn
    rw [mem_map, mem_nhdsGE_iff_exists_Icc_subset] at this
    obtain ⟨i, hi0, hiγ⟩ := this
    use min i (1 / (n + 1))
    refine ⟨⟨?_, Std.min_le_right⟩, subset_trans (Icc_subset_Icc_right Std.min_le_left) hiγ ⟩
    rw [lt_inf_iff]
    exact ⟨hi0, one_div_pos_of_nat⟩
  have hγn : ∀ (n : ℕ), ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)),
      slope (γ n) 0 i ∈ ball (v n) (1 / (n + 1)) ∧ γ n i ∈  ball p (1 / (n + 1)) := by
    intro n
    obtain ⟨i, hi, hiv⟩ := hγnp n
    obtain ⟨j, hj, hjp⟩ := hγn' n
    use min i j
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨lt_min hi hj.1, (min_le_right _ _).trans hj.2⟩
    · exact hiv ⟨lt_min hi hj.1, min_le_left _ _⟩
    · exact hjp ⟨(lt_min hi hj.1).le, min_le_right _ _⟩
  let j := fun n ↦ Classical.choose (hγn n)
  have hj0 : ∀ (n : ℕ), j n ∈ Ioc (0 : ℝ) (1 / (n + 1)) := fun n ↦ (Classical.choose_spec (hγn n)).1
  have hjn : ∀ (n : ℕ), γ n (j n) ∈ ball p (1 / (n + 1)) :=
    fun n ↦ (Classical.choose_spec (hγn n)).2.2
  have hjv : ∀ n, slope (γ n) 0 (j n) ∈ ball (v n) (1 / (n + 1)) :=
    fun n ↦ (Classical.choose_spec (hγn n)).2.1
  -- I think I need to choose a different `δ` such that `δ` agrees with the `γ` on certain
  -- intervals
  let δ' : ℝ → E := fun x ↦
      if h : ∃ (n : ℕ), x ∈ Ioc (j (n + 1)) (j n) then
        letI n := (Classical.choose h)
        γ n x
      else p
  let δ : ℝ → E := fun x ↦
    if h : ∃ (n : ℕ), x ∈ Ioc (1 / (n + 1) : ℝ) (1 / n) then
      letI n := (Classical.choose h)
      γ n (j n)
    else p
  -- we need to do this for elements of R with Gauss Brackets
  have hδ : ∀ (n : ℕ), ∀ x ∈ Ioc (1 / (n + 1) : ℝ) (1 / n), δ x = γ n (j n) := by
    intro n x hxn
    have : ∃ (n : ℕ), x ∈ Ioc (1 / (n + 1) : ℝ) (1 / n) := ⟨n, hxn⟩
    unfold δ
    rw [dif_pos this]
    suffices Classical.choose this = n by rw [this]
    have hxn' := Classical.choose_spec this
    by_contra! hn
    rw [Nat.lt_or_gt] at hn
    rcases hn with hn | hn
    · rw [← lt_self_iff_false x]
      let i := Classical.choose this
      calc
        x ≤ 1 / n := hxn.2
        _ ≤ 1 / (i + 1) := by
          apply one_div_le_one_div_of_le (cast_add_one_pos (Classical.choose this)) ?_
          norm_cast
        _ < x := hxn'.1
    · rw [← lt_self_iff_false x]
      let i := Classical.choose this
      calc
        x ≤ 1 / i := hxn'.2
        _ ≤ 1 / (n + 1) := by
          apply one_div_le_one_div_of_le (cast_add_one_pos n) ?_
          norm_cast
        _ < x := hxn.1
  have hδ' : ∀ x ∈ Ici 1, δ (1 / x) = γ ⌊x⌋₊ (j ⌊x⌋₊) := by
    intro x hx
    apply hδ
    refine ⟨?_, ?_⟩
    · rw [div_lt_div_iff_of_pos_left zero_lt_one (cast_add_one_pos ⌊x⌋₊)
        (lt_of_lt_of_le zero_lt_one hx)]
      exact lt_floor_add_one x
    · rw [div_le_div_iff_of_pos_left zero_lt_one (lt_of_lt_of_le zero_lt_one hx)]
      · exact floor_le (zero_le_one.trans hx)
      · norm_cast
        rw [Nat.floor_pos]
        exact hx
  use δ
  have hδ0 : δ 0 = p := by
    apply dif_neg
    push Not
    simp [(cast_add_one_pos _).le]
  suffices HasDerivWithinAt δ w (Ici 0) 0 from
    ⟨this.differentiableWithinAt, hδ0,  this.derivWithin (uniqueDiffWithinAt_Ici 0)⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  unfold slope
  simp only [sub_zero, hδ0, vsub_eq_sub]
  apply tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop
  simp only [inv_inv]
  rw [← Filter.tendsto_comp_val_Ioi_atTop (a := 1)]
  rw [Filter.tendsto_congr (f₂ := fun x ↦ ((j ⌊x.1⌋₊) * x.1) • slope (γ ⌊x.1⌋₊) 0 (j ⌊x.1⌋₊))]
  ·
    sorry
  · intro ⟨x, hx⟩
    simp [slope]
    sorry


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

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
public import CollarNeighbourhoods.DerivableCone

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

-- **Idea**: We probably want to have a "within" version as well

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
lemma PartialDiffeomorph.isRealizable_iff {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    {p : M} (v : TangentSpace I p) (f : PartialDiffeomorph I I M M' ∞)
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

omit [IsManifold I ∞ M] in
lemma IsLocalDiffeomorphAt.isRealizable_iff {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    {p : M} (v : TangentSpace I p) (f : M → M')
    (hf : IsLocalDiffeomorphAt I I ∞ f p) :
    IsRealizableMinimal v ↔ IsRealizableMinimal (mfderiv% f p v) := by
  rw [isLocalDiffeomorphAt_iff] at hf
  obtain ⟨φ, hpφ, hφf⟩ := hf
  rw [← mfderivWithin_of_isOpen φ.open_source hpφ, mfderivWithin_congr_of_mem hφf hpφ,
    mfderivWithin_of_isOpen φ.open_source hpφ, φ.isRealizable_iff v hpφ, (hφf hpφ)]

omit [IsManifold I ∞ M] in
lemma isRealizable_iff_of_mem_maximalAtlas {p : M} (v : TangentSpace I p)
    (f : OpenPartialHomeomorph M H) (hp : p ∈ f.source)
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) :
    IsRealizableMinimal v ↔ IsRealizableMinimal (mfderiv% f p v) :=
  (Manifold.localDiffeomorphOn_of_mem_maximalAtlas hf ⟨p, hp⟩).isRealizable_iff _

lemma isRealizable_iff_chartAt {p : M} (v : TangentSpace I p) :
    IsRealizableMinimal v ↔ IsRealizableMinimal (mfderiv% (chartAt H p) p v) :=
  isRealizable_iff_of_mem_maximalAtlas _ _ (mem_chart_source H p)
    (IsManifold.chart_mem_maximalAtlas p)

set_option backward.isDefEq.respectTransparency false in
lemma IsRealizable.derivableWithinAt {p : H} {v : TangentSpace I p} (hv : IsRealizableMinimal v) :
    derivableWithinAt ℝ I.target (I p) (d% I p v) := by
  obtain ⟨γ, hγ, hγp, hγv⟩ := hv
  use I ∘ γ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← mdifferentiableWithinAt_iff_differentiableWithinAt]
    exact I.mdifferentiableAt.comp_mdifferentiableWithinAt _ hγ
  · rw [comp_apply, hγp]
  · rw [← fderivWithin_derivWithin, ← mvfderivWithin_eq_fderivWithin,
      mvfderiv_comp_mfderivWithin 0 I.mdifferentiableAt hγ
        (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffWithinAt_Ici 0)),
      ContinuousLinearMap.comp_apply]
    congr
  · apply Filter.Eventually.of_forall
    intro x
    rw [comp_apply, ModelWithCorners.target_eq I]
    exact mem_range_self (γ x)

lemma derivableWithinAt.IsRealizable {p : H} {v : TangentSpace I p}
    (hv : derivableWithinAt ℝ I.target (I p) (d% I p v)) :
    IsRealizableMinimal v := by
  obtain ⟨γ, hγ, hγp, hγv, hγI⟩ := hv
  use I.symm ∘ γ
  refine ⟨?_, by simp [hγp], ?_⟩
  · apply (I.mdifferentiableOn_symm (γ 0) (hγp ▸ mem_range_self p)).comp_of_preimage_mem_nhdsWithin
      _ (mdifferentiableWithinAt_iff_differentiableWithinAt.2 hγ)
    exact I.target_eq ▸ hγI
  · rw [mfderivWithin_comp_of_preimage_mem_nhdsWithin _
      (I.mdifferentiableOn_symm (γ 0) (hγp ▸ mem_range_self p))
      (mdifferentiableWithinAt_iff_differentiableWithinAt.2 hγ) (I.target_eq ▸ hγI)
      (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffWithinAt_Ici 0))]
    rw [ContinuousLinearMap.comp_apply]
    have : Injective (mvfderiv I I p) := by
      rw [I.mvfderiv]
      exact injective_id
    apply this
    rw [← comp_apply (f := mvfderiv I I p) (g := (mfderivWithin _ _ I.symm (range I) (γ 0)))]
    -- can't rewrite because of def-eq abuse
    change (mvfderiv I I p ∘SL mfderivWithin _ _ I.symm (range I) (γ 0)) _= _
    -- fixing defeq abuse
    have : I.symm (γ 0) = p := by rw [hγp, I.left_inv p]
    rw [← this]
    rw [← mvfderiv_comp_mfderivWithin _ I.mdifferentiableAt
      (I.mdifferentiableOn_symm (γ 0) (hγp ▸ mem_range_self p))
      (I.uniqueMDiffOn _ (hγp ▸ mem_range_self p))]
    rw [mvfderivWithin_congr (f := id) _ (by exact I.rightInvOn)
      (I.rightInvOn (hγp ▸ mem_range_self p))]
    rw [MDifferentiableWithinAt.mvfderivWithin_mono (s := univ) _ mdifferentiableWithinAt_id ?_
      (subset_univ _)]
    · sorry

    sorry


set_option backward.isDefEq.respectTransparency false in
lemma isRealizable_iff_derivableWithinAt_traget {p : H} (v : TangentSpace I p) :
    IsRealizableMinimal v ↔ derivableWithinAt ℝ I.target (I p) (d% I p v) := by
  rw [isRealizable_iff_chartAt v]
  --unfold IsRealizableMinimal derivableWithinAt
  constructor
  · intro ⟨γ, hγ, hγp, hγv⟩
    use I ∘ γ
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact I.mdifferentiableAt.comp_mdifferentiableWithinAt _ hγ
    · rw [comp_apply, hγp]
      rfl
    · -- this proof is full with def-eq abuse
      rw [← fderivWithin_derivWithin, ← mvfderivWithin_eq_fderivWithin,
        mvfderiv_comp_mfderivWithin 0 I.mdifferentiableAt hγ
          (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffWithinAt_Ici 0)),
        ContinuousLinearMap.comp_apply]
      rw [ModelWithCorners.mvfderiv I, ModelWithCorners.mvfderiv I]
      change (mfderivWithin _ _ γ (Ici 0) 0) 1 = v
      rw [hγv]
      simp only [OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_source,
        OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq]
      rw [OpenPartialHomeomorph.refl_apply H, mfderiv_id]
      rfl
    · apply Filter.Eventually.of_forall
      intro x
      rw [comp_apply, ModelWithCorners.target_eq I]
      exact mem_range_self (γ x)
  · sorry

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
  rw [mem_ofPred, f.symm.isRealizable_iff w (f.map_source' hp),
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

omit [IsManifold I ∞ M] in
lemma IsLocalDiffeomorphAt.isInwardPointing_iff {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H M'] (p : M) (v : TangentSpace I p) (f : M → M')
    (hf : IsLocalDiffeomorphAt I I ∞ f p) :
    IsInwardPointingMinimal v ↔ IsInwardPointingMinimal (mfderiv% f p v) := by
  rw [isLocalDiffeomorphAt_iff] at hf
  obtain ⟨φ, hpφ, hφf⟩ := hf
  rw [← mfderivWithin_of_isOpen φ.open_source hpφ, mfderivWithin_congr_of_mem hφf hpφ,
    mfderivWithin_of_isOpen φ.open_source hpφ, φ.isInwardPointing_iff p v hpφ, (hφf hpφ)]

omit [IsManifold I ∞ M] in
lemma isInwardPointing_iff_of_mem_maximalAtlas {p : M} (v : TangentSpace I p)
    (f : OpenPartialHomeomorph M H) (hp : p ∈ f.source)
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) :
    IsInwardPointingMinimal v ↔ IsInwardPointingMinimal (mfderiv% f p v) :=
  (Manifold.localDiffeomorphOn_of_mem_maximalAtlas hf ⟨p, hp⟩).isInwardPointing_iff _ _

lemma isInwardPointing_iff_chartAt {p : M} (v : TangentSpace I p) :
    IsInwardPointingMinimal v ↔ IsInwardPointingMinimal (mfderiv% (chartAt H p) p v) :=
  isInwardPointing_iff_of_mem_maximalAtlas _ _ (mem_chart_source H p)
    (IsManifold.chart_mem_maximalAtlas p)

-- **I am not sure if we actually need anything of the end of the file**

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

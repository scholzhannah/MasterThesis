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
  {I : ModelWithCorners ℝ E H} {n : ℕ∞ω} [NeZero n] [IsManifold I n M]

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

omit [IsManifold I n M] in
lemma PartialDiffeomorph.isRealizable_apply {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (v : TangentSpace I p) (f : PartialDiffeomorph I I M M' n)
    (hp : p ∈ f.source) (hv : IsRealizableMinimal v) :
    IsRealizableMinimal (mfderiv% f p v) := by
  obtain ⟨γ, hγ, hγp, hγv⟩ := hv
  have hf := f.mdifferentiableAt (NeZero.ne n) (hγp ▸ hp)
  use f ∘ γ, hf.comp_mdifferentiableWithinAt 0 hγ, by simp [hγp]
  rw [mfderiv_comp_mfderivWithin 0 hf hγ ?_, ContinuousLinearMap.comp_apply, hγv, hγp]
  rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
  exact uniqueDiffWithinAt_Ici 0

omit [IsManifold I n M] in
lemma TangentSpace.ofEq_isRealizable_iff {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    {p q : M} (v : TangentSpace I p) (h : p = q) :
    IsRealizableMinimal v ↔ IsRealizableMinimal (TangentSpace.ofEq I h v) := by
  subst p
  rfl

omit [IsManifold I n M] in
lemma PartialDiffeomorph.isRealizable_iff {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    {p : M} (v : TangentSpace I p) (f : PartialDiffeomorph I I M M' n)
    (hp : p ∈ f.source) :
    IsRealizableMinimal v ↔ IsRealizableMinimal (mfderiv% f p v) := by
  refine ⟨fun hv ↦ isRealizable_apply p v f hp hv, ?_⟩
  have : v = (mfderiv% f.symm (f p)) ((mfderiv% f p) v) := by
    -- use proof def above to proof this
    rw [← mfderiv_comp_apply p ?_ (f.mdifferentiableAt (NeZero.ne n) hp) v]
    · rw [← mfderivWithin_of_isOpen f.open_source hp, mfderivWithin_congr_of_mem (f := id) ?_ hp]
      · rw [mfderivWithin_of_isOpen f.open_source hp, comp_apply, mfderiv_id]
        rfl
      exact f.leftInvOn
    · apply f.symm.mdifferentiableAt (NeZero.ne n)
      exact f.map_source' hp
  intro hv
  rw [this]
  nth_rw 1 [← f.left_inv hp]
  apply f.symm.isRealizable_apply _ _ ?_ hv
  simp [f.map_source' hp]

omit [IsManifold I n M] in
lemma IsLocalDiffeomorphAt.isRealizable_iff {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    {p : M} (v : TangentSpace I p) (f : M → M')
    (hf : IsLocalDiffeomorphAt I I n f p) :
    IsRealizableMinimal v ↔ IsRealizableMinimal (mfderiv% f p v) := by
  rw [isLocalDiffeomorphAt_iff] at hf
  obtain ⟨φ, hpφ, hφf⟩ := hf
  rw [← mfderivWithin_of_isOpen φ.open_source hpφ, mfderivWithin_congr_of_mem hφf hpφ,
    mfderivWithin_of_isOpen φ.open_source hpφ, φ.isRealizable_iff v hpφ, (hφf hpφ)]
  rfl

omit [IsManifold I n M] in
lemma isRealizable_iff_of_mem_maximalAtlas {p : M} (v : TangentSpace I p)
    (f : OpenPartialHomeomorph M H) (hp : p ∈ f.source)
    (hf : f ∈ IsManifold.maximalAtlas I n M) :
    IsRealizableMinimal v ↔ IsRealizableMinimal (mfderiv% f p v) :=
  (Manifold.localDiffeomorphOn_of_mem_maximalAtlas hf ⟨p, hp⟩).isRealizable_iff _

include n in
lemma isRealizable_iff_chartAt {p : M} (v : TangentSpace I p) :
    IsRealizableMinimal v ↔ IsRealizableMinimal (mfderiv% (chartAt H p) p v) :=
  isRealizable_iff_of_mem_maximalAtlas _ _ (mem_chart_source H p)
    (IsManifold.chart_mem_maximalAtlas (n := n) p)

set_option backward.isDefEq.respectTransparency false in
-- fix `mvfderivWithin_eq_fderivWithin`
lemma IsRealizable.derivableWithinAt {p : H} {v : TangentSpace I p} (hv : IsRealizableMinimal v) :
    derivableWithinAt ℝ (range I) (I p) (d% I p v) := by
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
    rw [comp_apply]
    exact mem_range_self (γ x)

lemma derivableWithinAt.IsRealizable {p : H} {v : TangentSpace I p}
    (hv : derivableWithinAt ℝ (range I) (I p) (d% I p v)) :
    IsRealizableMinimal v := by
  obtain ⟨γ, hγ, hγp, hγv, hγI⟩ := hv
  use I.symm ∘ γ
  refine ⟨?_, by simp [hγp], ?_⟩
  · apply (I.mdifferentiableOn_symm (γ 0) (hγp ▸ mem_range_self p)).comp_of_preimage_mem_nhdsWithin
      _ (mdifferentiableWithinAt_iff_differentiableWithinAt.2 hγ)
    exact I.target_eq ▸ hγI
  · have hI := I.mdifferentiableOn_symm (γ 0) (hγp ▸ mem_range_self p)
    have hIγ : UniqueMDiffAt[range I] (γ 0) := I.uniqueMDiffOn _ (hγp ▸ mem_range_self p)
    have h := uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffWithinAt_Ici 0)
    rw [← mdifferentiableWithinAt_iff_differentiableWithinAt] at hγ
    rw [mfderivWithin_comp_of_preimage_mem_nhdsWithin _ hI hγ (I.target_eq ▸ hγI) h,
      ContinuousLinearMap.comp_apply]
    have : Injective (mvfderiv I I p) := by
      rw [I.mvfderiv]
      exact injective_id
    apply this
    rw [← hγv, ← comp_apply (f := mvfderiv I I p) (g := (mfderivWithin _ _ I.symm (range I) (γ 0)))]
    -- can't rewrite because of def-eq abuse
    change (mvfderiv I I p ∘SL mfderivWithin _ _ I.symm (range I) (γ 0)) _= _
    -- fixing defeq abuse
    have : I.symm (γ 0) = p := by rw [hγp, I.left_inv p]
    rw [← this, ← mvfderiv_comp_mfderivWithin _ I.mdifferentiableAt hI hIγ,
      mvfderivWithin_congr (f := id) _ (by exact I.rightInvOn)
      (I.rightInvOn (hγp ▸ mem_range_self p)), mdifferentiableWithinAt_id.mvfderivWithin_mono
      (s := univ) _ hIγ (subset_univ _), mvfderivWithin_univ, ← ContinuousLinearMap.comp_apply,
      mvfderiv_id_comp_mfderivWithin _ hγ h, mvfderivWithin_eq_fderivWithin]
    exact fderivWithin_derivWithin (𝕜 := ℝ)

lemma isRealizable_iff_derivableWithinAt {p : H} {v : TangentSpace I p} :
    IsRealizableMinimal v ↔ derivableWithinAt ℝ (range I) (I p) (d% I p v) :=
  ⟨IsRealizable.derivableWithinAt, derivableWithinAt.IsRealizable⟩

omit [IsManifold I n M] in
lemma isRealizable_iff_derivableWithinAt_of_mem_maximalAtlas {p : M} {v : TangentSpace I p}
    (f : OpenPartialHomeomorph M H) (hp : p ∈ f.source)
    (hf : f ∈ IsManifold.maximalAtlas I n M) :
    IsRealizableMinimal v ↔
      derivableWithinAt ℝ (range I) (f.extend I p) (d% (f.extend I) p v) := by
  have hfp := mdifferentiableAt_of_mem_maximalAtlas
    (IsManifold.maximalAtlas_subset_of_le (ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne n)) hf) hp
  rw [isRealizable_iff_of_mem_maximalAtlas v f hp hf, isRealizable_iff_derivableWithinAt,
    ← ContinuousLinearMap.comp_apply, ← mvfderiv_comp (g := I) (f := f) p I.mdifferentiableAt hfp,
    f.extend_coe, comp_apply]

omit [IsManifold I n M] in
lemma isRealizable_iff_mem_posTangentConeAt_of_mem_maximalAtlas {p : M} {v : TangentSpace I p}
    (f : OpenPartialHomeomorph M H) (hp : p ∈ f.source)
    (hf : f ∈ IsManifold.maximalAtlas I n M) :
    IsRealizableMinimal v ↔
      d% (f.extend I) p v ∈ posTangentConeAt (range I) (f.extend I p) :=
  (isRealizable_iff_derivableWithinAt_of_mem_maximalAtlas f hp hf).trans
    (I.convex_range.derivableWithinAt_iff_mem_posTangentConeAt (mem_range_self _))

include n in
lemma isRealizable_iff_derivablewithinAt_extChartAt {p : M} {v : TangentSpace I p} :
    IsRealizableMinimal v ↔
      derivableWithinAt ℝ (range I) (extChartAt I p p) (d% (extChartAt I p) p v) :=
  isRealizable_iff_derivableWithinAt_of_mem_maximalAtlas _ (mem_chart_source H p)
    (IsManifold.chart_mem_maximalAtlas (n := n) p)

include n in
lemma isRealizable_iff_mem_posTangentConeAt_extChartAt {p : M} {v : TangentSpace I p} :
    IsRealizableMinimal v ↔
      d% (extChartAt I p) p v ∈ posTangentConeAt (range I) (extChartAt I p p) :=
  (isRealizable_iff_derivablewithinAt_extChartAt (n := n)).trans
    (I.convex_range.derivableWithinAt_iff_mem_posTangentConeAt (mem_range_self _))

include n in
lemma isRealizable_of_isInteriorPoint {p : M} (hp : I.IsInteriorPoint p) {v : TangentSpace I p} :
    IsRealizableMinimal v := by
  rw [isRealizable_iff_mem_posTangentConeAt_extChartAt (n := n), posTangentConeAt,
    tangentConeAt_of_mem_nhds (range_mem_nhds_isInteriorPoint hp)]
  exact mem_univ _

lemma isRealizable_iff_euclideanHalfSpace {m : ℕ} [NeZero m] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace m) M] [IsManifold (𝓡∂ m) n M] {p : M}
    (hp : (𝓡∂ m).IsBoundaryPoint p) {v : TangentSpace (𝓡∂ m) p} :
    IsRealizableMinimal v ↔ 0 ≤ ((d% (extChartAt (𝓡∂ m) p) p) v).ofLp 0 := by
  rw [isRealizable_iff_derivablewithinAt_extChartAt (n := n),
    range_modelWithCornersEuclideanHalfSpace m]
  apply derivableWithinAt_iff_euclideanHalfSpace
  rwa [extChartAt, OpenPartialHomeomorph.extend_coe, comp_apply,
    ← modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff,
    Manifold.isBoundaryPoint_chartAt_iff (n := n)]

-- **Question**: How do i say corner point in mathlib?

-- I think I need this because `PartialDiffeomorph` is private
-- Maybe try to isolate this an post on Zulip
set_option backward.isDefEq.respectTransparency false in
lemma PartialDiffeomorph.interior_isRealizable_eq {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H M'] (p : M) (f : PartialDiffeomorph I I M M' n) (hp : p ∈ f.source) :
    interior {v | IsRealizableMinimal v} =
      (mfderiv% f p) '' interior {v | IsRealizableMinimal v} := by
  rw [(isHomeomorph_mfderiv p f hp).image_interior]
  congrm interior ?_
  ext w
  rw [mem_ofPred, f.symm.isRealizable_iff (n := n) w (f.map_source' hp),
    show mfderiv% f p = ⇑(mfderiv p f hp).toEquiv from rfl,
    mem_image_equiv (f := (mfderiv p f hp).toEquiv), mem_ofPred]
  change IsRealizableMinimal ((mfderiv% f.symm (f p)) w) ↔
    IsRealizableMinimal ((mfderiv p f hp).symm w)
  rw [f.mfderiv_symm_apply p hp w,
    comp_apply, ← TangentSpace.ofEq_isRealizable_iff _ (f.leftInvOn hp) (M' := M')]

lemma PartialDiffeomorph.isInwardPointing_iff {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (v : TangentSpace I p) (f : PartialDiffeomorph I I M M' n)
    (hp : p ∈ f.source) :
    IsInwardPointingMinimal v ↔ IsInwardPointingMinimal (mfderiv% f p v) := by
  unfold IsInwardPointingMinimal
  rw [interior_isRealizable_eq p f hp, (bijective_mfderiv p f hp).injective.mem_set_image]

lemma IsLocalDiffeomorphAt.isInwardPointing_iff {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H M'] (p : M) (v : TangentSpace I p) (f : M → M')
    (hf : IsLocalDiffeomorphAt I I n f p) :
    IsInwardPointingMinimal v ↔ IsInwardPointingMinimal (mfderiv% f p v) := by
  rw [isLocalDiffeomorphAt_iff] at hf
  obtain ⟨φ, hpφ, hφf⟩ := hf
  rw [← mfderivWithin_of_isOpen φ.open_source hpφ, mfderivWithin_congr_of_mem hφf hpφ,
    mfderivWithin_of_isOpen φ.open_source hpφ, φ.isInwardPointing_iff p v hpφ, (hφf hpφ)]
  rfl

lemma isInwardPointing_iff_of_mem_maximalAtlas {p : M} (v : TangentSpace I p)
    (f : OpenPartialHomeomorph M H) (hp : p ∈ f.source)
    (hf : f ∈ IsManifold.maximalAtlas I n M) :
    IsInwardPointingMinimal v ↔ IsInwardPointingMinimal (mfderiv% f p v) :=
  (Manifold.localDiffeomorphOn_of_mem_maximalAtlas hf ⟨p, hp⟩).isInwardPointing_iff _ _

include n in
lemma isInwardPointing_iff_chartAt {p : M} (v : TangentSpace I p) :
    IsInwardPointingMinimal v ↔ IsInwardPointingMinimal (mfderiv% (chartAt H p) p v) :=
  isInwardPointing_iff_of_mem_maximalAtlas _ _ (mem_chart_source H p)
    (IsManifold.chart_mem_maximalAtlas (n := n) p)

lemma interior_posTangentConeAt_eq {p : H} :
    interior (posTangentConeAt (range I) (I p)) =
      d% I p '' interior {v | IsRealizableMinimal v} := by
  rw [(isHomeomorph_mvfderiv_modelWithCorners I p).image_interior]
  congr
  ext w
  rw [← I.convex_range.derivableWithinAt_iff_mem_posTangentConeAt (mem_range_self p)]
  change _ ↔ _ ∈ (mvfderivModelWithCorners I p).toEquiv '' _
  rw [mem_image_equiv, mem_ofPred, isRealizable_iff_derivableWithinAt,
    ← mvfderivModelWithCorners_apply]
  congrm derivableWithinAt ℝ (range I) (I p) ?_
  exact (Homeomorph.symm_apply_eq (mvfderivModelWithCorners I p)).mp rfl

lemma isInwardPointing_iff_mem_interior_posTangentConeAt_of_mem_maximalAtlas {p : M}
    {v : TangentSpace I p} (f : OpenPartialHomeomorph M H) (hp : p ∈ f.source)
    (hf : f ∈ IsManifold.maximalAtlas I n M) :
    IsInwardPointingMinimal v ↔
      d% (f.extend I) p v ∈ interior (posTangentConeAt (range I) (f.extend I p)) := by
  have hfp := mdifferentiableAt_of_mem_maximalAtlas
    (IsManifold.maximalAtlas_subset_of_le (ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne n)) hf) hp
  rw [isInwardPointing_iff_of_mem_maximalAtlas v f hp hf, f.extend_coe, comp_apply,
    interior_posTangentConeAt_eq, mvfderiv_comp p I.mdifferentiableAt hfp,
    ContinuousLinearMap.comp_apply,
    (bijective_mvfderiv_modelWithCorners I _).injective.mem_set_image, IsInwardPointingMinimal]

include n in
lemma isInwardPointing_iff_extChartAt_mem_interior_posTangentConeAt {p : M}
    {v : TangentSpace I p} :
    IsInwardPointingMinimal v ↔
      d% (extChartAt I p) p v ∈ interior (posTangentConeAt (range I) (extChartAt I p p)) :=
  isInwardPointing_iff_mem_interior_posTangentConeAt_of_mem_maximalAtlas _ (mem_chart_source H p)
    (IsManifold.chart_mem_maximalAtlas (n := n) p)

include n in
lemma isInwardPointing_of_isInteriorPoint {p : M} (hp : I.IsInteriorPoint p)
    {v : TangentSpace I p} : IsInwardPointingMinimal v := by
  rw [isInwardPointing_iff_extChartAt_mem_interior_posTangentConeAt (n := n), posTangentConeAt,
    tangentConeAt_of_mem_nhds (range_mem_nhds_isInteriorPoint hp), interior_univ]
  exact mem_univ _

lemma isInwardPointing_iff_euclideanHalfSpace {m : ℕ} [NeZero m] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace m) M] [IsManifold (𝓡∂ m) n M] {p : M}
    (hp : (𝓡∂ m).IsBoundaryPoint p) {v : TangentSpace (𝓡∂ m) p} :
    IsInwardPointingMinimal v ↔ 0 < ((d% (extChartAt (𝓡∂ m) p) p) v).ofLp 0 := by
  rw [isInwardPointing_iff_extChartAt_mem_interior_posTangentConeAt (n := n),
    range_modelWithCornersEuclideanHalfSpace m,
    interior_posTangentConeAt_euclideanHalfSpace ?_, mem_ofPred]
  rwa [extChartAt, OpenPartialHomeomorph.extend_coe, comp_apply,
    ← modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff,
    Manifold.isBoundaryPoint_chartAt_iff (n := n)]

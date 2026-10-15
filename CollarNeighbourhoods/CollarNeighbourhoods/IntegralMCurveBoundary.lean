module

public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import CollarNeighbourhoods.ExistsUniqueBoundary
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.LinearAlgebra.AffineSpace.Ordered

/-! Header -/

@[expose] public section

open scoped Manifold Topology

open Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

-- this doesn't make any sense because we cannot control the preimage
def IsMIntegralCurveAtNew (γ : ℝ → M) (v : (x : M) → TangentSpace% x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in (𝓝 (γ t₀)).comap γ, HasMFDerivAt% γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

example (γ : ℝ → M) (v : (x : M) → TangentSpace% x) (t₀ : ℝ)
    (ht₀ : I.IsInteriorPoint (γ t₀)) :
    IsMIntegralCurveAtNew γ v t₀ ↔ IsMIntegralCurveAt γ v t₀ := by
  constructor
  · unfold IsMIntegralCurveAt IsMIntegralCurveAtNew
    simp_rw [Filter.eventually_iff_exists_mem, Filter.mem_comap]
    intro ⟨t, ⟨s, hs, hst⟩, htγ⟩
    refine ⟨t, ?_, htγ⟩
    apply Filter.mem_of_superset _ hst
    refine ((htγ t₀ ?_).mdifferentiableAt ).continuousAt.preimage_mem_nhds hs
    apply hst
    rw [mem_preimage]
    exact mem_of_mem_nhds hs
  · unfold IsMIntegralCurveAt IsMIntegralCurveAtNew
    simp_rw [Filter.eventually_iff_exists_mem]
    intro ⟨t, ht, htγ⟩
    refine ⟨t, ?_, htγ⟩
    --rw [← nhds_induced γ t₀]
    rw [Filter.mem_comap]
    --refine ⟨γ '' t, ?_, ?_⟩

    sorry

theorem continuousWithinAt_def {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    {s : Set X} {x : X} : ContinuousWithinAt f s x ↔ ∀ A ∈ 𝓝 (f x), f ⁻¹' A ∈ 𝓝[s] x :=
  Iff.rfl

@[to_dual]
theorem nhdsWithin_Icc_eq_nhdsLE' {α : Type u} [TopologicalSpace α] [LinearOrder α]
    [ClosedIicTopology α] {a b c : α} (h : a < c) : 𝓝[Icc a b] c = 𝓝[Iic b] c :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ici_mem_nhds h

@[to_dual]
theorem nhdsWithin_Ioc_eq_nhdsLE' {α : Type u} [TopologicalSpace α] [LinearOrder α]
    [ClosedIicTopology α] {a b c : α} (h : a < c) : 𝓝[Ioc a b] c = 𝓝[Iic b] c :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ioi_mem_nhds h

-- do `IntegralCurveWithinAt`
def IsRightMIntegralCurveAt (γ : ℝ → M) (v : (x : M) → TangentSpace% x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝[≥] t₀, HasMFDerivAt[Ici t₀] γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

lemma isRightMIntegralCurveAt_iff {γ : ℝ → M} {v : (x : M) → TangentSpace% x} {t₀ : ℝ} :
    IsRightMIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝[≥] t₀, IsMIntegralCurveOn γ v s := by
  unfold IsRightMIntegralCurveAt IsMIntegralCurveOn
  rw [Filter.eventually_iff_exists_mem]
  have htt₀ : ∀ t, ∀ i ∈ Ico t₀ t, Ico t₀ t =ᶠ[𝓝 i] Ici t₀ := by
    intro t i hi
    rw [← nhdsWithin_eq_iff_eventuallyEqSet]
    nth_rw 1 [← max_self t₀, ← Ico_inter_Ici]
    refine nhdsWithin_inter_of_mem ?_
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
    use Ioo (t₀ - 1) t, Ioo_mem_nhds (lt_of_lt_of_le (sub_one_lt t₀) hi.1) hi.2
    intro x ⟨⟨_, hxt⟩, hxt₀⟩
    exact ⟨hxt₀, hxt⟩
  refine ⟨fun ⟨s, hs, hsγ⟩ ↦ ?_, fun ⟨s, hs, hsγ⟩ ↦ ?_⟩
  · rw [mem_nhdsGE_iff_exists_Ico_subset] at hs
    obtain ⟨t, ht, hts⟩ := hs
    use Ico t₀ t, Ico_mem_nhdsGE ht
    intro i hi
    exact (hasMFDerivWithinAt_congr_set (htt₀ t i hi)).2 (hsγ i (hts hi))
  · rw [mem_nhdsGE_iff_exists_Ico_subset] at hs
    obtain ⟨t, ht, hts⟩ := hs
    use Ico t₀ t, Ico_mem_nhdsGE ht
    intro i hi
    exact (hasMFDerivWithinAt_congr_set (htt₀ t i hi).symm).2 ((hsγ i (hts hi)).mono hts)

lemma isRightMIntegralCurveAt_iff' {γ : ℝ → M} {v : (x : M) → TangentSpace% x} {t₀ : ℝ} :
    IsRightMIntegralCurveAt γ v t₀ ↔ ∃ t > t₀, IsMIntegralCurveOn γ v (Icc t₀ t) := by
  rw [isRightMIntegralCurveAt_iff]
  constructor
  · intro ⟨s, hs, hsγ⟩
    rw [mem_nhdsGE_iff_exists_Icc_subset] at hs
    obtain ⟨t, ht, hts⟩ := hs
    use t, ht, hsγ.mono hts
  · intro ⟨t, ht, htγ⟩
    use Icc t₀ t, Icc_mem_nhdsGE ht

theorem IsRightMIntegralCurveAt.continuousWithinAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {t₀ : ℝ}
    (hγ : IsRightMIntegralCurveAt γ v t₀) : ContinuousWithinAt γ (Ici t₀) t₀ := by
  have ⟨s, hs, hγ⟩ := isRightMIntegralCurveAt_iff'.mp hγ
  apply (hγ.continuousWithinAt (left_mem_Icc.mpr hs.le)).congr_set
  rw [← nhdsWithin_eq_iff_eventuallyEqSet]
  exact nhdsWithin_Icc_eq_nhdsGE' hs

set_option backward.isDefEq.respectTransparency false in
lemma IsRightMIntegralCurveAt.eventually_hasDerivWithinAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {t₀ : ℝ}
    [IsManifold I 1 M] (hγ : IsRightMIntegralCurveAt γ v t₀) :
    ∀ᶠ t in 𝓝[≥] t₀, HasDerivWithinAt ((extChartAt I (γ t₀)) ∘ γ)
      (tangentCoordChange I (γ t) (γ t₀) (γ t) (v (γ t))) (Ici t₀) t := by
  apply eventually_mem_nhdsWithin_iff.mpr
    (hγ.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (I := I) _)) |>.and
    hγ |>.mp
  obtain ⟨t, htt₀, ht⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 <|
    (continuousWithinAt_def.1 hγ.continuousWithinAt)
    (extChartAt I (γ t₀)).source (extChartAt_source_mem_nhds (γ t₀))
  rw [← nhdsWithin_Icc_eq_nhdsGE' htt₀]
  apply eventually_nhdsWithin_of_forall
  intro x hx ⟨hx1, hx2⟩
  have hsrc := mem_of_mem_nhdsWithin hx.1 hx1
  rw [mem_preimage, extChartAt_source I (γ t₀)] at hsrc
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivAt.comp_hasMFDerivWithinAt x
    (hasMFDerivAt_extChartAt (I := I) hsrc) hx2).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← one_apply_eq_self (F := TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) t) a,
    ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ} (t₀ : ℝ) {x₀ : M}

-- really I think this proof should be split up into a few things:
-- right integral curves are preserved under partial diffeomorphisms
-- and then conclude

set_option backward.isDefEq.respectTransparency false in
theorem exists_isRightMIntegralCurveAt_of_contMDiffAt [CompleteSpace E]
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx : IsInwardPointingMinimal (v x₀)) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsRightMIntegralCurveAt γ v t₀ := by
  -- express the differentiability of the vector field `v` in the local chart
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
    -- use Picard-Lindelöf theorem to extract a solution to the ODE in the local chart
  let f := ((extChartAt I.tangent (⟨x₀, v x₀⟩ : Bundle.TotalSpace E (TangentSpace I))) ∘
    (fun x ↦ ⟨x, v x⟩) ∘ ↑(extChartAt I x₀).symm)
  -- factor out?
  have hf : inwardPointing ℝ (range I) ((extChartAt I x₀) x₀) (f ((extChartAt I x₀) x₀)).2 := by
    rw [isInwardPointing_iff_inwardPointing_extChartAt (n := 1)] at hx
    convert hx
    unfold f
    rw [Function.comp_apply, Function.comp_apply,
      PartialEquiv.left_inv (extChartAt I x₀) (mem_extChartAt_source x₀),
      FiberBundle.extChartAt ⟨x₀, v x₀⟩]
    simp [TangentBundle.trivializationAt_apply x₀ ⟨x₀, v x₀⟩,
      (mdifferentiableAt_extChartAt (mem_chart_source H x₀)).mvfderiv (f := I ∘ (chartAt H x₀))]
    rfl
  obtain ⟨ε, hε, α, hαt₀, hαI⟩ := ContDiffAt.exists_eq_forall_mem_Icc_hasDerivAt₀ I.convex_range
    I.nonempty_interior (x₀ := extChartAt I x₀ x₀)
    (extChartAt_target_subset_range _ <| mem_extChartAt_target x₀) hf hv.snd t₀
  have hcont : ContinuousWithinAt α (Ici t₀) t₀ := by
    apply HasDerivWithinAt.continuousWithinAt
    apply (hαI t₀ ⟨le_refl t₀, (le_add_iff_nonneg_right t₀).2 hε.le⟩).1.congr_set
    rw [← nhdsWithin_eq_iff_eventuallyEqSet,
      nhdsWithin_Icc_eq_nhdsGE ((lt_add_iff_pos_right t₀).2 hε)]
  --have hev : ∀ᶠ x in 𝓝[≥] t₀, α x ∈ range I := by sorry
  have hcont' : ∀ A ∈ 𝓝[range I] (α t₀), α ⁻¹' A ∈ 𝓝[≥] t₀ := by
    intro A hA
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hA
    obtain ⟨u, hu, huα⟩ := hA
    suffices α ⁻¹' u ∈ 𝓝[≥] t₀ by
      apply Filter.mem_of_superset (x := Icc t₀ (t₀ + ε) ∩ α ⁻¹' u)
        (Filter.inter_mem (Icc_mem_nhdsGE ((lt_add_iff_pos_right t₀).mpr hε)) this)
      intro i ⟨hi, hiα⟩
      exact huα ⟨hiα, (hαI i hi).2⟩
    exact hcont hu
  have hnhds : α ⁻¹' ((extChartAt I x₀).target) ∈ 𝓝[≥] t₀ := by
    apply hcont'
    rw [hαt₀]
    exact extChartAt_target_mem_nhdsWithin x₀
  have hα2 : ∀ᶠ t in 𝓝[≥] t₀, HasDerivWithinAt α (((extChartAt I.tangent ⟨x₀, v x₀⟩) ∘
      (fun x ↦ ⟨x, v x⟩ : M → Bundle.TotalSpace E (TangentSpace I)) ∘
      (extChartAt I x₀).symm) (α t)).2 (Icc t₀ (t₀ + ε)) t := by
    rw [Filter.eventually_iff_exists_mem]
    use Icc t₀ (t₀ + ε), Icc_mem_nhdsGE ((lt_add_iff_pos_right t₀).mpr hε)
    intro i hi
    exact (hαI i hi).1
  rw [← eventually_mem_nhdsWithin_iff] at hnhds
  -- obtain a neighbourhood `s` so that the above conditions both hold in `s`
  obtain ⟨s, hs, haux⟩ := (hα2.and hnhds).exists_mem
  use (extChartAt I x₀).symm ∘ α, by simp [hαt₀]
  rw [isRightMIntegralCurveAt_iff]
  use s ∩ Ico t₀ (t₀ + ε), Filter.inter_mem hs (Ico_mem_nhdsGE ((lt_add_iff_pos_right t₀).mpr hε))
  intro t ht
  -- collect useful terms in convenient forms
  let xₜ : M := (extChartAt I x₀).symm (α t) -- `xₜ := γ t`
  have h : HasDerivWithinAt α (s := Icc t₀ (t₀ + ε)) (x := t) <|
    fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I xₜ).symm)
    (range I) (extChartAt I xₜ xₜ) (v xₜ) := (haux t ht.1).1
  rw [← tangentCoordChange_def] at h
  have hf3 : α t ∈ (extChartAt I x₀).target := by
    -- this needs to stay in exactly this shape for some reason
    apply mem_of_mem_nhdsWithin ht.2.1 (haux t ht.1).2
  --have hft1 := mem_preimage.mp <|
  --  mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hcont : ContinuousWithinAt α (Ici t₀) t := by
    apply h.continuousWithinAt.congr_set
    rw [← nhdsWithin_eq_iff_eventuallyEqSet]
    exact nhdsWithin_Icc_eq_nhdsGE' ht.2.2
  have hft1 : (extChartAt I x₀).symm (α t) ∈ (extChartAt I x₀).source :=
    mem_preimage.mp (mem_of_mem_of_subset hf3 (extChartAt I x₀).target_subset_preimage_source)
  have hft2 := mem_extChartAt_source (I := I) xₜ
  refine ⟨?_, ?_⟩
  · apply ((continuousOn_extChartAt_symm _).continuousWithinAt hf3).comp
    · exact hcont.mono <| inter_subset_right.trans Ico_subset_Ici_self
    · intro x hx
      apply mem_of_mem_nhdsWithin hx.2.1 (haux x hx.1).2
  · apply HasDerivWithinAt.hasFDerivWithinAt
    simp only [mfld_simps]
    change HasDerivWithinAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ α) (v xₜ) _ t
    rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
      ←  tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
    apply ((extChartAt I x₀).right_inv hf3 ▸
      hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩).comp_hasDerivWithinAt _
      (h.mono (inter_subset_right.trans Ico_subset_Icc_self))
    intro x hx
    exact (hαI x (Ico_subset_Icc_self hx.2)).2

theorem exists_isMRightIntegralCurveAt_of_contMDiffAt_of_isInteriorPoint [CompleteSpace E]
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx : I.IsInteriorPoint x₀) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsRightMIntegralCurveAt γ v t₀ :=
  exists_isRightMIntegralCurveAt_of_contMDiffAt _ hv
    (isInwardPointing_of_isInteriorPoint (n := 1) hx)

variable {t₀}


open NNReal in
/-- Local uniqueness of ODE solutions. -/
theorem ODE_solution_unique_right_of_eventually {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0} {f g : ℝ → E} {t₀ : ℝ}
    (hv : ∀ᶠ t in 𝓝[≥] t₀, LipschitzOnWith K (v t) (s t))
    (hf : ∀ᶠ t in 𝓝[≥] t₀, HasDerivWithinAt f (v t (f t)) (Ici t₀) t ∧ f t ∈ s t)
    (hg : ∀ᶠ t in 𝓝[≥] t₀, HasDerivWithinAt g (v t (g t)) (Ici t₀) t ∧ g t ∈ s t)
    (heq : f t₀ = g t₀) : f =ᶠ[𝓝[≥] t₀] g := by
  obtain ⟨u, hu, h⟩ := Filter.eventually_iff_exists_mem.mp (hv.and (hf.and hg))
  rw [mem_nhdsGE_iff_exists_Icc_subset] at hu
  -- might be nicer to directly have a lemma that gives you this `t` instead of going through `u`
  obtain ⟨t, htt₀, ht⟩ := hu
  rw [Filter.eventuallyEq_iff_exists_mem]
  use Icc t₀ t, Icc_mem_nhdsGE htt₀
  exact ODE_solution_unique_of_mem_Icc_right (fun x hx ↦ (h x (ht (Ico_subset_Icc_self hx))).1)
    (fun x hx ↦ (h x (ht hx)).2.1.1.continuousWithinAt.mono Icc_subset_Ici_self)
    (fun x hx ↦ (h x (ht (Ico_subset_Icc_self hx))).2.1.1.mono (Ici_subset_Ici.mpr hx.1))
    (fun x hx ↦ (h x (ht (Ico_subset_Icc_self hx))).2.1.2)
    (fun x hx ↦ (h x (ht hx)).2.2.1.continuousWithinAt.mono Icc_subset_Ici_self)
    (fun x hx ↦ (h x (ht (Ico_subset_Icc_self hx))).2.2.1.mono (Ici_subset_Ici.mpr hx.1))
    (fun x hx ↦ (h x (ht (Ico_subset_Icc_self hx))).2.2.2) heq

/-- Local integral curves are unique.

If a $C^1$ vector field `v` admits two local integral curves `γ γ' : ℝ → M` at `t₀` with
`γ t₀ = γ' t₀`, then `γ` and `γ'` agree on some open interval containing `t₀`. -/
theorem isRightMIntegralCurveAt_eventuallyEq_of_contMDiffAt
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsRightMIntegralCurveAt γ v t₀) (hγ' : IsRightMIntegralCurveAt γ' v t₀)
    (h : γ t₀ = γ' t₀) : γ =ᶠ[𝓝[≥] t₀] γ' := by
  -- first define `v'` as the vector field expressed in the local chart around `γ t₀`
  -- this is basically what the function looks like when `hv` is unfolded
  set v' : E → E := fun x ↦
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀) ((extChartAt I (γ t₀)).symm x)
      (v ((extChartAt I (γ t₀)).symm x)) with hv'
  -- extract a set `s` on which `v'` is Lipschitz
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  have := hv.snd.exists_lipschitzOnWith I.convex_range
  obtain ⟨K, s, hs, hlip⟩ := hv.snd.exists_lipschitzOnWith I.convex_range
  have hlip (t : ℝ) : LipschitzOnWith K ((fun _ ↦ v') t) ((fun _ ↦ s) t) := hlip
  -- internal lemmas to reduce code duplication
  have hsrc {g} (hg : IsRightMIntegralCurveAt g v t₀) :
    ∀ᶠ t in 𝓝[≥] t₀, g ⁻¹' (extChartAt I (g t₀)).source ∈ 𝓝[Ici t₀] t :=
      eventually_mem_nhdsWithin_iff.mpr <| continuousWithinAt_def.mp hg.continuousWithinAt _
        (extChartAt_source_mem_nhds (g t₀))
  have hmem {g : ℝ → M} {t} (htt₀ : t₀ ≤ t)
      (ht : g ⁻¹' (extChartAt I (g t₀)).source ∈ 𝓝[Ici t₀] t) :
      g t ∈ (extChartAt I (g t₀)).source := by
    apply mem_preimage.mp
    exact mem_of_mem_nhdsWithin htt₀ ht
  have hdrv {g} (hg : IsRightMIntegralCurveAt g v t₀) (h' : γ t₀ = g t₀) : ∀ᶠ t in 𝓝[≥] t₀,
      HasDerivWithinAt ((extChartAt I (g t₀)) ∘ g) ((fun _ ↦ v') t
      (((extChartAt I (g t₀)) ∘ g) t)) (Ici t₀) t ∧
      ((extChartAt I (g t₀)) ∘ g) t ∈ (fun _ ↦ s) t := by
    apply Filter.Eventually.and
    · apply (hsrc hg |>.and hg.eventually_hasDerivWithinAt).mp
      apply eventually_nhdsWithin_of_forall
      intro t htt₀ ⟨ht1, ht2⟩
      rw [hv', h']
      apply ht2.congr_deriv
      congr <;>
      rw [Function.comp_apply, PartialEquiv.left_inv _ (hmem htt₀ ht1)]
    · obtain ⟨t, htt₀, ht⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 <|
        (continuousWithinAt_def.1 hg.continuousWithinAt)
        (extChartAt I (g t₀)).source (extChartAt_source_mem_nhds (g t₀))
      have : ContinuousWithinAt g (Icc t₀ t) t₀ := by
        apply hg.continuousWithinAt.congr_set
        rw [← nhdsWithin_eq_iff_eventuallyEqSet]
        exact (nhdsWithin_Icc_eq_nhdsGE' htt₀).symm
      rw [← nhdsWithin_Icc_eq_nhdsGE' htt₀]
      apply ((continuousAt_extChartAt (g t₀)).comp_continuousWithinAt
        this).preimage_mem_nhdsWithin'
      rw [Function.comp_apply, ← h']
      suffices 𝓝[(extChartAt I (γ t₀)) ∘ g '' Icc t₀ t] (extChartAt I (γ t₀)) (γ t₀) ≤
          𝓝[range I] (extChartAt I (γ t₀)) (γ t₀) from
        this hs
      apply nhdsWithin_mono
      rw [image_comp]
      apply subset_trans ?_ (extChartAt_target_subset_range (γ t₀))
      rw [← PartialEquiv.image_source_eq_target (extChartAt I (γ t₀)), h']
      apply image_mono
      exact image_subset_iff.mpr ht
  have heq {g} (hg : IsRightMIntegralCurveAt g v t₀) :
      g =ᶠ[𝓝[≥] t₀] (extChartAt I (g t₀)).symm ∘ ↑(extChartAt I (g t₀)) ∘ g := by
    refine (hsrc hg).mp <| eventually_nhdsWithin_of_forall ?_
    intro t htt₀ ht
    rw [Function.comp_apply, Function.comp_apply, PartialEquiv.left_inv _ (hmem htt₀ ht)]
  -- main proof
  suffices (extChartAt I (γ t₀)) ∘ γ =ᶠ[𝓝[≥] t₀] (extChartAt I (γ' t₀)) ∘ γ' from
    (heq hγ).trans <| (this.fun_comp (extChartAt I (γ t₀)).symm).trans (h ▸ (heq hγ').symm)
  apply ODE_solution_unique_right_of_eventually (.of_forall hlip) (hdrv hγ rfl) (hdrv hγ' h)
  simp [h]

omit [IsManifold I 1 M] in
lemma IsMIntegralCurveOn.isRightMIntegralCurve [T2Space M] {a b : ℝ} (hab : a < b)
    (hγ : IsMIntegralCurveOn γ v (Ico a b)) : IsRightMIntegralCurveAt γ v a := by
  rw [IsRightMIntegralCurveAt, Filter.eventually_iff_exists_mem]
  use Ico a b, Ico_mem_nhdsGE hab
  intro t ht
  refine (hasMFDerivWithinAt_congr_set ?_).1 (hγ t ht)
  rw [← nhdsWithin_eq_iff_eventuallyEqSet]
  exact nhdsWithin_Ico_eq_nhdsGE' ht.2

@[simp]
theorem left_lt_midpoint {k E : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E]
    [IsStrictOrderedModule k E] [PosSMulReflectLE k E] {a b : E} :
    a < midpoint k a b ↔ a < b :=
  left_lt_lineMap_iff_lt <| inv_pos.2 zero_lt_two

@[simp]
theorem midpoint_lt_right {k E : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E]
    [IsStrictOrderedModule k E] [PosSMulReflectLE k E] {a b : E} :
    midpoint k a b < b ↔ a < b :=
  lineMap_lt_right_iff_lt two_inv_lt_one

/-- Integral curves are unique on open intervals.

If a $C^1$ vector field `v` admits two integral curves `γ γ' : ℝ → M` on some open interval
`Ioo a b`, and `γ t₀ = γ' t₀` for some `t ∈ Ioo a b`, then `γ` and `γ'` agree on `Ioo a b`. -/
theorem isMIntegralCurveOn_Ico_eqOn_of_contMDiff [T2Space M] {a b : ℝ} (hab : a < b)
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Ico a b)) (hγ' : IsMIntegralCurveOn γ' v (Ico a b))
    (h : γ a = γ' a) : EqOn γ γ' (Ico a b) := by
  set s := {t | γ t = γ' t} ∩ Ico a b
  suffices hsub : Ico a b ⊆ s from fun t ht ↦ mem_ofPred.mp ((subset_def ▸ hsub) t ht).1
  set x := sSup {x ∈ Ico a b| ∀ y ≤ x, a ≤ y → y ∈ s} with hx
  have hxset : BddAbove {x ∈ Ico a b| ∀ y ≤ x, a ≤ y → y ∈ s} := ⟨b, fun y ⟨hy, _⟩ ↦ hy.2.le⟩
  have ha : a ∈ {x ∈ Ico a b| ∀ y ≤ x, a ≤ y → y ∈ s} :=
    ⟨left_mem_Ico.mpr hab, fun y hy hay ↦ eq_of_le_of_ge hy hay ▸ ⟨h, left_mem_Ico.mpr hab⟩⟩
  have hxnon : {x ∈ Ico a b| ∀ y ≤ x, a ≤ y → y ∈ s}.Nonempty := ⟨a, ha⟩
  have hxsa : ∀ z < x, a ≤ z → z ∈ s := by
    intro y hyx
    rw [hx, lt_csSup_iff hxset hxnon] at hyx
    obtain ⟨z, ⟨hz, hzs⟩, hyz⟩ := hyx
    apply hzs _ hyz.le
  suffices x = b from fun y ⟨hya, hyb⟩ ↦ hxsa _ (this ▸ hyb) hya
  by_contra hxb
  have hxb' : x < b := by
    apply lt_of_le_of_ne ?_ hxb
    apply csSup_le hxnon
    intro y ⟨hy, _⟩
    exact hy.2.le
  have hxa : a ≤ x := le_csSup hxset ha
  suffices ∃ y > x, y ∈ {y | y ∈ Ico a b ∧ ∀ z ≤ y, a ≤ z → z ∈ s} by
    obtain ⟨y, hyx, hy⟩ := this
    exact not_le_of_gt hyx (le_csSup hxset hy)
  have hxs : x ∈ s := by
    obtain ⟨u, hu, (hux : Filter.Tendsto u Filter.atTop (𝓝 x)), hus⟩ :=
      exists_seq_tendsto_sSup hxnon hxset
    refine ⟨?_, ⟨hxa, hxb'⟩⟩
    suffices x ∈ {t | γ t = γ' t} ∩ Icc a x from this.1
    have : IsClosed ({t | γ t = γ' t} ∩ Icc a x) := by
      rw [inter_comm]
      exact isClosed_Icc.isClosed_eq (hγ.continuousOn.mono (Icc_subset_Ico_right hxb'))
        (hγ'.continuousOn.mono (Icc_subset_Ico_right hxb'))
    apply this.mem_of_frequently_of_tendsto ?_ hux
    apply Filter.Frequently.of_forall
    intro n
    exact ⟨((hus n).2 (u n) (le_refl _) (hus n).1.1).1, ⟨(hus n).1.1, hu.ge_of_tendsto hux _⟩⟩
  obtain ⟨t, ht, htγ⟩ := Filter.eventuallyEq_iff_exists_mem.1
    (isRightMIntegralCurveAt_eventuallyEq_of_contMDiffAt hv.contMDiffAt
    ((hγ.mono (Ico_subset_Ico_left hxa)).isRightMIntegralCurve hxb' )
    ((hγ'.mono (Ico_subset_Ico_left hxa)).isRightMIntegralCurve hxb') hxs.1)
  -- we should have a lemma that does this directly
  obtain ⟨c, hc, hct⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 ht
  use midpoint ℝ x (min b c), left_lt_midpoint.2 <| lt_min hxb' hc
  have hbc : midpoint ℝ x (min b c) < b :=
    lt_of_lt_of_le (midpoint_lt_right.mpr (lt_min hxb' hc)) (min_le_left b c)
  refine ⟨⟨hxa.trans (left_lt_midpoint.2 <| lt_min hxb' hc).le, hbc⟩, ?_⟩
  intro z hz haz
  refine ⟨?_, ⟨haz, lt_of_le_of_lt hz hbc⟩⟩
  by_cases! hzx : z < x
  · exact (hxsa _ hzx haz).1
  · refine htγ (hct ?_)
    exact ⟨hzx, hz.trans ((midpoint_lt_right.mpr (lt_min hxb' hc)).le.trans (min_le_right b c))⟩

end

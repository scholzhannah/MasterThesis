/-
Copyright (c) 2026 Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Scholz
-/
module

public import CollarNeighbourhoods.IsInwardPointingVectorField
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import CollarNeighbourhoods.ExistsUniqueBoundary
public import CollarNeighbourhoods.PR26394.ExistUnique

/-! Header-/

open Set Function Filter Module EuclideanSpace Convexity
open scoped Topology Manifold ContDiff

public section

variable {M H : Type*} [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]

-- this is how we say that `M` is a smooth manifold
variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] (t₀ : ℝ)
  {I : ModelWithCorners ℝ E H} {n : ℕ∞} [NeZero n] [IsManifold I n M]

def IsLocalFlowDomain (D : Set (M × ℝ)) :=
  ∀ p, {t | (p, t) ∈ D}.Nonempty → (IsConnected {t | (p, t) ∈ D} ∧ (p, t₀) ∈ D)

def IsFlowDomain (D : Set (M × ℝ)) :=
  ∀ p, IsConnected {t | (p, t) ∈ D} ∧ (p, t₀) ∈ D

structure IsFlowOn (γ : M → ℝ → M) (D : Set (M × ℝ)) (v : (x : M) → TangentSpace I x) where
  isMIntegralCurveOn p : IsMIntegralCurveOn (fun x ↦ γ p x) v {t | (p, t) ∈ D}
  toFun_zero : ∀ p, {t | (p, t) ∈ D}.Nonempty → γ p t₀ = p

omit [TopologicalSpace M] in
lemma isFlowDomain_univ : IsFlowDomain t₀ (univ : Set (M × ℝ)) := by
  intro
  simp [isConnected_univ]

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} (t₀ : ℝ) {x₀ : M}

omit [TopologicalSpace M] in
lemma isLocalFlowDomain_sprod_ico {u : Set M} {ε : ℝ} (hε : ε > 0) :
    IsLocalFlowDomain t₀ (u ×ˢ (Ico t₀ (t₀ + ε))) := by
  intro p ⟨_, hp, _⟩
  refine ⟨?_, ⟨hp, left_mem_Ico.mpr ((lt_add_iff_pos_right t₀).mpr hε)⟩⟩
  simp only [mem_prod, hp, true_and, ofPred_mem_eq]
  exact isConnected_Ico ((lt_add_iff_pos_right t₀).mpr hε)

omit [TopologicalSpace M] in
lemma isLocalFlowDomain_sprod_ioo {u : Set M} {ε : ℝ} (hε : ε > 0) :
    IsLocalFlowDomain t₀ (u ×ˢ (Ioo (t₀ - ε) (t₀ + ε))) := by
  intro p ⟨_, hp, _⟩
  refine ⟨?_, ⟨hp, by simp [hε]⟩⟩
  simp only [mem_prod, hp, true_and, ofPred_mem_eq]
  refine isConnected_Ioo ?_
  exact lt_trans (sub_lt_self t₀ hε) ((lt_add_iff_pos_right t₀).mpr hε)

variable (E H I v) in
structure LocalFlow (t₀ : ℝ) where
  domain : Set (M × ℝ)
  isLocalFlowDomain : IsLocalFlowDomain t₀ domain
  map : M → ℝ → M
  flowOn : IsFlowOn t₀ map domain v

set_option backward.isDefEq.respectTransparency false in
lemma hasDerivAt_extChartAt_comp_extChartAt_comp_of_hasDerivAt_tangentCoordChange
    {x₀ : M} {f : ℝ → E} {t : ℝ} {v : TangentSpace I ((extChartAt I x₀).symm (f t))}
    {ε : ℝ} (hε : MapsTo f (Ico t₀ (t₀ + ε)) (range I))
    (hmem : f t ∈ (extChartAt I x₀).target)
    (hf : let xₜ : M := (extChartAt I x₀).symm (f t)
      HasDerivWithinAt f (tangentCoordChange I xₜ x₀ xₜ v) (Ico t₀ (t₀ + ε)) t) :
    let xₜ : M := (extChartAt I x₀).symm (f t)
    HasDerivWithinAt (((extChartAt I xₜ) ∘ (extChartAt I x₀).symm) ∘ f) v (Ico t₀ (t₀ + ε)) t := by
  dsimp only
  let xₜ : M := (extChartAt I x₀).symm (f t)
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hmem (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  rw [← tangentCoordChange_self (I := I) (v := v) hft2,
    ← tangentCoordChange_comp ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivWithinAt.comp_hasDerivWithinAt _ _ hf (t := range I)
  · exact hε
  · nth_rw 2 [← (extChartAt I x₀).right_inv hmem]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

set_option backward.isDefEq.respectTransparency false in
/-- Let `f : ℝ → E` and `v` be a tangent vector field on `M`. This lemma gives what `f'(t)` needs to
be in the model space in order for $(\phi_{x_0}^{-1} ∘ f)'(t) = v(\phi_{x_0}^{-1}(f(t))$ to hold
on the manifold. -/
lemma hasMFDerivAt_extChartAt_comp_of_hasDerivAt {ε : ℝ} {v : (x : M) → TangentSpace I x} {x₀ : M}
    {f : ℝ → E} {t : ℝ} (hε : MapsTo f (Ico t₀ (t₀ + ε)) (range I))
    (hmem : f t ∈ (extChartAt I x₀).target)
    (hf : HasDerivWithinAt f (((extChartAt I.tangent (⟨x₀, v x₀⟩ : TangentBundle I M)) ∘
      (fun x ↦ ⟨x, v x⟩) ∘ (extChartAt I x₀).symm) (f t)).2 (Ico t₀ (t₀ + ε)) t) :
    HasMFDerivAt[Ico t₀ (t₀ + ε)] ((extChartAt I x₀).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((extChartAt I x₀).symm (f t)))) := by
  let xₜ : M := (extChartAt I x₀).symm (f t)
  change HasDerivWithinAt f (tangentCoordChange I xₜ x₀ xₜ (v xₜ)) (Ico t₀ (t₀ + ε)) t at hf
  refine ⟨continuousAt_extChartAt_symm'' hmem |>.comp_continuousWithinAt (x := t)
    hf.continuousWithinAt, HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps]
  exact hasDerivAt_extChartAt_comp_extChartAt_comp_of_hasDerivAt_tangentCoordChange _ hε hmem hf

theorem exists_mem_nhds_isFlowOn_Ioo_of_contMDiffAt' [CompleteSpace E]
    (hv1 : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx2 : IsInwardPointing (v x₀)) :
    ∃ u ∈ 𝓝 x₀, ∃ ε > (0 : ℝ), ∃ γ : M → ℝ → M, IsFlowOn t₀ γ (u ×ˢ (Ico t₀ (t₀ + ε))) v := by
  have hv := (contMDiffAt_iff.mp hv1).2
  let f := ((extChartAt I.tangent (⟨x₀, v x₀⟩ : Bundle.TotalSpace E (TangentSpace I))) ∘
    (fun x ↦ ⟨x, v x⟩) ∘ ↑(extChartAt I x₀).symm)
  have hf : inwardPointing (range I) ((extChartAt I x₀) x₀) (f ((extChartAt I x₀) x₀)).2 := by
    rw [isInwardPointing_iff_inwardPointing_extChartAt (n := 1)] at hx2
    convert hx2
    unfold f
    rw [Function.comp_apply, Function.comp_apply,
      PartialEquiv.left_inv (extChartAt I x₀) (mem_extChartAt_source x₀),
      FiberBundle.extChartAt ⟨x₀, v x₀⟩]
    simp [TangentBundle.trivializationAt_apply x₀ ⟨x₀, v x₀⟩,
      (mdifferentiableAt_extChartAt (mem_chart_source H x₀)).mvfderiv (f := I ∘ (chartAt H x₀))]
    rfl
  have := hv.snd
  obtain ⟨α, hα⟩ :=
    ContDiffWithinAt.exists_eventually_eq_hasDerivWithinAt_continuousWithinAt
    I.convex_range I.isClosed_range I.nonempty_interior (x₀ := extChartAt I x₀ x₀)
    (f := fun x ↦ (f x).2)
    (extChartAt_target_subset_range _ <| mem_extChartAt_target x₀) hf hv.snd t₀
  simp only [Filter.eventually_and] at hα
  obtain ⟨hα1, hα2, hα3, hα4⟩ := hα
  -- extract explicit product neighbourhoods for the continuity condition
  rw [nhdsWithin_prod_eq, Filter.eventually_prod_iff_exists_mem] at hα4
  obtain ⟨u0, hu0, s0, hs0, hα4'⟩ := hα4
  have huox₀ : extChartAt I x₀ x₀ ∈ u0 := mem_of_mem_nhdsWithin (by exact mem_range_self _) hu0
  have hs0t₀ : t₀ ∈ s0 := mem_of_mem_nhdsWithin self_mem_Ici hs0
  have hcont' : ∀ A ∈ 𝓝[range I] (α (extChartAt I x₀ x₀, t₀)), α ⁻¹' A ∈
      𝓝[(range I) ×ˢ (Ici t₀)] (extChartAt I x₀ x₀, t₀) := by
    intro A hA
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hA
    obtain ⟨u, hu, huα⟩ := hA
    suffices α ⁻¹' u ∈ 𝓝[(range I) ×ˢ (Ici t₀)] (extChartAt I x₀ x₀, t₀) by
      rw [Filter.eventually_iff_exists_mem] at hα3
      obtain ⟨v, hv, hvI⟩ := hα3
      apply Filter.mem_of_superset (Filter.inter_mem this hv)
      intro x ⟨hx1, hx2⟩
      exact huα ⟨hx1, hvI x hx2⟩
    exact hα4' _ huox₀ t₀ hs0t₀ hu
  have hnhds : α ⁻¹' ((extChartAt I x₀).target) ∈
      𝓝[(range I) ×ˢ (Ici t₀)] (extChartAt I x₀ x₀, t₀) := by
    apply hcont'
    rw [hα1.self_of_nhdsWithin (by simp)]
    exact extChartAt_target_mem_nhdsWithin x₀
  have hα5 :  ∀ᶠ (x : E × ℝ) in 𝓝[range I ×ˢ Ici t₀] ((extChartAt I x₀) x₀, t₀),
      α x ∈ (extChartAt I x₀).target := by
    rw [Filter.eventually_iff_exists_mem]
    use α ⁻¹' (extChartAt I x₀).target, hnhds
    exact fun x hx ↦ hx
  rw [nhdsWithin_prod_eq] at hα1 hα2 hα5
  obtain ⟨u, hu, s, hs, hf⟩ :=
    Filter.eventually_prod_iff_exists_mem.mp (hα1.and (hα2.and hα5))
  have ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.inter_mem hs0 hs)
  rw [Real.ball_eq_Ioo t₀ ε, ← Iio_inter_Ioi, inter_assoc,
    inter_eq_self_of_subset_right (s := Ioi (t₀ - ε))
    (by exact fun i hi ↦  lt_of_lt_of_le (sub_lt_self t₀ hε) hi), Iio_inter_Ici] at hεs
  let U := (extChartAt I x₀) ⁻¹' (u0 ∩ u) ∩ (extChartAt I x₀).source
  let γ (xt : M × ℝ) := (extChartAt I x₀).symm (α (extChartAt I x₀ xt.1, xt.2))
  use U
  constructor
  · refine Filter.inter_mem ?_ (extChartAt_source_mem_nhds x₀)
    rw [← nhdsWithin_univ x₀]
    apply (continuousAt_extChartAt _).continuousWithinAt.preimage_mem_nhdsWithin'
    refine (nhdsWithin_mono _ ?_) (Filter.inter_mem hu0 hu)
    rw [image_univ, range_subset_iff]
    exact fun _ ↦ mem_range_self _
  · use ε, hε, curry γ
    constructor
    · intro p t ⟨hp, ht⟩
      simp only [curry_apply, mem_prod, hp, mem_Ico, true_and, γ]
      apply hasMFDerivAt_extChartAt_comp_of_hasDerivAt
      · intro t ht
        exact extChartAt_target_subset_range x₀ (hf (extChartAt I x₀ p) hp.1.2 t (hεs ht).2).2.2
      · exact (hf (extChartAt I x₀ p) hp.1.2 t (hεs ht).2).2.2
      · simp only [comp_apply]
        have := (hf (extChartAt I x₀ p) hp.1.2 t (hεs ht).2).2.1
        apply this.congr_set
        rw [← nhdsWithin_eq_iff_eventuallyEqSet]
        exact (nhdsWithin_Ico_eq_nhdsGE' ht.2).symm
    · intro p ⟨_, hp, _⟩
      simp_rw [curry_apply, γ,
        (hf (extChartAt I x₀ p) hp.1.2 t₀ (mem_of_mem_nhdsWithin (self_mem_Ici) hs)).1,
        PartialEquiv.left_inv (extChartAt I x₀) hp.2]

@[expose]
noncomputable def LocalRightFlowAt [CompleteSpace E]
    (hv1 : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hv2 : IsInwardPointing (v x₀)) : LocalFlow E H I v t₀ :=
  letI u := (exists_mem_nhds_isFlowOn_Ioo_of_contMDiffAt' t₀ hv1 hv2).choose
  letI ε := (exists_mem_nhds_isFlowOn_Ioo_of_contMDiffAt' t₀ hv1 hv2).choose_spec.2.choose
  haveI hε := (exists_mem_nhds_isFlowOn_Ioo_of_contMDiffAt' t₀ hv1 hv2).choose_spec.2.choose_spec.1
  letI γ :=
    (exists_mem_nhds_isFlowOn_Ioo_of_contMDiffAt' t₀ hv1 hv2).choose_spec.2.choose_spec.2.choose
  haveI hγ := (exists_mem_nhds_isFlowOn_Ioo_of_contMDiffAt' t₀ hv1
    hv2).choose_spec.2.choose_spec.2.choose_spec
  { domain := u ×ˢ (Ico t₀ (t₀ + ε))
    isLocalFlowDomain := isLocalFlowDomain_sprod_ico t₀ hε
    map := γ
    flowOn := hγ }

@[expose]
noncomputable def LocalTwoSidedFlowAt [CompleteSpace E]
    (hv1 : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx : I.IsInteriorPoint x₀) : LocalFlow E H I v t₀ :=
  letI u := (PR26394.exists_mem_nhds_isMIntegralCurveOn_Ioo_of_contMDiffAt t₀ hv1 hx).choose
  letI ε :=
    (PR26394.exists_mem_nhds_isMIntegralCurveOn_Ioo_of_contMDiffAt t₀ hv1 hx).choose_spec.2.choose
  haveI hε := (PR26394.exists_mem_nhds_isMIntegralCurveOn_Ioo_of_contMDiffAt
    t₀ hv1 hx).choose_spec.2.choose_spec.1
  letI γ := (PR26394.exists_mem_nhds_isMIntegralCurveOn_Ioo_of_contMDiffAt
    t₀ hv1 hx).choose_spec.2.choose_spec.2.choose
  haveI hγ := (PR26394.exists_mem_nhds_isMIntegralCurveOn_Ioo_of_contMDiffAt
    t₀ hv1 hx).choose_spec.2.choose_spec.2.choose_spec
  { domain := u ×ˢ (Ioo (t₀ - ε) (t₀ + ε))
    isLocalFlowDomain := isLocalFlowDomain_sprod_ioo t₀ hε
    map := curry γ
    flowOn := by
      constructor
      · intro p t ⟨hp, ht⟩
        simp only [curry_apply, mem_prod, hp, true_and]
        exact (hγ p hp).2.1 _ ht
      · intro p ⟨t, ⟨hp, ht⟩⟩
        exact (hγ p hp).1 }

lemma mem_localFlowAt_domain [CompleteSpace E]
    (hv1 : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hv2 : IsInwardPointing (v x₀)) : (x₀, t₀) ∈ (LocalRightFlowAt t₀ hv1 hv2).domain := by
  have hu := (exists_mem_nhds_isFlowOn_Ioo_of_contMDiffAt' t₀ hv1 hv2).choose_spec.1
  have hε := (exists_mem_nhds_isFlowOn_Ioo_of_contMDiffAt' t₀ hv1 hv2).choose_spec.2.choose_spec.1
  simp [LocalRightFlowAt, hε, mem_of_mem_nhds hu]

variable (v) in
def MaximalFlowDomain (t₀ : ℝ) :=
  ⋃₀ {D : Set (M × ℝ) | ∃ (γ : LocalFlow E H I v t₀), γ.domain = D}

@[instance_reducible]
noncomputable def inhabited_LocalFlow [CompleteSpace E] [Inhabited M]
  (hv1 : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
  (hv2 : ∀ x, IsInwardPointing (v x)) : Inhabited (LocalFlow E H I v t₀) :=
  ⟨LocalRightFlowAt t₀ (hv1 default) (hv2 default)⟩

lemma isFlowDomain_maximalFlowDomain [CompleteSpace E] [Inhabited M]
    (hv1 : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hv2 : ∀ x, IsInwardPointing (v x)) (t₀ : ℝ) :
    IsFlowDomain t₀ (MaximalFlowDomain v t₀) := by
  intro p
  constructor
  · unfold MaximalFlowDomain
    simp_rw [sUnion_eq_biUnion, mem_iUnion, ofPred_exists]
    simp only [ofPred_eq_eq_singleton', iUnion_singleton_eq_range, mem_range, iUnion_exists,
      iUnion_iUnion_eq']
    suffices IsConnected (⋃ (y : LocalFlow E H I v t₀) (hy : {x | (p, x) ∈ y.domain}.Nonempty),
        {x | (p, x) ∈ y.domain}) by
      simpa
    apply IsConnected.biUnion_of_reflTransGen
    · refine ⟨LocalRightFlowAt t₀ (hv1 p) (hv2 p), ?_⟩
      exact ⟨t₀, mem_ofPred_eq ▸ mem_localFlowAt_domain t₀ (hv1 p) (hv2 p)⟩
    · intro γ ⟨t, ht⟩
      exact (γ.isLocalFlowDomain p ⟨t, ht⟩).1
    · intro γ₁ ⟨t₁, ht₁⟩ γ₂ ⟨t₂, ht₂⟩
      rw [Relation.ReflTransGen.cases_tail_iff]
      right
      use γ₁, Relation.ReflTransGen.refl
      refine ⟨⟨t₀, ?_⟩, ⟨t₁, ht₁⟩⟩
      simp [(γ₁.isLocalFlowDomain p ⟨t₁, ht₁⟩).2, (γ₂.isLocalFlowDomain p ⟨t₂, ht₂⟩).2]
  · simp only [MaximalFlowDomain, mem_sUnion, mem_ofPred_eq, exists_exists_eq_and]
    exact ⟨LocalRightFlowAt t₀ (hv1 p) (hv2 p), mem_localFlowAt_domain t₀ (hv1 p) (hv2 p)⟩

open Classical in
variable (v) in
noncomputable def MaximalFlowMap [Inhabited M] (t₀ : ℝ) : M → ℝ → M :=
  fun x t ↦ if h : ∃ (γ : LocalFlow E H I v t₀), (x, t) ∈ γ.domain then
      h.choose.map x t else default

example (γ₁ γ₂ : LocalFlow E H I v t₀) : EqOn (uncurry γ₁.map) (uncurry γ₂.map)
    (γ₁.domain ∩ γ₂.domain) := by
  intro ⟨x, t⟩ ⟨h1, h2⟩

  sorry

/-noncomputable def MaximalFlowMap [CompleteSpace E]
  (hv1 : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
  (hv2 : ∀ x, IsInwardPointing (v x)) (t₀ : ℝ) :
  M → ℝ → M :=
  fun x ↦ if h : I.IsInteriorPoint x then (LocalTwoSidedFlowAt t₀ (hv1 x) h).map x else
    (LocalRightFlowAt t₀ (hv1 x) (hv2 x)).map x-/

lemma isMIntegralCurveOn_maximalFlowMap [CompleteSpace E] [Inhabited M]
    (hv1 : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hv2 : ∀ x, IsInwardPointing (v x)) (t₀ : ℝ) (p : M) :
    IsMIntegralCurveOn (MaximalFlowMap v t₀ p) v {t | (p, t) ∈ MaximalFlowDomain v t₀} := by
  -- I think I might have to differentiate between interior points and boundary points
  by_cases hp : I.IsInteriorPoint p
  · intro t ⟨_, ⟨⟨γ, rfl⟩, hpγ⟩⟩


    rw [MaximalFlowMap, dite_eq_left ⟨γ, hpγ⟩]

    have hγ := (LocalTwoSidedFlowAt t₀ (hv1 p) hp).flowOn.isMIntegralCurveOn p t



    have := γ.flowOn.isMIntegralCurveOn p t hpγ
    sorry
  sorry


lemma isFlowOn_maximalFlowMap_maximalFlowDomain [CompleteSpace E] [Inhabited M]
    (hv1 : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hv2 : ∀ x, IsInwardPointing (v x))
    (t₀ : ℝ) :
    IsFlowOn t₀ (MaximalFlowMap v t₀) (MaximalFlowDomain v t₀) v where
  isMIntegralCurveOn := by
    intro p t ⟨_, ⟨⟨γ, rfl⟩, hpγ⟩⟩
    have := γ.flowOn.isMIntegralCurveOn p t hpγ


    sorry
  toFun_zero := by
    rintro p _
    rw [MaximalFlowMap, dite_eq_left ⟨LocalRightFlowAt t₀ (hv1 p) (hv2 p),
      mem_localFlowAt_domain t₀ (hv1 p) (hv2 p)⟩]
    apply (LocalFlow.flowOn _).toFun_zero
    use t₀
    exact Exists.choose_spec (_ : ∃ (γ : LocalFlow E H I v t₀), (p, t₀) ∈ γ.domain)

/-
-- wrong
lemma isFlowDomain_ico_prod_nhd (t₀ : ℝ) {ε : ℝ} (hε : ε > 0) {x₀ : M} {u : Set M} (hu : u ∈ 𝓝 x₀) :
    IsLocalFlowDomain t₀ ((Ico t₀ (t₀ + ε)) ×ˢ u) := by
  intro p
  constructor
  · sorry
  · sorry






#check exists_isMIntegralCurveAt_of_contMDiffAt

lemma PartialEquiv.isInvertible_of_contMDiff  {H' : Type*} [TopologicalSpace H'] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (p : M') (f : PartialEquiv M M') (hp : p ∈ f.target) (hf : CMDiff[f.source] n f) :
    (mfderiv[f.target] f.symm p).IsInvertible := by

  sorry

lemma isMIntegralCurve_pullback
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (s : Set ℝ) (hγ : IsMIntegralCurveOn γ v s)
    (f : PartialEquiv M M') (hs : γ '' s ⊆ f.source) (hf : CMDiff[f.source] n f)
    (hf : CMDiff[f.target] n f.symm) :
    IsMIntegralCurveOn (f ∘ γ)
      (VectorField.mpullbackWithin I' I f.symm v f.target) s := by
  intro t ht
  unfold VectorField.mpullbackWithin
  have : (mfderiv[f.target] f.symm ((f ∘ γ) t)).inverse = mfderiv[f.source] f (γ t) := by
    have : (mfderiv[f.target] f.symm ((f ∘ γ) t)).IsInvertible := sorry
    ext x
    rw [this.inverse_apply_eq]

    sorry
  rw [this]
  rw [comp_apply]
  rw [PartialEquiv.left_inv f (hs (mem_image_of_mem γ ht))]

  sorry

theorem isMIntegralCurve_iff_isIntegralCurve (γ : ℝ → M) (v : (x : M) → TangentSpace I x)
    (s : Set ℝ) (t : ℝ) (ht : t ∈ s) (hγ : IsMIntegralCurveOn γ v s) :
    IsMIntegralCurveOn ((extChartAt I (γ t)) ∘ γ)
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I (γ t)).symm v
      (extChartAt I (γ t)).target)
      (s ∩ (γ ⁻¹' (extChartAt I (γ t)).source)) := by
  unfold IsMIntegralCurveOn HasMFDerivWithinAt at hγ
  intro x hx
  specialize hγ x hx.1



  sorry

theorem isMIntegralCurveOn_Ico_eqOn_of_contMDiff [IsManifold I 1 M] {γ γ' : ℝ → H}
    {v : (x : H) → TangentSpace I x} {t₀ : ℝ} [T2Space M] {a : ℝ} (ha : 0 < a)
    (hγ0 : I.IsBoundaryPoint (γ 0)) (hγt : ∀ t ∈ Ioo 0 a, I.IsInteriorPoint (γ 0))
    (hv : ContMDiff I I.tangent 1 fun (x : H) => (⟨x, v x⟩ : TangentBundle I H))
    (hγ : IsMIntegralCurveOn γ v (Ioo 0 a)) (hγ' : IsMIntegralCurveOn γ' v (Ico 0 a))
    (h : γ 0 = γ' 0) :
    EqOn γ γ' (Set.Ico 0 a) := by


  suffices EqOn γ γ' (Ioo 0 a) by
    intro x hx
    rw [← Ioo_union_left ha] at hx
    rcases hx with hx | hx
    · exact this hx
    · exact hx ▸ h
  -- this doesn't work like this
  sorry-/



-- look at `https://github.com/leanprover-community/mathlib4/pull/26394`.
-- this is only for interior points

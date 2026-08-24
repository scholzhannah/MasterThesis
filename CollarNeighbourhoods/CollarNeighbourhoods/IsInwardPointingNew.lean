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
def IsRealizable' {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (γ : ℝ → M) (ε : ℝ) (_ : ε > 0) (_ : CMDiff[Ico 0 ε] ∞ γ),
    γ 0 = p ∧ HasMFDerivAt[Ici 0] γ (0 : ℝ)
    ((ContinuousLinearMap.toSpanSingleton ℝ v).comp
      (NormedSpace.fromTangentSpace 1).toContinuousLinearMap)

def IsInwardPointingTry2 {p : M} (v : TangentSpace I p) : Prop :=
  v ∈ interior {v | IsRealizable v}


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

lemma isRealizable_of_mem_interior {p : H} (hp : I.IsBoundaryPoint p) (v : TangentSpace I p)
    {ε : ℝ} (hε : ε > 0) (h : I p + ε • d% I p v ∈ interior (range I)) :
    IsRealizable v := by
  unfold IsRealizable
  let γ : ℝ → H := I.symm ∘ fun i ↦ I p + i • mvfderiv I I p v
  have hεI : Ico 0 ε ⊆ (fun i ↦ I p + i • mvfderiv I I p v) ⁻¹' range I := by
    intro i hi
    exact I.convex_range.add_smul_mem_icc (mem_range_self p) hε (interior_subset h)
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
      rw [ModelWithCorners.mvfderiv I]



      sorry
    · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      fun_prop
    · exact hεI
    · exact h0.uniqueMDiffWithinAt
    · simp
  · exact this.mdifferentiableOn (ne_of_beq_false rfl) 0 (left_mem_Ico.mpr hε)
  · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffWithinAt_Ici 0
  · exact Ico_mem_nhdsGE hε

lemma isInwardPointing_iff {p : H} (hp : I.IsBoundaryPoint p) (v : TangentSpace I p) :
    IsInwardPointingTry2 v ↔ ∃ ε > 0, I p + ε • d% I p v ∈ interior I.target := by
  constructor
  · intro h

    sorry
  · intro ⟨ε, hε, h⟩

    sorry

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

variable {n : ℕ} [NeZero n]

def IsInwardPointingTry5 {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (f : M → ℝ) (_ : CMDiff ∞ f) (_ : ∀ x ∈ I.interior M, 0 < f x)
    (_ : ∀ x ∈ I.boundary M, f x = 0), 0 < d% f p v

lemma modelWithCornersEuclideanHalfSpace_apply {p : EuclideanHalfSpace n} : (𝓡∂ n) p = p.val :=
  rfl

lemma modelWithCornersEuclideanHalfSpace_symm_apply {p : EuclideanSpace ℝ (Fin n)} : (𝓡∂ n).symm p =
    ⟨WithLp.toLp 2 (update p 0 (max (p 0) 0)), by simp⟩ :=
  rfl

lemma modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff {p : EuclideanHalfSpace n} :
    (𝓡∂ n).IsBoundaryPoint p ↔ p.val.ofLp 0 = 0 := by
  simp [ModelWithCorners.isBoundaryPoint_iff, range_modelWithCornersEuclideanHalfSpace n,
    modelWithCornersEuclideanHalfSpace_apply, eq_comm]

lemma ModelWithCorners.IsBoundaryPoint.eq_zero_of_modelWithCornersEuclideanHalfSpace
    {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) : p.val.ofLp 0 = 0 :=
  modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.mp hp

lemma modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) : (𝓡∂ n).symm p.val = p := by
  rw [modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff] at hp
  have : (update p.val.ofLp 0 0) = p.val.ofLp := by
    rw [update_eq_self_iff, hp]
  simp [modelWithCornersEuclideanHalfSpace_symm_apply, this, hp]

lemma modelWithCornersEuclideanHalfSpace_boundary_eq :
    (𝓡∂ n).boundary (EuclideanHalfSpace n) = {p | p.val.ofLp 0 = 0} := by
  simp_rw [← modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff]
  rfl

lemma modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff {p : EuclideanHalfSpace n} :
    (𝓡∂ n).IsInteriorPoint p ↔ p.val.ofLp 0 > 0 := by
  simp [ModelWithCorners.isInteriorPoint_iff, range_modelWithCornersEuclideanHalfSpace n,
    modelWithCornersEuclideanHalfSpace_apply]

lemma modelWithCornersEuclideanHalfSpace_interior_eq :
    (𝓡∂ n).interior (EuclideanHalfSpace n) = {p | 0 < p.val.ofLp 0} := by
  simp_rw [← modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff]
  rfl

lemma modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) :
    HasMFDerivAt[{ x : EuclideanSpace ℝ (Fin n) | 0 ≤ x 0 }] (𝓡∂ n).symm
      (p.val)
      -- this line below isn't type correct at all
      -- I think writing this as the derivative of the model with corners is already the only
      -- sensible way to write this
      -- why is this okay for `ModelWithCorners.hasMFDerivAt`?
      (ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) ( p.val))) := by
  refine ⟨(𝓡∂ n).continuousOn_symm.continuousWithinAt (by simp), ?_⟩
  apply HasFDerivWithinAt.congr (f := id)
  · apply HasFDerivAt.hasFDerivWithinAt
    exact hasFDerivAt_id p.val
  · intro x hx
    simp_all [modelWithCornersEuclideanHalfSpace_symm_apply,
      modelWithCornersEuclideanHalfSpace_apply]
  · rw [modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff] at hp
    have : (update p.val.ofLp 0 0) = p.val.ofLp := by
        rw [update_eq_self_iff, hp]
    simp [modelWithCornersEuclideanHalfSpace_symm_apply, modelWithCornersEuclideanHalfSpace_apply,
      hp, this]

lemma modelWithCornersEuclideanHalfSpace_symm_mDifferentialbleWithinAt {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) :
    MDiffAt[{ x : EuclideanSpace ℝ (Fin n) | 0 ≤ x 0 }] (𝓡∂ n).symm p.val :=
  HasMFDerivWithinAt.mdifferentiableWithinAt
    (modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt hp)


-- **ToDo** : Fix defeq abuse tomorrow

--set_option linter.tacticCheckInstances true
--#defeq_abuse in
set_option backward.isDefEq.respectTransparency false in
lemma prop541euclideanTry5 {p : EuclideanHalfSpace n} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5 v ↔ 0 < ((d% (𝓡∂ n) p) v).ofLp 0 := by
  constructor
  · intro ⟨f, hf1, hf2, hf3, hf4⟩
    by_contra! hv
    let x := (mfderiv% (𝓡∂ n) p) v
    let y := (d% (𝓡∂ n) p) v
    have yay1 : d[Ici (0 : ℝ)] (f ∘ (𝓡∂ n).symm ∘ fun (i : ℝ) ↦ p.val - i • y) 0 1 < 0 := by
      unfold mvfderivWithin
      have h1 :  MDiffAt f p := hf1.mdifferentiableAt (ne_of_beq_false rfl)
      have hh : MDiffAt[{x | 0 ≤ x.ofLp 0}] (𝓡∂ n).symm (p.val - (0 : ℝ) • y) := by
        simp only [zero_smul, sub_zero]
        exact modelWithCornersEuclideanHalfSpace_symm_mDifferentialbleWithinAt hp
      have h2'' : MDiffAt[Ici 0] (fun (i : ℝ) ↦ p.val - i • y) 0 := by
          refine DifferentiableWithinAt.mdifferentiableWithinAt ?_
          fun_prop
      have h2''' : Ici 0 ⊆ (fun (i : ℝ) ↦ p.val - i • y) ⁻¹' {x | 0 ≤ x.ofLp 0} := by
        intro x hx
        simp [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, y,
          mul_nonpos_of_nonneg_of_nonpos hx hv]
      have h2 : MDiffAt[Ici 0] ((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ p.val - i • y) 0 := hh.comp 0 h2'' h2'''
      have h3 : UniqueMDiffAt[Ici (0 : ℝ)] 0 := by
        rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
        exact uniqueDiffWithinAt_Ici 0
      have h4 : (↑(𝓡∂ n).symm ∘ fun (i : ℝ) ↦ p.val - i • y) 0 = p := by
        simp [modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint hp]
      rw [mfderiv_comp_mfderivWithin_of_eq h1 h2 h3 h4, ← ContinuousLinearMap.comp_assoc]
      rw [ContinuousLinearMap.comp_apply]
      suffices h : (mfderiv[Ici (0 : ℝ)] ((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ p.val - i • y) 0) 1 =  - v by
        have : (d% f p) (-v) < 0 := by simp [hf4]
        exact h ▸ this
      rw [mfderivWithin_comp 0 hh h2'' h2''' h3]
      rw [zero_smul ℝ y]
      rw [sub_zero]
      rw [HasMFDerivWithinAt.mfderivWithin
        (modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt hp)]
      · simp only [comp_apply, mfderivWithin_eq_fderivWithin, ContinuousLinearMap.id_comp]
        change (fderivWithin ℝ (fun (i : ℝ) ↦ p.val - i • y) (Ici 0) 0) 1 = -v
        rw [fderivWithin_derivWithin (𝕜 := ℝ) (f := fun (i : ℝ) ↦ p.val - i • y) (s := Ici 0)]
        rw [derivWithin_const_sub]
        rw [derivWithin_smul_const differentiableWithinAt_fun_id y]
        rw [derivWithin_id' 0 (Ici 0) (uniqueDiffWithinAt_Ici 0)]
        simp only [mvfderiv, (𝓡∂ n).hasMFDerivAt.mfderiv (x := p), ContinuousLinearMap.comp_id,
          ContinuousLinearEquiv.coe_coe, one_smul, neg_inj, y]
        rfl
      rw [← range_modelWithCornersEuclideanHalfSpace n]
      change UniqueMDiffAt[range (𝓡∂ n)] ((𝓡∂ n) p)
      exact (𝓡∂ n).uniqueMDiffOn _ (mem_range_self p)
    unfold mvfderivWithin at yay1
    simp only [comp_apply, mfderivWithin_eq_fderivWithin, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] at yay1
    rw [zero_smul, sub_zero] at yay1
    -- this is major def-eq abuse caused by `mfderiv_eq_fderiv`
    simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk] at yay1
    -- this uses the assumptions hv and hf3
    have yay2 : 0 ≤ (fderivWithin ℝ (f ∘ ↑(𝓡∂ n).symm ∘ fun i ↦ p.val - i • y)
        (Ici (0 : ℝ)) 0) 1 := by
      apply IsLocalMinOn.fderivWithin_nonneg
      · apply IsMinOn.localize
        intro x hx
        simp only [comp_apply, zero_smul, sub_zero, mem_setOf_eq]
        rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint hp, hf3 p hp]
        by_cases! hx' : x = 0 ∨ ((d% (𝓡∂ n) p) v).ofLp 0 = 0
        · apply ge_of_eq
          apply hf3
          simp [modelWithCornersEuclideanHalfSpace_boundary_eq,
            modelWithCornersEuclideanHalfSpace_symm_apply, y,
            hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, mul_nonpos_of_nonneg_of_nonpos hx hv,
            hx']
        · apply le_of_lt
          apply hf2
          simp only [modelWithCornersEuclideanHalfSpace_interior_eq,
            modelWithCornersEuclideanHalfSpace_symm_apply, WithLp.ofLp_sub, WithLp.ofLp_smul,
            PiLp.sub_apply, hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, PiLp.smul_apply,
            smul_eq_mul, zero_sub, mem_setOf_eq, update_self, right_lt_sup, Left.neg_nonpos_iff,
            not_le, y]
          exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hx hx'.1.symm) (lt_of_le_of_ne hv hx'.2)
      · simp [one_mem_posTangentConeAt_iff_mem_closure,
          inter_eq_self_of_subset_left Ioi_subset_Ici_self]
    apply not_lt_of_ge yay2 yay1
  · intro h
    have h1 : ∀ x ∈ (𝓡∂ n).interior (EuclideanHalfSpace n), 0 < (proj 0 ∘ 𝓡∂ n) x := by
      intro x hx
      simpa [modelWithCornersEuclideanHalfSpace_apply,
        modelWithCornersEuclideanHalfSpace_interior_eq] using hx
    have h2 : ∀ x ∈ (𝓡∂ n).boundary (EuclideanHalfSpace n), (proj 0 ∘ 𝓡∂ n) x = 0 := by
      intro x hx
      simpa [modelWithCornersEuclideanHalfSpace_apply,
        modelWithCornersEuclideanHalfSpace_boundary_eq] using hx
    use proj 0 ∘ 𝓡∂ n, ContDiff.comp_contMDiff (by fun_prop) (𝓡∂ n).contMDiff, h1, h2
    unfold mvfderiv
    -- **Def-eq issues reproducer**:
    -- if you turn the line below into a `simp only`, this causes def-eq issues not caught by
    -- `linter.tacticCheckInstances`, this is especially bad, because this lemma is a
    -- `simp` lemma
    rw [Function.comp_apply]
    have h3 : MDiffAt (proj 0 : StrongDual ℝ (EuclideanSpace ℝ (Fin n))) ((𝓡∂ n) p) := by
      apply DifferentiableAt.mdifferentiableAt
      fun_prop
    rw [mfderiv_comp p h3 (𝓡∂ n).mdifferentiableAt,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.mfderiv_eq (proj 0 : StrongDual ℝ (EuclideanSpace ℝ (Fin n)))]
    exact h

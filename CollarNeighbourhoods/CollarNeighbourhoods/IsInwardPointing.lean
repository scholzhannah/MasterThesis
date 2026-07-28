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

def IsInwardPointingTry5Local {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (f : M → ℝ) (U : Set M) (_ : IsOpen U) (_ : p ∈ U) (_ : CMDiff[U] ∞ f)
    (_ : ∀ x ∈ I.interior M ∩ U, 0 < f x)
    (_ : ∀ x ∈ I.boundary M ∩ U, f x = 0), 0 < d% f p v

lemma modelWithCornersEuclideanHalfSpace_apply {p : EuclideanHalfSpace n} : (𝓡∂ n) p = p.val :=
  rfl

lemma modelWithCornersEuclideanHalfSpace_symm_apply {p : EuclideanSpace ℝ (Fin n)} : (𝓡∂ n).symm p =
    ⟨WithLp.toLp 2 (update p 0 (max (p 0) 0)), by simp⟩ :=
  rfl

lemma modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff {p : EuclideanHalfSpace n} :
    (𝓡∂ n).IsBoundaryPoint p ↔ ((𝓡∂ n) p).ofLp 0 = 0 := by
  simp [ModelWithCorners.isBoundaryPoint_iff, range_modelWithCornersEuclideanHalfSpace n,
    modelWithCornersEuclideanHalfSpace_apply, eq_comm]

lemma ModelWithCorners.IsBoundaryPoint.eq_zero_of_modelWithCornersEuclideanHalfSpace
    {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) : ((𝓡∂ n) p).ofLp 0 = 0 :=
  modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.mp hp

lemma modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint {p : EuclideanHalfSpace n}
    : (𝓡∂ n).symm ((𝓡∂ n) p) = p := by
  simp

lemma modelWithCornersEuclideanHalfSpace_boundary_eq :
    (𝓡∂ n).boundary (EuclideanHalfSpace n) = {p | ((𝓡∂ n) p).ofLp 0 = 0} := by
  simp_rw [← modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff]
  rfl

lemma modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff {p : EuclideanHalfSpace n} :
    (𝓡∂ n).IsInteriorPoint p ↔ ((𝓡∂ n) p).ofLp 0 > 0 := by
  simp [ModelWithCorners.isInteriorPoint_iff, range_modelWithCornersEuclideanHalfSpace n,
    modelWithCornersEuclideanHalfSpace_apply]

lemma modelWithCornersEuclideanHalfSpace_interior_eq :
    (𝓡∂ n).interior (EuclideanHalfSpace n) = {p | 0 < ((𝓡∂ n) p).ofLp 0} := by
  simp_rw [← modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff]
  rfl

#check ModelWithCorners.hasMFDerivAt

lemma modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) :
    HasMFDerivAt[{ x : EuclideanSpace ℝ (Fin n) | 0 ≤ x 0 }] (𝓡∂ n).symm
      ((𝓡∂ n) p)
      -- this line below isn't type correct at all
      -- I think writing this as the derivative of the model with corners is already the only
      -- sensible way to write this
      -- why is this okay for `ModelWithCorners.hasMFDerivAt`?
      (ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) ((𝓡∂ n) p))) := by
  refine ⟨(𝓡∂ n).continuousOn_symm.continuousWithinAt
    (by simp [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace]), ?_⟩
  apply HasFDerivWithinAt.congr (f := id)
  · apply HasFDerivAt.hasFDerivWithinAt
    exact hasFDerivAt_id p.val
  · intro x hx
    simp_all [modelWithCornersEuclideanHalfSpace_symm_apply,
      modelWithCornersEuclideanHalfSpace_apply]
  · rw [modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff] at hp
    have : (update ((𝓡∂ n) p).ofLp 0 0) = ((𝓡∂ n) p).ofLp := by
      rw [update_eq_self_iff, hp]
    simp [modelWithCornersEuclideanHalfSpace_symm_apply,
      hp, this]
    rfl

lemma modelWithCornersEuclideanHalfSpace_symm_mDifferentialbleWithinAt {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) :
    MDiffAt[{ x : EuclideanSpace ℝ (Fin n) | 0 ≤ x 0 }] (𝓡∂ n).symm p.val :=
  HasMFDerivWithinAt.mdifferentiableWithinAt
    (modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt hp)

section

variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type u_4}
  [TopologicalSpace M] [ChartedSpace H M] {F : Type u_8} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : M → F) (x : M) {s t : Set M}

theorem mvfderivWithin_subset (st : s ⊆ t) (hs : UniqueMDiffAt[s] x) (h : MDiffAt[t] f x) :
    d[s] f x = d[t] f x :=
  mfderivWithin_subset st hs h

theorem mvfderivWithin_inter (ht : t ∈ 𝓝 x) : d[s ∩ t] f x = d[s] f x :=
  mfderivWithin_inter ht

theorem mvfderivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : d[s] f x = d% f x :=
  mfderivWithin_of_mem_nhds h

lemma mvfderivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) : d[s] f x = d% f x :=
  mfderivWithin_of_isOpen hs hx

end

set_option backward.isDefEq.respectTransparency false in
lemma prop541euclideanTry5Local {p : EuclideanHalfSpace n} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5Local v ↔ 0 < ((d% (𝓡∂ n) p) v).ofLp 0 := by
  constructor
  · intro ⟨f, U, hU, hUp, hf1, hf2, hf3, hf4⟩
    by_contra! hv
    let x := (mfderiv% (𝓡∂ n) p) v
    let y := (d% (𝓡∂ n) p) v
    let V := (↑(𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) ⁻¹' U
    have hV : IsOpen V := by
      apply Continuous.isOpen_preimage ?_ U hU
      exact (ModelWithCorners.continuous_symm (𝓡∂ n)).comp (by fun_prop)
    have hV0 : 0 ∈ V := by
      simp [V, hUp]
    have yay1 : d[Ici (0 : ℝ) ∩ V] (f ∘ (𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 1 < 0 := by
      unfold mvfderivWithin
      have h1 :  MDiffAt[U] f (((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0) := by
        simp only [comp_apply, zero_smul, sub_zero, ModelWithCorners.left_inv]
        exact (hf1 p hUp).mdifferentiableWithinAt (ne_of_beq_false rfl)
      have hh : MDiffAt[{x | 0 ≤ x.ofLp 0}] (𝓡∂ n).symm ((𝓡∂ n) p - (0 : ℝ) • y) := by
        simp only [zero_smul, sub_zero]
        exact modelWithCornersEuclideanHalfSpace_symm_mDifferentialbleWithinAt hp
      have h2'' : MDiffAt[Ici 0 ∩ V] (fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 := by
          refine DifferentiableWithinAt.mdifferentiableWithinAt ?_
          fun_prop
      have h2''' : Ici 0 ∩ V ⊆ (fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) ⁻¹' {x | 0 ≤ x.ofLp 0} := by
        intro x ⟨hx1, hx2⟩
        simp [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, y,
          mul_nonpos_of_nonneg_of_nonpos hx1 hv]
      have h2 : MDiffAt[Ici 0 ∩ V] ((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 :=
        hh.comp 0 h2'' h2'''
      have h3 : UniqueMDiffAt[Ici (0 : ℝ) ∩ V] 0 := by
        apply UniqueMDiffWithinAt.inter
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffWithinAt_Ici 0
        · exact hV.mem_nhds_iff.mpr hV0
      have h4 : (↑(𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 = p := by
        simp
      -- this rewrite below produces defeq issues because we're changing the precise presentation
      -- of the point in the tangent space. Even when removing this def-eq issue, we still
      -- get a def-eq issue where the lemma applies both functions  individually but we need them
      -- applied as a composition
      rw [mfderivWithin_comp (s := Ici (0 : ℝ) ∩ V) (g := f)
        (f := (𝓡∂ n).symm ∘ fun i ↦ (𝓡∂ n) p - i • y) (x := 0) h1 h2 inter_subset_right h3]
      simp only [comp_apply]
      rw [zero_smul, sub_zero, ModelWithCorners.left_inv]
      rw [← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_apply]
      suffices h : (mfderiv[Ici (0 : ℝ) ∩ V]
        ((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0) 1 = -v by
        have : d[U] f p (-v) < 0 := by simp [mvfderivWithin_of_isOpen _ f p hU hUp, hf4]
        exact h ▸ this
      rw [mfderivWithin_comp 0 hh h2'' h2''' h3]
      rw [zero_smul ℝ y]
      rw [sub_zero]
      rw [HasMFDerivWithinAt.mfderivWithin
        (modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt hp)]
      · simp only [comp_apply, mfderivWithin_eq_fderivWithin, ContinuousLinearMap.id_comp]
        change (fderivWithin ℝ (fun (i : ℝ) ↦ p.val - i • y) (Ici 0 ∩ V) 0) 1 = -v
        rw [fderivWithin_derivWithin (𝕜 := ℝ) (f := fun (i : ℝ) ↦ p.val - i • y) (s := Ici 0 ∩ V)]
        rw [derivWithin_const_sub]
        rw [derivWithin_smul_const differentiableWithinAt_fun_id y]
        rw [derivWithin_id' 0 (Ici 0 ∩ V) h3.uniqueDiffWithinAt]
        simp only [mvfderiv, (𝓡∂ n).hasMFDerivAt.mfderiv (x := p), ContinuousLinearMap.comp_id,
          ContinuousLinearEquiv.coe_coe, one_smul, neg_inj, y]
        rfl
      rw [← range_modelWithCornersEuclideanHalfSpace n]
      exact (𝓡∂ n).uniqueMDiffOn _ (mem_range_self p)
    unfold mvfderivWithin at yay1
    simp only [comp_apply, mfderivWithin_eq_fderivWithin, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] at yay1
    rw [zero_smul, sub_zero] at yay1
    -- this is major def-eq abuse caused by `mfderiv_eq_fderiv`
    simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk] at yay1
    -- this uses the assumptions hv and hf3
    have yay2 : 0 ≤ (fderivWithin ℝ (f ∘ ↑(𝓡∂ n).symm ∘ fun i ↦ (𝓡∂ n) p - i • y)
        (Ici 0 ∩ V) 0) 1 := by
      apply IsLocalMinOn.fderivWithin_nonneg
      · apply IsMinOn.localize
        intro x ⟨hx1, hx2⟩
        simp only [comp_apply, zero_smul, sub_zero, ModelWithCorners.left_inv, hf3 p ⟨hp, hUp⟩,
          mem_setOf_eq]
        by_cases! hx' : x = 0 ∨ ((d% (𝓡∂ n) p) v).ofLp 0 = 0
        · rcases hx' with h1 | h2
          · simp only [h1, zero_smul, sub_zero, ModelWithCorners.left_inv]
            apply ge_of_eq
            apply hf3
            simp [modelWithCornersEuclideanHalfSpace_boundary_eq,
              hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, hUp]
          · apply ge_of_eq
            apply hf3
            simp only [modelWithCornersEuclideanHalfSpace_boundary_eq, mem_inter_iff, mem_setOf_eq,
              y]
            rw [ModelWithCorners.right_inv]
            · simpa [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, h2, V] using hx2
            · simp [range_modelWithCornersEuclideanHalfSpace n,
                hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, h2]
        · apply le_of_lt
          apply hf2
          simp only [modelWithCornersEuclideanHalfSpace_interior_eq, mem_inter_iff, mem_setOf_eq]
          rw [ModelWithCorners.right_inv]
          · simp only [PiLp.sub_apply, hp.eq_zero_of_modelWithCornersEuclideanHalfSpace,
              PiLp.smul_apply, smul_eq_mul, zero_sub, Left.neg_pos_iff, y]
            refine ⟨?_, by simpa [V] using hx2⟩
            exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hx1 hx'.1.symm) (lt_of_le_of_ne hv hx'.2)
          · simp only [range_modelWithCornersEuclideanHalfSpace n, mem_setOf_eq, PiLp.sub_apply,
              hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, PiLp.smul_apply, smul_eq_mul,
              zero_sub, Left.nonneg_neg_iff, y]
            apply le_of_lt
            exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hx1 hx'.1.symm) (lt_of_le_of_ne hv hx'.2)
      · simp only [one_mem_posTangentConeAt_iff_mem_closure, ← inter_assoc,
          inter_eq_self_of_subset_left Ioi_subset_Ici_self]
        apply hV.closure_inter
        simp [hV0]
    exact not_lt_of_ge yay2 yay1
  · intro h
    have h1 : ∀ x ∈ (𝓡∂ n).interior (EuclideanHalfSpace n), 0 < (proj 0 ∘ 𝓡∂ n) x := by
      intro x hx
      simpa [modelWithCornersEuclideanHalfSpace_apply,
        modelWithCornersEuclideanHalfSpace_interior_eq] using hx
    have h2 : ∀ x ∈ (𝓡∂ n).boundary (EuclideanHalfSpace n), (proj 0 ∘ 𝓡∂ n) x = 0 := by
      intro x hx
      simpa [modelWithCornersEuclideanHalfSpace_apply,
        modelWithCornersEuclideanHalfSpace_boundary_eq] using hx
    use proj 0 ∘ 𝓡∂ n, univ, isOpen_univ, mem_univ p,
      (ContDiff.comp_contMDiff (by fun_prop) (𝓡∂ n).contMDiff).contMDiffOn
    simp only [inter_univ]
    refine ⟨h1, h2, ?_⟩
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
    have yay1 : d[Ici (0 : ℝ)] (f ∘ (𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 1 < 0 := by
      unfold mvfderivWithin
      have h1 :  MDiffAt f p := hf1.mdifferentiableAt (ne_of_beq_false rfl)
      have hh : MDiffAt[{x | 0 ≤ x.ofLp 0}] (𝓡∂ n).symm ((𝓡∂ n) p - (0 : ℝ) • y) := by
        simp only [zero_smul, sub_zero]
        exact modelWithCornersEuclideanHalfSpace_symm_mDifferentialbleWithinAt hp
      have h2'' : MDiffAt[Ici 0] (fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 := by
          refine DifferentiableWithinAt.mdifferentiableWithinAt ?_
          fun_prop
      have h2''' : Ici 0 ⊆ (fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) ⁻¹' {x | 0 ≤ x.ofLp 0} := by
        intro x hx
        simp [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, y,
          mul_nonpos_of_nonneg_of_nonpos hx hv]
      have h2 : MDiffAt[Ici 0] ((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 :=
        hh.comp 0 h2'' h2'''
      have h3 : UniqueMDiffAt[Ici (0 : ℝ)] 0 := by
        rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
        exact uniqueDiffWithinAt_Ici 0
      have h4 : (↑(𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 = p := by
        simp
      -- this rewrite below produces defeq issues because we're changing the precise presentation
      -- of the point in the tangent space. Even when removing this def-eq issue, we still
      -- get a def-eq issue where the lemma applies both functions  individually but we need them
      -- applied as a composition
      rw [mfderiv_comp_mfderivWithin_of_eq h1 h2 h3 h4]
      simp only [comp_apply]
      rw [zero_smul, sub_zero, ModelWithCorners.left_inv]
      rw [← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_apply]
      suffices h : (mfderiv[Ici (0 : ℝ)] ((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0) 1 = -v by
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
      exact (𝓡∂ n).uniqueMDiffOn _ (mem_range_self p)
    unfold mvfderivWithin at yay1
    simp only [comp_apply, mfderivWithin_eq_fderivWithin, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] at yay1
    rw [zero_smul, sub_zero] at yay1
    -- this is major def-eq abuse caused by `mfderiv_eq_fderiv`
    simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk] at yay1
    -- this uses the assumptions hv and hf3
    have yay2 : 0 ≤ (fderivWithin ℝ (f ∘ ↑(𝓡∂ n).symm ∘ fun i ↦ (𝓡∂ n) p - i • y)
        (Ici (0 : ℝ)) 0) 1 := by
      apply IsLocalMinOn.fderivWithin_nonneg
      · apply IsMinOn.localize
        intro x hx
        simp only [comp_apply, zero_smul, sub_zero, ModelWithCorners.left_inv, hf3 p hp,
          mem_setOf_eq]
        by_cases! hx' : x = 0 ∨ ((d% (𝓡∂ n) p) v).ofLp 0 = 0
        · rcases hx' with h1 | h2
          · simp only [h1, zero_smul, sub_zero, ModelWithCorners.left_inv]
            apply ge_of_eq
            apply hf3
            simp [modelWithCornersEuclideanHalfSpace_boundary_eq,
              hp.eq_zero_of_modelWithCornersEuclideanHalfSpace]
          · apply ge_of_eq
            apply hf3
            simp only [modelWithCornersEuclideanHalfSpace_boundary_eq, mem_setOf_eq, y]
            rw [ModelWithCorners.right_inv]
            · simp [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, h2]
            · simp [range_modelWithCornersEuclideanHalfSpace n,
                hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, h2]
        · apply le_of_lt
          apply hf2
          simp only [modelWithCornersEuclideanHalfSpace_interior_eq, mem_setOf_eq]
          rw [ModelWithCorners.right_inv]
          · simp only [PiLp.sub_apply, hp.eq_zero_of_modelWithCornersEuclideanHalfSpace,
              PiLp.smul_apply, smul_eq_mul, zero_sub, Left.neg_pos_iff, y]
            exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hx hx'.1.symm) (lt_of_le_of_ne hv hx'.2)
          · simp only [range_modelWithCornersEuclideanHalfSpace n, mem_setOf_eq, PiLp.sub_apply,
              hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, PiLp.smul_apply, smul_eq_mul,
              zero_sub, Left.nonneg_neg_iff, y]
            apply le_of_lt
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

def Manifold.PartialDiffeomorphOfMaximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) : PartialDiffeomorph I I M H ∞ where
  toPartialEquiv := f.toPartialEquiv
  open_source := f.open_source
  open_target := f.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hf
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hf

omit [IsManifold I ∞ M] in
lemma Manifold.localDiffeomorphOn_of_mem_maximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) : IsLocalDiffeomorphOn I I ∞ f f.source:= by
  intro x
  apply (Manifold.PartialDiffeomorphOfMaximalAtlas hf).isLocalDiffeomorphAt
  simp

lemma prop541general_part1 {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : IsInwardPointingTry5 v)
    (f : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (hpf : p ∈ f.source) (hf : f ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M) :
    0 < (d% (𝓡∂ n) (f p) (mfderiv (𝓡∂ n) _ f p v)).ofLp 0 := by


  rw [← prop541euclideanTry5]
  · obtain ⟨g, hg1, hg2, hg3, hg4⟩ := hv
    unfold IsInwardPointingTry5
    use g ∘ f.symm
    refine ⟨?_, ?_⟩
    ·
      sorry
    · sorry
  · rw [← ((Manifold.localDiffeomorphOn_of_mem_maximalAtlas hf) ⟨p, hpf⟩).isBoundaryPoint_iff
      (ne_of_beq_false rfl)]
    exact hp

lemma prop541general {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5 v ↔ ∀ (f) (hf : f ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M),
      0 < (d% (𝓡∂ n) (f p) (mfderiv (𝓡∂ n) _ f p v)).ofLp 0 := by
  sorry

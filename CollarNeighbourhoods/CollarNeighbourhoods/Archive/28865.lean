module

public import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.ContMDiff.Defs

open scoped Topology ContDiff
open Function Set

public noncomputable section

namespace Manifold

-- We manually name the universe of `E''` as `IsImmersionAt` will use it.
universe u
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E''' : Type*} {E'' : Type u} {F F' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

variable {f g : M → N} {x : M}

namespace IsImmersionAtOfComplement

/-- Let `f : M → N` be a function, and suppose `φ : N → P` is a `C^n` immersion at `f x`, such
that `φ ∘ f` is `C^n` at `x`. Let `x ∈ t ⊆ M` be contained in the slice chart at `f x`.
Then `f` seen in the slice chart at `φ (f x)` and the preferred chart at `x`
is `C^n` at (the image of) `x` within (the image of) `t`. -/
private lemma aux {f : M → N} {φ : N → N'}
    (h : IsImmersionAtOfComplement F J J' n φ (f x)) (h' : CMDiffAt n (φ ∘ f) x)
    {t : Set M} (ht : t ⊆ f ⁻¹' h.domChart.source) (hxt : x ∈ t) :
    ContDiffWithinAt 𝕜 n ((h.domChart.extend J) ∘ f ∘ (extChartAt I x).symm)
      ((extChartAt I x).symm ⁻¹' t ∩ range I) ((extChartAt I x) x) := by
  -- Consider the local expressions of `f`, `φ`, `x` and `s'` in the charts we're considering.
  set f' := (h.domChart.extend J) ∘ f ∘ (extChartAt I x).symm
  set φ' := (h.codChart.extend J') ∘ φ ∘ (h.domChart.extend J).symm
  set x' := (extChartAt I x) x
  set s := (extChartAt I x).symm ⁻¹' t ∩ range I
  have hx' : extChartAt I x x ∈ s := ⟨by simp [mem_chart_source H x, hxt], mem_range_self _⟩
  have h'loc : ContDiffWithinAt 𝕜 n ((h.codChart.extend J') ∘ (φ ∘ f) ∘ (extChartAt I x).symm)
      ((extChartAt I x).symm ⁻¹' t ∩ range I) (extChartAt I x x) := by
    replace h' : CMDiffAt[t] n (φ ∘ f) x := h'.contMDiffWithinAt
    rw [contMDiffWithinAt_iff_of_mem_maximalAtlas' h.codChart_mem_maximalAtlas] at h'
    exacts [h'.2, h.mem_codChart_source]
  -- By hypothesis, `φ ∘ f` (read in our charts) is `C^n` at `x'` within `s`.
  have h'' : ContDiffWithinAt 𝕜 n (φ' ∘ f') s x' := by
    apply h'loc.congr_of_mem (fun y hy ↦ ?_) hx'
    simp only [mfld_simps, φ', f']
    rw [h.domChart.left_inv]
    apply ht hy.1
  -- On the other hand, composing `f'` with the inclusion `u ↦ (u, 0)` is also `C^n`
  -- (as a composition of `C^n` functions); this locally equals `φ ∘ f` in coordinates
  -- (since `f` is an immersion).
  set f'' := (h.equiv ∘ fun x ↦ (x, 0)) ∘ f'
  have h''' : ContDiffWithinAt 𝕜 n f'' s x' := by
    refine h''.congr_of_mem (fun y hy ↦ ?_) hx'
    simp only [f'', φ', f']
    nth_rw 2 [comp_apply]
    rw [Function.comp_apply, h.writtenInCharts]
    rw [h.domChart.extend_target_eq_image_source]
    exact ⟨(f ∘ (extChartAt I x).symm) y, ht hy.1, by simp⟩
  -- Composing with a suitable projection to cancel the inclusion, we deduce that `f` is `C^n`.
  have h'''' : ContDiffWithinAt 𝕜 n ((Prod.fst ∘ h.equiv.symm) ∘ f'') s x' := by
    refine ContDiffWithinAt.comp x' ?_ h''' (mapsTo_univ _ _)
    rw [contDiffWithinAt_univ]
    exact contDiffAt_fst.comp _ h.equiv.symm.contDiff.contDiffAt
  exact h''''.congr_of_mem (fun y hy ↦ by simp [f'']) hx'

/-- A function `f : M → N` between `C^n` manifolds is `C^n` at `x` if and only if it is continuous
at `x` and its composition `φ ∘ f` with a `C^n` immersion `φ : N → P` at `f x` is `C^n` at `x`. -/
lemma _root_.ContMDiffAt.iff_comp_isImmersionAtOfComplement
    {f : M → N} {φ : N → N'} (hφ : IsImmersionAtOfComplement F J J' n φ (f x)) :
    -- Note: `φ` need not be inducing, so continuity of `φ ∘ f` at `x`
    -- generally does not imply continuity of `f`
    CMDiffAt n f x ↔ ContinuousAt f x ∧ CMDiffAt n (φ ∘ f) x := by
  refine ⟨fun hf ↦ ⟨hf.continuousAt, hφ.contMDiffAt.comp x hf⟩, fun ⟨hf, h'⟩ ↦ ?_⟩
  -- Since `f` is continuous at `x`, some neighbourhood `t` of `x` is mapped
  -- into `hφ.domChart.source` under `f`. By restriction, we may assume `t` is open,
  -- so it suffices to test smoothness on `t`.
  have : hφ.domChart.source ∈ 𝓝 (f x) := hφ.domChart.open_source.mem_nhds hφ.mem_domChart_source
  obtain ⟨t, ht, htopen, hxt⟩ := mem_nhds_iff.mp (hf this)
  suffices CMDiffAt[t] n f x from this.contMDiffAt <| htopen.mem_nhds hxt
  -- We test smoothness of `f` on `t` in the preferred chart at `x` and `hφ.codChart`.
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas'
    hφ.domChart_mem_maximalAtlas hφ.mem_domChart_source]
  refine ⟨hf.continuousWithinAt, ?_⟩
  exact aux hφ h' ht hxt

end IsImmersionAtOfComplement

end Manifold

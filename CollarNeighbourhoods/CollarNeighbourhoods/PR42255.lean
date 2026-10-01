module

public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.LocallyConvex.Bounded

/-! https://github.com/leanprover-community/mathlib4/pull/42255-/

@[expose] public section


open Set

variable {ι : Sort*} {𝕜 E : Type*}

section Topology
open Bornology Filter
open scoped Pointwise Topology

variable [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [CompactIccSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] {s t : Set E}

/-- The convex join of a compact closed set and a closed von Neumann bounded set is closed. -/
theorem IsCompact.isClosed_convexJoin (hs : IsCompact s) (hs' : IsClosed s) (ht : IsClosed t)
    (htb : IsVonNBounded 𝕜 t) : IsClosed (convexJoin 𝕜 s t) := by
  rcases t.eq_empty_or_nonempty with rfl | ht₀
  · simp
  -- Parametrise the join by `Φ (θ, a, b) = (1 - θ) • a + θ • b` over `S = [0, 1] ×ˢ s ×ˢ t`.
  set Φ : 𝕜 × E × E → E := fun p ↦ (1 - p.1) • p.2.1 + p.1 • p.2.2 with hΦ
  set S : Set (𝕜 × E × E) := Icc 0 1 ×ˢ s ×ˢ t
  have himg : convexJoin 𝕜 s t ⊆ Φ '' S := fun y hy ↦ by
    obtain ⟨a, ha, b, hb, p, q, hp, hq, hpq, rfl⟩ := mem_convexJoin.1 hy
    exact ⟨(q, a, b), ⟨⟨hq, by linarith⟩, ha, hb⟩, by simp [hΦ, show (1 : 𝕜) - q = p by linarith]⟩
  rw [isClosed_iff_forall_filter]
  intro x F hF hFs hFx
  -- Lift a filter converging to `x` inside the join to an ultrafilter on the parameter space.
  have : (comap Φ F ⊓ 𝓟 S).NeBot :=
    comap_inf_principal_neBot_of_image_mem hF (mem_of_superset (le_principal_iff.1 hFs) himg)
  obtain ⟨u, hu⟩ := Ultrafilter.exists_le (comap Φ F ⊓ 𝓟 S)
  have hSu : S ∈ u := le_principal_iff.1 (hu.trans inf_le_right)
  have hΦu : Tendsto Φ ↑u (𝓝 x) :=
    ((map_mono (hu.trans inf_le_left)).trans map_comap_le).trans hFx
  -- Compactness of `[0, 1]` and of `s` makes the first two parameters converge along `u`.
  obtain ⟨θ, hθ, hθu⟩ : ∃ θ ∈ Icc (0 : 𝕜) 1, Tendsto (fun p : 𝕜 × E × E ↦ p.1) ↑u (𝓝 θ) :=
    isCompact_Icc.ultrafilter_le_nhds' (u.map fun p : 𝕜 × E × E ↦ p.1)
      (Ultrafilter.mem_map.2 <| by filter_upwards [hSu] with p hp using hp.1)
  obtain ⟨a, ha, hau⟩ : ∃ a ∈ s, Tendsto (fun p : 𝕜 × E × E ↦ p.2.1) ↑u (𝓝 a) :=
    hs.ultrafilter_le_nhds' (u.map fun p : 𝕜 × E × E ↦ p.2.1)
      (Ultrafilter.mem_map.2 <| by filter_upwards [hSu] with p hp using hp.2.1)
  rcases eq_or_ne θ 0 with rfl | hθ₀
  · -- If `θ → 0`, boundedness crushes the third parameter and `x` is a limit of points of `s`.
    have hbdd : Tendsto (fun p : 𝕜 × E × E ↦ p.1 • (p.2.2 - p.2.1)) ↑u (𝓝 0) :=
      (htb.sub (hs.isVonNBounded 𝕜)).smul_tendsto_zero
        (by filter_upwards [hSu] with p hp using sub_mem_sub hp.2.2 hp.2.1) hθu
    have h : Tendsto (fun p : 𝕜 × E × E ↦ p.2.1) ↑u (𝓝 x) := sub_zero x ▸
      (hΦu.sub hbdd).congr fun p ↦ by simp only [hΦ, sub_smul, smul_sub, one_smul]; abel
    exact subset_convexJoin_left ht₀
      (hs'.mem_of_tendsto h (by filter_upwards [hSu] with p hp using hp.2.1))
  · -- Otherwise the third parameter converges to `θ⁻¹ • (x - (1 - θ) • a)`, which lies in `t`.
    have hb : Tendsto (fun p : 𝕜 × E × E ↦ p.2.2) ↑u (𝓝 (θ⁻¹ • (x - (1 - θ) • a))) := by
      refine Tendsto.congr' ?_
        ((hθu.inv₀ hθ₀).smul (hΦu.sub ((tendsto_const_nhds.sub hθu).smul hau)))
      filter_upwards [hθu.eventually_ne hθ₀] with p hp
      simp [hΦ, inv_smul_smul₀ hp]
    have hbt := ht.mem_of_tendsto hb (by filter_upwards [hSu] with p hp using hp.2.2)
    rw [show x = (1 - θ) • a + θ • (θ⁻¹ • (x - (1 - θ) • a)) by rw [smul_inv_smul₀ hθ₀]; abel]
    exact segment_subset_convexJoin ha hbt ⟨1 - θ, θ, sub_nonneg.2 hθ.2, hθ.1, by ring, rfl⟩

/-- The convex hull of the union of a compact convex set and a closed von Neumann bounded convex
set is closed. -/
theorem IsCompact.isClosed_convexHull_union [T2Space E] (hs : IsCompact s) (hs' : Convex 𝕜 s)
    (ht : IsClosed t) (ht' : Convex 𝕜 t) (htb : IsVonNBounded 𝕜 t) :
    IsClosed (convexHull 𝕜 (s ∪ t)) := by
  rcases s.eq_empty_or_nonempty with rfl | hs₀
  · simpa [ht'.convexHull_eq] using ht
  rcases t.eq_empty_or_nonempty with rfl | ht₀
  · simpa [hs'.convexHull_eq] using hs.isClosed
  exact hs'.convexHull_union ht' hs₀ ht₀ ▸ hs.isClosed_convexJoin hs.isClosed ht htb

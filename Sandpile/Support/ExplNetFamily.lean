import LatticeProb.Prob.NetApprox
import Mathlib.Topology.MetricSpace.Basic

/-!
# A finite net of continuous functions approximating tightly oscillating fields

`Sandpile.stability_uniform_of_finite` turns a stability threshold depending on a finite
family of rewards, an accuracy, a uniform bound, and a compact set into one threshold valid
for the whole finite family, so a tight random field need only be shown close to one member of
a fixed finite family. `exists_finite_family_of_compact` builds that family from a single pair
`(δ, η)`: a uniform bound `M` and oscillation `η` at scale `δ` on a compact set `K` already
place any such function within `2η` of one of finitely many continuous functions, built as the
tent interpolation `regApprox` over a `δ/2`-net of `K` with values in the finite grid
`η ℤ ∩ [-M-η, M+η]`. Keeping the interpolation's denominator away from zero with `max _ (δ/2)`
makes every member of the family continuous on all of `E`, not merely on `K`, and
`exists_near_family_of_not_bad` reads the two hypotheses of the family off the two negated
events of the tightness clause it replaces.
-/

open Finset

namespace Sandpile

variable {E : Type*} [PseudoMetricSpace E]

/-- The tent interpolation with its denominator kept away from zero, so that it is
continuous on the whole space and not only where the net reaches. -/
noncomputable def regApprox {m : ℕ} (x : Fin m → E) (η s₀ : ℝ) (u : Fin m → ℝ) (y : E) : ℝ :=
  (∑ k, LatticeProb.tentWeight η (x k) y * u k) / max (LatticeProb.tentSum x η y) s₀

/-- The regularized interpolation is continuous everywhere. -/
theorem continuous_regApprox {m : ℕ} (x : Fin m → E) (η s₀ : ℝ) (hs₀ : 0 < s₀)
    (u : Fin m → ℝ) : Continuous (regApprox x η s₀ u) := by
  have hw : ∀ k : Fin m, Continuous fun y : E => LatticeProb.tentWeight η (x k) y := by
    intro k
    unfold LatticeProb.tentWeight
    fun_prop
  have hnum : Continuous fun y : E => ∑ k, LatticeProb.tentWeight η (x k) y * u k :=
    continuous_finsetSum _ fun k _ => (hw k).mul continuous_const
  have hden : Continuous fun y : E => max (LatticeProb.tentSum x η y) s₀ := by
    have hts : Continuous fun y : E => LatticeProb.tentSum x η y := by
      unfold LatticeProb.tentSum
      exact continuous_finsetSum _ fun k _ => hw k
    exact hts.max continuous_const
  refine hnum.div hden ?_
  intro y
  exact ne_of_gt (lt_of_lt_of_le hs₀ (le_max_right _ _))

/-- The regularized interpolation inherits a bound on the interpolated values. -/
theorem abs_regApprox_le {m : ℕ} (x : Fin m → E) (η s₀ : ℝ) (hs₀ : 0 < s₀)
    (u : Fin m → ℝ) (B : ℝ) (hB : 0 ≤ B) (hu : ∀ k, |u k| ≤ B) (y : E) :
    |regApprox x η s₀ u y| ≤ B := by
  have hden : 0 < max (LatticeProb.tentSum x η y) s₀ := lt_of_lt_of_le hs₀ (le_max_right _ _)
  have hnum : |∑ k, LatticeProb.tentWeight η (x k) y * u k|
      ≤ LatticeProb.tentSum x η y * B := by
    calc |∑ k, LatticeProb.tentWeight η (x k) y * u k|
        ≤ ∑ k, |LatticeProb.tentWeight η (x k) y * u k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, LatticeProb.tentWeight η (x k) y * B := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_of_nonneg (LatticeProb.tentWeight_nonneg η (x k) y)]
          exact mul_le_mul_of_nonneg_left (hu k) (LatticeProb.tentWeight_nonneg η (x k) y)
      _ = LatticeProb.tentSum x η y * B := by
          rw [← Finset.sum_mul]
          rfl
  rw [regApprox, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hle : LatticeProb.tentSum x η y ≤ max (LatticeProb.tentSum x η y) s₀ := le_max_left _ _
  nlinarith

/-- Where the net reaches, the regularization changes nothing. -/
theorem regApprox_eq_netApprox {m : ℕ} (x : Fin m → E) (η s₀ : ℝ) (u : Fin m → ℝ) (y : E)
    (h : s₀ ≤ LatticeProb.tentSum x η y) :
    regApprox x η s₀ u y = LatticeProb.netApprox x η u y := by
  rw [regApprox, LatticeProb.netApprox_eq_div, max_eq_left h]

/-- A net point within `η - s₀` forces the tent denominator above `s₀`. -/
theorem le_tentSum_of_dist {m : ℕ} {x : Fin m → E} {η s₀ : ℝ} {y : E} {k : Fin m}
    (hk : dist (x k) y ≤ η - s₀) : s₀ ≤ LatticeProb.tentSum x η y := by
  have hterm : s₀ ≤ LatticeProb.tentWeight η (x k) y := by
    unfold LatticeProb.tentWeight
    exact le_max_of_le_right (by linarith)
  refine le_trans hterm ?_
  unfold LatticeProb.tentSum
  exact Finset.single_le_sum (f := fun k => LatticeProb.tentWeight η (x k) y)
    (fun k _ => LatticeProb.tentWeight_nonneg η (x k) y) (Finset.mem_univ k)

/-- A point of `[-M,M]` is within `η` of a point of the grid `η(n - K₀)`, `0 ≤ n ≤ 2K₀`. -/
theorem exists_grid_index (η M : ℝ) (hη : 0 < η) (K₀ : ℕ) (hK₀ : M ≤ η * (K₀ : ℝ))
    (t : ℝ) (ht : |t| ≤ M) :
    ∃ n : ℕ, n ≤ 2 * K₀ ∧ |η * ((n : ℝ) - (K₀ : ℝ)) - t| ≤ η := by
  have habs := abs_le.1 ht
  have hs0 : (0 : ℝ) ≤ (t + η * (K₀ : ℝ)) / η := by
    apply div_nonneg _ hη.le
    linarith [habs.1]
  set s : ℝ := (t + η * (K₀ : ℝ)) / η with hs
  refine ⟨⌊s⌋₊, ?_, ?_⟩
  · have hle : s ≤ 2 * (K₀ : ℝ) := by
      rw [hs, div_le_iff₀ hη]
      linarith [habs.2]
    have hfl : (⌊s⌋₊ : ℝ) ≤ 2 * (K₀ : ℝ) := le_trans (Nat.floor_le hs0) hle
    have h2 : ((2 * K₀ : ℕ) : ℝ) = 2 * (K₀ : ℝ) := by push_cast; ring
    exact_mod_cast hfl.trans_eq h2.symm
  · have hlo : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le hs0
    have hhi : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
    have hts : t + η * (K₀ : ℝ) = η * s := by
      rw [hs]
      field_simp
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith

/-- **The finite family.**  On a compact set, a uniform bound `M` and a single pair `(δ, η)`
of an oscillation bound place every function within `2η`, uniformly on the set, of one of
finitely many functions continuous on the whole space and bounded by `M + η`. -/
theorem exists_finite_family_of_compact {K : Set E} (hK : IsCompact K)
    (M η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) (hM : 0 ≤ M) :
    ∃ (N : ℕ) (g : Fin N → E → ℝ),
      (∀ i, Continuous (g i)) ∧
      (∀ (i : Fin N) (y : E), |g i y| ≤ M + η) ∧
      ∀ v : E → ℝ, (∀ y ∈ K, |v y| ≤ M) →
        (∀ y ∈ K, ∀ z ∈ K, dist y z < δ → |v y - v z| ≤ η) →
        ∃ i, ∀ y ∈ K, |v y - g i y| ≤ 2 * η := by
  classical
  obtain ⟨m, x, hxK, hcov⟩ := LatticeProb.exists_net hK (by positivity : (0:ℝ) < δ / 2)
  set K₀ : ℕ := ⌈M / η⌉₊ with hK₀def
  have hK₀ : M ≤ η * (K₀ : ℝ) := by
    have hce : M / η ≤ (K₀ : ℝ) := Nat.le_ceil _
    have hmul : η * (M / η) ≤ η * (K₀ : ℝ) := mul_le_mul_of_nonneg_left hce hη.le
    calc M = η * (M / η) := by field_simp
      _ ≤ η * (K₀ : ℝ) := hmul
  have hK₀B : η * (K₀ : ℝ) ≤ M + η := by
    have hce : (K₀ : ℝ) ≤ M / η + 1 := by
      have := Nat.ceil_lt_add_one (a := M / η) (by positivity)
      linarith
    have hmul : η * (K₀ : ℝ) ≤ η * (M / η + 1) := mul_le_mul_of_nonneg_left hce hη.le
    have hsimp : η * (M / η + 1) = M + η := by field_simp
    linarith [hmul, hsimp.le, hsimp.ge]
  set val : Fin (2 * K₀ + 1) → ℝ := fun j => η * ((j : ℝ) - (K₀ : ℝ)) with hvaldef
  have hvalB : ∀ j : Fin (2 * K₀ + 1), |val j| ≤ M + η := by
    intro j
    have hj : (j : ℝ) ≤ 2 * (K₀ : ℝ) := by
      have := j.2
      have hcast : ((j : ℕ) : ℝ) ≤ ((2 * K₀ : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 j.2
      calc ((j : ℕ) : ℝ) ≤ ((2 * K₀ : ℕ) : ℝ) := hcast
        _ = 2 * (K₀ : ℝ) := by push_cast; ring
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    have hK₀0 : (0 : ℝ) ≤ (K₀ : ℝ) := Nat.cast_nonneg _
    rw [hvaldef, abs_le]
    constructor
    · nlinarith
    · nlinarith
  set G : (Fin m → Fin (2 * K₀ + 1)) → E → ℝ :=
    fun j => regApprox x δ (δ / 2) (fun k => val (j k)) with hGdef
  set e := Fintype.equivFin (Fin m → Fin (2 * K₀ + 1)) with hedef
  refine ⟨Fintype.card (Fin m → Fin (2 * K₀ + 1)), fun i => G (e.symm i), ?_, ?_, ?_⟩
  · intro i
    exact continuous_regApprox x δ (δ / 2) (by positivity) _
  · intro i y
    exact abs_regApprox_le x δ (δ / 2) (by positivity) _ (M + η) (by positivity)
      (fun k => hvalB _) y
  · intro v hvb hvm
    have hchoice : ∀ k : Fin m, ∃ n : ℕ, n ≤ 2 * K₀ ∧
        |η * ((n : ℝ) - (K₀ : ℝ)) - v (x k)| ≤ η :=
      fun k => exists_grid_index η M hη K₀ hK₀ (v (x k)) (hvb _ (hxK k))
    choose n hn hnv using hchoice
    set j : Fin m → Fin (2 * K₀ + 1) := fun k => ⟨n k, by have := hn k; omega⟩ with hjdef
    refine ⟨e j, ?_⟩
    intro y hy
    obtain ⟨k₀, hk₀⟩ := hcov y hy
    have hts : δ / 2 ≤ LatticeProb.tentSum x δ y :=
      le_tentSum_of_dist (k := k₀) (by linarith)
    have hpos : 0 < LatticeProb.tentSum x δ y := lt_of_lt_of_le (by positivity) hts
    have hnear : |LatticeProb.netApprox x δ (fun k => val (j k)) y - v y| ≤ 2 * η := by
      refine LatticeProb.abs_netApprox_sub_le hpos ?_
      intro k hk
      have h1 : |val (j k) - v (x k)| ≤ η := by
        simpa [hvaldef, hjdef] using hnv k
      have h2 : |v (x k) - v y| ≤ η := hvm _ (hxK k) _ hy hk
      calc |val (j k) - v y| ≤ |val (j k) - v (x k)| + |v (x k) - v y| := abs_sub_le _ _ _
        _ ≤ η + η := add_le_add h1 h2
        _ = 2 * η := by ring
    have hsymm : e.symm (e j) = j := e.symm_apply_apply j
    show |v y - G (e.symm (e j)) y| ≤ 2 * η
    rw [hsymm, hGdef]
    simp only
    rw [regApprox_eq_netApprox x δ (δ / 2) _ y hts, abs_sub_comm]
    exact hnear

/-- The two hypotheses of the family, read off the two events of the tightness clause of
`prop:dlt4-heat-potential-invariance` exactly as that clause writes them. -/
theorem exists_near_family_of_not_bad {K : Set E} (M η δ : ℝ) (N : ℕ) (g : Fin N → E → ℝ)
    (happ : ∀ v : E → ℝ, (∀ y ∈ K, |v y| ≤ M) →
      (∀ y ∈ K, ∀ z ∈ K, dist y z < δ → |v y - v z| ≤ η) →
      ∃ i, ∀ y ∈ K, |v y - g i y| ≤ 2 * η)
    (v : E → ℝ)
    (h1 : ¬ ∃ y ∈ K, M < |v y|)
    (h2 : ¬ ∃ y ∈ K, ∃ z ∈ K, dist y z < δ ∧ η < |v y - v z|) :
    ∃ i, ∀ y ∈ K, |v y - g i y| ≤ 2 * η := by
  push Not at h1 h2
  refine happ v (fun y hy => h1 y hy) ?_
  intro y hy z hz hd
  exact h2 y hy z hz hd

end Sandpile

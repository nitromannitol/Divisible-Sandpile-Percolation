import Sandpile.Support.Dgt4ABandWeights

/-!
# Band parameter choices for Step 1

The parameter choices in Step 1 of `thm:dgt4-many-limits`
(`sandpile.tex:5938-5951`). The exponent sequence has precisely `[1,2]` as
its set of subsequential limits. The extraction for each stopping exponent
is made independently of the horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

/-- The band parameters can be chosen with every exponent in `[1,2]` as a
subsequential limit, with all four numerical parameters prescribed. -/
theorem BandParameters.exists_recurrent
    (A c0 l1 lam0 : ℝ) (hA : 1 < A) (hc0 : 0 < c0)
    (hl1 : l1 ∈ Set.Ioo (0 : ℝ) 1) (hlam0 : 0 < lam0) :
    ∃ P : BandParameters, P.A = A ∧ P.c0 = c0 ∧ P.l1 = l1 ∧ P.lam0 = lam0 ∧
      (∀ θ : ℝ, θ ∈ Set.Icc (1 : ℝ) 2 ↔
        ∃ kl : ℕ → ℕ, StrictMono kl ∧ Tendsto (P.theta ∘ kl) atTop (𝓝 θ)) ∧
      (∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
        ∃ kl : ℕ → ℕ, StrictMono kl ∧
          Tendsto (fun n => 1 + 1 / P.theta (kl n)) atTop (𝓝 κ)) := by
  let I := Set.Icc (1 : ℝ) 2
  haveI : Nonempty I := ⟨⟨1, by norm_num [I]⟩⟩
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq I
  let u : ℕ → I := fun n => v (Nat.unpair n).1
  let P : BandParameters := ⟨A, c0, l1, lam0, fun n => (u n : ℝ),
    hA, hc0, hl1, hlam0, fun n => (u n).property⟩
  have hlim : ∀ θ : ℝ, θ ∈ I →
      ∃ kl : ℕ → ℕ, StrictMono kl ∧ Tendsto (P.theta ∘ kl) atTop (𝓝 θ) := by
    intro θ hθ
    have hc : MapClusterPt (⟨θ, hθ⟩ : I) atTop u := by
      apply mapClusterPt_iff_frequently.mpr
      intro s hs
      obtain ⟨j, hj⟩ := hv.mem_nhds hs
      apply frequently_atTop.mpr
      intro N
      refine ⟨Nat.pair j N, Nat.right_le_pair j N, ?_⟩
      simpa only [u, Nat.unpair_pair] using hj
    obtain ⟨kl, hkl, hconv⟩ := hc.tendsto_subseq
    exact ⟨kl, hkl, continuous_subtype_val.continuousAt.tendsto.comp hconv⟩
  refine ⟨P, rfl, rfl, rfl, rfl, fun θ => ⟨hlim θ, ?_⟩, ?_⟩
  · rintro ⟨kl, _, hkl⟩
    exact isClosed_Icc.mem_of_tendsto hkl (Eventually.of_forall fun n => P.htheta (kl n))
  · intro κ hκ
    have hk : 0 < κ - 1 := by linarith [hκ.1]
    have hθ : 1 / (κ - 1) ∈ I := by
      constructor
      · apply (le_div_iff₀ hk).mpr
        linarith [hκ.2]
      · apply (div_le_iff₀ hk).mpr
        linarith [hκ.1]
    obtain ⟨kl, hkl, ht⟩ := hlim (1 / (κ - 1)) hθ
    refine ⟨kl, hkl, ?_⟩
    have hc := ((tendsto_const_nhds (x := (1 : ℝ))).div ht (one_div_ne_zero hk.ne')).const_add 1
    simpa only [Pi.div_apply, Function.comp_def, one_div_one_div,
      show 1 + (κ - 1) = κ by ring] using hc

/-- The numerical choices and exponent sequence in Step 1 can be made
simultaneously, with positive mass left for the atom at zero. -/
theorem BandParameters.exists_admissible (l0 : ℝ) (hl0 : 0 < l0) (hl01 : l0 < 1) :
    ∃ P : BandParameters,
      l0 < P.l1 ∧ 1 / P.l1 < P.lam0 ∧ P.lam0 < 1 / l0 ∧
      1 / P.A < P.l1 ∧ 1 - P.lam0 * P.l1 + (P.lam0 - 1) / P.A < 0 ∧
      Summable P.weight ∧ (∑' k, P.weight k) < 1 ∧
      (∀ θ : ℝ, θ ∈ Set.Icc (1 : ℝ) 2 ↔
        ∃ kl : ℕ → ℕ, StrictMono kl ∧ Tendsto (P.theta ∘ kl) atTop (𝓝 θ)) ∧
      (∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
        ∃ kl : ℕ → ℕ, StrictMono kl ∧
          Tendsto (fun n => 1 + 1 / P.theta (kl n)) atTop (𝓝 κ)) := by
  obtain ⟨l1, hl0l1, hl11⟩ := exists_between hl01
  have hl1 : 0 < l1 := hl0.trans hl0l1
  have hinv : 1 / l1 < 1 / l0 := one_div_lt_one_div_of_lt hl0 hl0l1
  obtain ⟨lam, hlow, hhigh⟩ := exists_between hinv
  have hlam : 0 < lam := (one_div_pos.mpr hl1).trans hlow
  have hprod : 0 < lam * l1 - 1 := by
    have h := (div_lt_iff₀ hl1).mp hlow
    linarith
  obtain ⟨A, hA⟩ := exists_gt (max (max (1 : ℝ) (1 / l1)) ((lam - 1) / (lam * l1 - 1)))
  have hA1 : 1 < A := (le_max_left 1 (1 / l1)).trans_lt ((le_max_left _ _).trans_lt hA)
  have hAi : 1 / l1 < A := (le_max_right 1 (1 / l1)).trans_lt ((le_max_left _ _).trans_lt hA)
  have hAr : (lam - 1) / (lam * l1 - 1) < A := (le_max_right _ _).trans_lt hA
  have hA0 : 0 < A := zero_lt_one.trans hA1
  have hband : 1 / A < l1 := (div_lt_iff₀ hA0).mpr (by
    have h := (div_lt_iff₀ hl1).mp hAi
    nlinarith)
  have hparam : 1 - lam * l1 + (lam - 1) / A < 0 := by
    have h := (div_lt_iff₀ hprod).mp hAr
    have h' : (lam - 1) / A < lam * l1 - 1 := (div_lt_iff₀ hA0).mpr (by nlinarith)
    linarith
  let S : ℝ := ∑' k, Real.exp (-(A ^ k))
  have hS : 0 ≤ S := tsum_nonneg fun _ => Real.exp_nonneg _
  let c0 : ℝ := 1 / (2 * (S + 1))
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  obtain ⟨P, hPA, hPc, hPl, hPm, hθ, hκ⟩ :=
    BandParameters.exists_recurrent A c0 l1 lam hA1 hc0 ⟨hl1, hl11⟩ hlam
  refine ⟨P, by simpa only [hPl] using hl0l1,
    by simpa only [hPl, hPm] using hlow, by simpa only [hPm] using hhigh,
    by simpa only [hPA, hPl] using hband,
    by simpa only [hPA, hPl, hPm] using hparam, P.summable_weight, ?_, hθ, hκ⟩
  have he : (∑' k, P.weight k) = c0 * S := by
    simp only [BandParameters.weight, BandParameters.level, hPA, hPc]
    exact tsum_mul_left
  rw [he]
  dsimp [c0]
  rw [one_div_mul_eq_div]
  exact (div_lt_one (by positivity)).mpr (by linarith)

end Sandpile.Support

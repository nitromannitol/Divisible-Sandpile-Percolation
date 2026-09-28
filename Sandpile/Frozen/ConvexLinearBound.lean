import Sandpile.Support.ConvexLinear

/-! # Convex Linearization Bound

Lemma bounding a coordinatewise convex function by its linearization, of
sandpile.tex, frozen.  `sandpile.tex:1548-1570` (label `lem:convex-linear-bound`):

  "Let $\xi_1,\ldots,\xi_N$ be i.i.d. mean-zero variables with finite variance.
   Let $F$ be convex in each coordinate and suppose that, $\P$-almost surely,
   for every $1\leq i\leq N$, $0\leq\partial_i^+F\leq b_i$, where the $b_i$ are
   deterministic.  Then there is a universal $C<\infty$ such that, for every
   $L>0$,
   \[
     \E\left[\left(F-\E F-\sum_{i=1}^N\E[\partial_i^+F]\xi_i\right)^2\right]
     \leq CL^2\sum_{i=1}^N\Var(\partial_i^+F)+C\eta(L)\sum_{i=1}^Nb_i^2\, ,
   \]
   where, for an independent copy $\xi_1'$ of $\xi_1$,
   $\eta(L):=\E[(\xi_1-\xi_1')^2\one_{\{|\xi_1-\xi_1'|>L\}}]$."

Modelling.  The `N` i.i.d. coordinates are the product space `Fin N → ℝ` under
`Measure.pi fun _ => ν` for a one-site law `ν` with mean zero and finite second
moment.  The right partial derivative `∂_i^+F` is supplied as a function
`D : Fin N → (Fin N → ℝ) → ℝ` together with the hypothesis that `D i ξ` is the
derivative at `ξ i` of the one-variable section `y ↦ F (Function.update ξ i y)`
within `Set.Ici (ξ i)`, that is, the right derivative in coordinate `i`.  This
is preferred to writing `derivWithin` in the conclusion, because the paper uses
`∂_i^+F` as a genuine random variable whose mean and variance appear, and
`derivWithin` would take its junk value `0` at a point of non-differentiability
rather than the right derivative that convexity guarantees to exist.  The
hypothesis states existence, so no junk value is read.

`η(L)` is the iterated integral `truncatedGap ν L` over an independent pair,
which is the paper's `\E[(\xi_1-\xi_1')^2\one_{\{|\xi_1-\xi_1'|>L\}}]`.

Quantifier order.  `C` is universal, so it is bound before `N`, the law, `F`,
`D`, `b` and `L`.  The bound `0 ≤ ∂_i^+F ≤ b_i` is imposed almost surely, as in
the paper, and the `b_i` are deterministic, so `b` is a function of the index
alone.
-/

open MeasureTheory ProbabilityTheory Filter Topology

/-- `η(L) = E[(ξ - ξ')² 1{|ξ - ξ'| > L}]` for an independent pair of variables
with common law `ν`. -/
noncomputable def Sandpile.truncatedGap (ν : Measure ℝ) (L : ℝ) : ℝ :=
  ∫ y, ∫ z, (if L < |y - z| then (y - z) ^ 2 else 0) ∂ν ∂ν

set_option maxHeartbeats 1000000 in
-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.convex_linear_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        Integrable (fun z => z ^ 2) ν →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
        ∀ D : Fin N → (Fin N → ℝ) → ℝ, (∀ i, Measurable (D i)) →
          (∀ (i : Fin N) (ξ : Fin N → ℝ),
            ConvexOn ℝ (Set.univ : Set ℝ) fun y => F (Function.update ξ i y)) →
          (∀ (i : Fin N) (ξ : Fin N → ℝ),
            HasDerivWithinAt (fun y => F (Function.update ξ i y)) (D i ξ)
              (Set.Ici (ξ i)) (ξ i)) →
        ∀ b : Fin N → ℝ,
          (∀ᵐ ξ ∂(Measure.pi fun _ : Fin N => ν), ∀ i : Fin N, 0 ≤ D i ξ ∧ D i ξ ≤ b i) →
          ∀ L : ℝ, 0 < L →
            ∫ ξ, (F ξ - (∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)) -
                ∑ i, (∫ η, D i η ∂(Measure.pi fun _ : Fin N => ν)) * ξ i) ^ 2
                ∂(Measure.pi fun _ : Fin N => ν) ≤
              C * L ^ 2 * (∑ i, variance (D i) (Measure.pi fun _ : Fin N => ν)) +
                C * Sandpile.truncatedGap ν L * ∑ i, b i ^ 2
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨C₀, hC₀pos, hES⟩ := LatticeProb.exists_efron_stein_L2
  refine ⟨4 * C₀ + 1, by positivity, ?_⟩
  intro N ν hprob hmean hsq F hFm D hDm hconv hderiv b hDb L hL
  haveI := hprob
  set π : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => ν with hπ
  haveI : IsProbabilityMeasure π := by rw [hπ]; infer_instance
  set a : Fin N → ℝ := fun i => ∫ η, D i η ∂π with hadef
  set c : ℝ := ∫ η, F η ∂π with hcdef
  -- the right-hand side is nonnegative
  have hgap0 : 0 ≤ Sandpile.truncatedGap ν L :=
    integral_nonneg fun y => integral_nonneg fun z => by positivity
  have hvar0 : ∀ i, 0 ≤ variance (D i) π := fun i => variance_nonneg _ _
  have hb0 : ∀ i, 0 ≤ b i := by
    intro i
    obtain ⟨ξ, hξ⟩ := hDb.exists
    exact le_trans (hξ i).1 (hξ i).2
  have hRHS : 0 ≤ (4 * C₀ + 1) * L ^ 2 * (∑ i, variance (D i) π)
      + (4 * C₀ + 1) * Sandpile.truncatedGap ν L * ∑ i, b i ^ 2 := by
    have h1 : 0 ≤ ∑ i, variance (D i) π := Finset.sum_nonneg fun i _ => hvar0 i
    have h2 : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h3 : (0 : ℝ) < 4 * C₀ + 1 := by positivity
    positivity
  by_cases hint : Integrable (fun ξ => (F ξ - c - ∑ i, a i * ξ i) ^ 2) π
  case neg =>
    rw [integral_undef hint]
    exact hRHS
  case pos =>
  -- the coordinates
  have hcoord : ∀ i : Fin N, MeasurePreserving (fun ξ : Fin N → ℝ => ξ i) π ν := by
    intro i
    rw [hπ]
    exact measurePreserving_eval _ i
  have hsq' : Integrable (fun z => |z| ^ (2 : ℝ)) ν :=
    hsq.congr (Filter.Eventually.of_forall fun z => (LatticeProb.abs_rpow_two z).symm)
  have hνint : Integrable (fun z : ℝ => z) ν :=
    LatticeProb.integrable_abs_of_rpow (p := 2) ν (by norm_num) (fun z => z)
      measurable_id.aestronglyMeasurable hsq'
  have hxi : ∀ i, Integrable (fun ξ : Fin N → ℝ => ξ i) π := fun i =>
    LatticeProb.integrable_comp_mp (hcoord i) (fun z => z)
      measurable_id.aestronglyMeasurable hνint
  have hxi2 : ∀ i, Integrable (fun ξ : Fin N → ℝ => (ξ i) ^ 2) π := fun i =>
    LatticeProb.integrable_comp_mp (hcoord i) (fun z => z ^ 2)
      (by fun_prop) hsq
  have hximean : ∀ i, ∫ ξ, ξ i ∂π = 0 := by
    intro i
    rw [← LatticeProb.integral_comp_mp (hcoord i) (fun z => z)
      measurable_id.aestronglyMeasurable]
    exact hmean
  -- the derivative bounds
  have hDint : ∀ i, Integrable (D i) π := by
    intro i
    refine Integrable.mono' (integrable_const (b i)) (hDm i).aestronglyMeasurable ?_
    filter_upwards [hDb] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (hξ i).1]
    exact (hξ i).2
  have hD2 : ∀ i, Integrable (fun ξ => (D i ξ) ^ 2) π := by
    intro i
    refine Integrable.mono' (integrable_const (b i ^ 2))
      ((hDm i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hDb] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [(hξ i).1, (hξ i).2, hb0 i]
  have ha0 : ∀ i, 0 ≤ a i := by
    intro i
    show (0 : ℝ) ≤ ∫ η, D i η ∂π
    exact integral_nonneg_of_ae (by filter_upwards [hDb] with ξ hξ using (hξ i).1)
  have hab : ∀ i, a i ≤ b i := by
    intro i
    show (∫ η, D i η ∂π) ≤ b i
    have := integral_mono_ae (hDint i) (integrable_const (b i))
      (by filter_upwards [hDb] with ξ hξ using (hξ i).2)
    simpa using this
  have hvar : ∀ i, variance (D i) π = ∫ ξ, (D i ξ - a i) ^ 2 ∂π := fun i =>
    variance_eq_integral (hDm i).aemeasurable
  -- the resampling map
  have hupd : ∀ i : Fin N, MeasurePreserving
      (fun q : (Fin N → ℝ) × ℝ => Function.update q.1 i q.2) (π.prod ν) π := by
    intro i
    rw [hπ]
    exact LatticeProb.measurePreserving_update' _ i
  have hDbfst : ∀ᵐ q ∂(π.prod ν), ∀ i, 0 ≤ D i q.1 ∧ D i q.1 ≤ b i :=
    measurePreserving_fst.quasiMeasurePreserving.ae hDb
  have hDbupd : ∀ i : Fin N, ∀ᵐ q ∂(π.prod ν),
      ∀ k, 0 ≤ D k (Function.update q.1 i q.2)
        ∧ D k (Function.update q.1 i q.2) ≤ b k :=
    fun i => (hupd i).quasiMeasurePreserving.ae hDb
  -- the centred function
  set G : (Fin N → ℝ) → ℝ := fun ξ => F ξ - ∑ i, a i * ξ i with hGdef
  have hlinm : Measurable fun ξ : Fin N → ℝ => ∑ i, a i * ξ i :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have hGm : Measurable G := hFm.sub hlinm
  have hGc : ∀ ξ, F ξ - c - ∑ i, a i * ξ i = G ξ - c := fun ξ => by rw [hGdef]; ring
  have hint' : Integrable (fun ξ => (G ξ - c) ^ 2) π :=
    hint.congr (Filter.Eventually.of_forall fun ξ => by
      show (F ξ - c - ∑ i, a i * ξ i) ^ 2 = (G ξ - c) ^ 2
      rw [hGc ξ])
  have hgoal : ∫ ξ, (F ξ - c - ∑ i, a i * ξ i) ^ 2 ∂π = ∫ ξ, (G ξ - c) ^ 2 ∂π :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
      show (F ξ - c - ∑ i, a i * ξ i) ^ 2 = (G ξ - c) ^ 2
      rw [hGc ξ])
  rw [hgoal]
  have hG2 : Integrable (fun ξ => G ξ ^ 2) π := by
    refine Integrable.mono' ((hint'.const_mul 2).add (integrable_const (2 * c ^ 2)))
      ((hGm.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (G ξ - 2 * c)]
  have hG1 : Integrable G π :=
    LatticeProb.integrable_abs_of_rpow (p := 2) π (by norm_num) G hGm.aestronglyMeasurable
      (hG2.congr (Filter.Eventually.of_forall fun ξ => (LatticeProb.abs_rpow_two (G ξ)).symm))
  have hlin : Integrable (fun ξ : Fin N → ℝ => ∑ i, a i * ξ i) π :=
    integrable_finsetSum _ fun i _ => (hxi i).const_mul (a i)
  have hFint : Integrable F π :=
    (hG1.add hlin).congr (Filter.Eventually.of_forall fun ξ => by
      show G ξ + ∑ i, a i * ξ i = F ξ
      rw [hGdef]; ring)
  have hGmean : ∫ ξ, G ξ ∂π = c := by
    have hzero : ∀ i : Fin N, ∫ ξ, a i * ξ i ∂π = 0 := by
      intro i
      rw [integral_const_mul, hximean i, mul_zero]
    rw [hGdef, integral_sub hFint hlin,
      integral_finsetSum _ (fun i _ => (hxi i).const_mul (a i))]
    simp [hzero, hcdef]
  -- the dominating function for each coordinate's resampling energy
  have hDvar : ∀ i, Integrable (fun ξ => (D i ξ - a i) ^ 2) π := by
    intro i
    refine Integrable.mono' (integrable_const (b i ^ 2))
      (((hDm i).sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hDb] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [(hξ i).1, (hξ i).2, ha0 i, hab i]
  have hupdm : ∀ i : Fin N, Measurable
      (fun q : (Fin N → ℝ) × ℝ => (D i (Function.update q.1 i q.2) - a i) ^ 2) := fun i =>
    (((hDm i).comp (LatticeProb.measurable_update_pair i)).sub measurable_const).pow_const 2
  have hp1 : ∀ i, Integrable
      (fun q : (Fin N → ℝ) × ℝ => (D i q.1 - a i) ^ 2) (π.prod ν) := fun i =>
    (hDvar i).comp_fst ν
  have hp2 : ∀ i, Integrable
      (fun q : (Fin N → ℝ) × ℝ => (D i (Function.update q.1 i q.2) - a i) ^ 2)
      (π.prod ν) := fun i =>
    LatticeProb.integrable_comp_mp (hupd i) (fun ξ => (D i ξ - a i) ^ 2)
      ((((hDm i).sub measurable_const).pow_const 2)).aestronglyMeasurable (hDvar i)
  have hpairMP : ∀ i : Fin N, MeasurePreserving
      (fun q : (Fin N → ℝ) × ℝ => (q.1 i, q.2)) (π.prod ν) (ν.prod ν) := fun i =>
    (hcoord i).prod (MeasurePreserving.id ν)
  have htruncm : Measurable
      (fun p : ℝ × ℝ => if L < |p.1 - p.2| then (p.1 - p.2) ^ 2 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) measurable_const
    exact measurableSet_lt measurable_const (measurable_fst.sub measurable_snd).abs
  have htruncint : Integrable
      (fun p : ℝ × ℝ => if L < |p.1 - p.2| then (p.1 - p.2) ^ 2 else 0) (ν.prod ν) := by
    refine Integrable.mono' (((hsq.comp_fst ν).const_mul 2).add ((hsq.comp_snd ν).const_mul 2))
      htruncm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    by_cases hcase : L < |p.1 - p.2|
    · rw [if_pos hcase, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (p.1 + p.2)]
    · rw [if_neg hcase]
      simp only [abs_zero]
      nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  have hp3 : ∀ i : Fin N, Integrable
      (fun q : (Fin N → ℝ) × ℝ =>
        if L < |q.1 i - q.2| then (q.1 i - q.2) ^ 2 else 0) (π.prod ν) := fun i =>
    LatticeProb.integrable_comp_mp (hpairMP i) _ htruncm.aestronglyMeasurable htruncint
  have hgapeval : ∀ i : Fin N,
      ∫ q : (Fin N → ℝ) × ℝ, (if L < |q.1 i - q.2| then (q.1 i - q.2) ^ 2 else 0)
          ∂(π.prod ν) = Sandpile.truncatedGap ν L := by
    intro i
    rw [← LatticeProb.integral_comp_mp (hpairMP i) _ htruncm.aestronglyMeasurable,
      integral_prod _ htruncint]
    rfl
  have hp1eval : ∀ i : Fin N,
      ∫ q : (Fin N → ℝ) × ℝ, (D i q.1 - a i) ^ 2 ∂(π.prod ν)
        = variance (D i) π := by
    intro i
    rw [hvar i]
    exact (LatticeProb.integral_comp_mp measurePreserving_fst
      (fun ξ : Fin N → ℝ => (D i ξ - a i) ^ 2)
      (((hDm i).sub measurable_const).pow_const 2).aestronglyMeasurable).symm
  have hp2eval : ∀ i : Fin N,
      ∫ q : (Fin N → ℝ) × ℝ, (D i (Function.update q.1 i q.2) - a i) ^ 2 ∂(π.prod ν)
        = variance (D i) π := by
    intro i
    rw [hvar i]
    exact (LatticeProb.integral_comp_mp (hupd i)
      (fun ξ : Fin N → ℝ => (D i ξ - a i) ^ 2)
      (((hDm i).sub measurable_const).pow_const 2).aestronglyMeasurable).symm
  -- the pointwise bound on the resampling difference
  have hEbound : ∀ i : Fin N, ∀ᵐ q ∂(π.prod ν),
      (G q.1 - G (Function.update q.1 i q.2)) ^ 2
        ≤ 2 * L ^ 2 * ((D i q.1 - a i) ^ 2
            + (D i (Function.update q.1 i q.2) - a i) ^ 2)
          + b i ^ 2 * (if L < |q.1 i - q.2| then (q.1 i - q.2) ^ 2 else 0) := by
    intro i
    filter_upwards [hDbfst, hDbupd i] with q h1 h2
    obtain ⟨Δ, hΔeq, hΔmin, hΔmax⟩ :=
      Sandpile.exists_slope_between F D hconv hderiv i q.1 q.2
    have hu0 : 0 ≤ D i q.1 := (h1 i).1
    have hub : D i q.1 ≤ b i := (h1 i).2
    have hv0 : 0 ≤ D i (Function.update q.1 i q.2) := (h2 i).1
    have hvb : D i (Function.update q.1 i q.2) ≤ b i := (h2 i).2
    have hsum : (∑ k, a k * q.1 k) - ∑ k, a k * Function.update q.1 i q.2 k
        = a i * (q.1 i - q.2) := by
      rw [← Finset.sum_sub_distrib]
      refine (Finset.sum_eq_single i ?_ ?_).trans ?_
      · intro k _ hk
        rw [Function.update_of_ne hk]; ring
      · intro h; exact absurd (Finset.mem_univ i) h
      · rw [Function.update_self]; ring
    have hGdiff : G q.1 - G (Function.update q.1 i q.2) = (q.1 i - q.2) * (Δ - a i) := by
      show (F q.1 - ∑ k, a k * q.1 k)
          - (F (Function.update q.1 i q.2) - ∑ k, a k * Function.update q.1 i q.2 k)
        = (q.1 i - q.2) * (Δ - a i)
      rw [show (F q.1 - ∑ k, a k * q.1 k)
            - (F (Function.update q.1 i q.2)
              - ∑ k, a k * Function.update q.1 i q.2 k)
          = (F q.1 - F (Function.update q.1 i q.2))
            - ((∑ k, a k * q.1 k) - ∑ k, a k * Function.update q.1 i q.2 k) from by ring,
        hΔeq, hsum]
      ring
    have hΔ0 : 0 ≤ Δ := le_trans (le_min hu0 hv0) hΔmin
    have hΔb : Δ ≤ b i := le_trans hΔmax (max_le hub hvb)
    have habs2 : |Δ - a i| ≤ b i :=
      abs_le.mpr ⟨by linarith [ha0 i, hab i], by linarith [ha0 i]⟩
    have hxle : |Δ - a i|
        ≤ |D i q.1 - a i| + |D i (Function.update q.1 i q.2) - a i| := by
      have hmin : min (D i q.1) (D i (Function.update q.1 i q.2)) ≤ Δ := hΔmin
      have hmax : Δ ≤ max (D i q.1) (D i (Function.update q.1 i q.2)) := hΔmax
      have hlo : -(|D i q.1 - a i| + |D i (Function.update q.1 i q.2) - a i|) ≤ Δ - a i := by
        rcases le_total (D i q.1) (D i (Function.update q.1 i q.2)) with h | h
        · rw [min_eq_left h] at hmin
          have := neg_abs_le (D i q.1 - a i)
          have := abs_nonneg (D i (Function.update q.1 i q.2) - a i)
          linarith
        · rw [min_eq_right h] at hmin
          have := neg_abs_le (D i (Function.update q.1 i q.2) - a i)
          have := abs_nonneg (D i q.1 - a i)
          linarith
      have hhi : Δ - a i ≤ |D i q.1 - a i| + |D i (Function.update q.1 i q.2) - a i| := by
        rcases le_total (D i q.1) (D i (Function.update q.1 i q.2)) with h | h
        · rw [max_eq_right h] at hmax
          have := le_abs_self (D i (Function.update q.1 i q.2) - a i)
          have := abs_nonneg (D i q.1 - a i)
          linarith
        · rw [max_eq_left h] at hmax
          have := le_abs_self (D i q.1 - a i)
          have := abs_nonneg (D i (Function.update q.1 i q.2) - a i)
          linarith
      exact abs_le.mpr ⟨hlo, hhi⟩
    have hsq2 : (Δ - a i) ^ 2
        ≤ 2 * ((D i q.1 - a i) ^ 2 + (D i (Function.update q.1 i q.2) - a i) ^ 2) := by
      calc (Δ - a i) ^ 2 = |Δ - a i| ^ 2 := (sq_abs _).symm
        _ ≤ (|D i q.1 - a i| + |D i (Function.update q.1 i q.2) - a i|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hxle 2
        _ ≤ 2 * (|D i q.1 - a i| ^ 2
              + |D i (Function.update q.1 i q.2) - a i| ^ 2) := by
            nlinarith [sq_nonneg (|D i q.1 - a i|
              - |D i (Function.update q.1 i q.2) - a i|)]
        _ = 2 * ((D i q.1 - a i) ^ 2
              + (D i (Function.update q.1 i q.2) - a i) ^ 2) := by rw [sq_abs, sq_abs]
    rw [hGdiff, mul_pow]
    by_cases hcase : L < |q.1 i - q.2|
    · rw [if_pos hcase]
      have h1' : (Δ - a i) ^ 2 ≤ b i ^ 2 := by
        nlinarith [habs2, abs_nonneg (Δ - a i), sq_abs (Δ - a i), hb0 i]
      have h2' : 0 ≤ 2 * L ^ 2 * ((D i q.1 - a i) ^ 2
          + (D i (Function.update q.1 i q.2) - a i) ^ 2) := by positivity
      nlinarith [sq_nonneg (q.1 i - q.2), h1', h2']
    · rw [if_neg hcase, mul_zero, add_zero]
      have hle : |q.1 i - q.2| ≤ L := not_lt.mp hcase
      have hsqle : (q.1 i - q.2) ^ 2 ≤ L ^ 2 := by
        nlinarith [abs_nonneg (q.1 i - q.2), sq_abs (q.1 i - q.2), hL.le]
      calc (q.1 i - q.2) ^ 2 * (Δ - a i) ^ 2
          ≤ L ^ 2 * (2 * ((D i q.1 - a i) ^ 2
              + (D i (Function.update q.1 i q.2) - a i) ^ 2)) :=
            mul_le_mul hsqle hsq2 (sq_nonneg _) (sq_nonneg L)
        _ = 2 * L ^ 2 * ((D i q.1 - a i) ^ 2
              + (D i (Function.update q.1 i q.2) - a i) ^ 2) := by ring
  -- the resampling energies
  have hdomint : ∀ i : Fin N, Integrable
      (fun q : (Fin N → ℝ) × ℝ => 2 * L ^ 2 * ((D i q.1 - a i) ^ 2
          + (D i (Function.update q.1 i q.2) - a i) ^ 2)
        + b i ^ 2 * (if L < |q.1 i - q.2| then (q.1 i - q.2) ^ 2 else 0)) (π.prod ν) :=
    fun i => (((hp1 i).add (hp2 i)).const_mul (2 * L ^ 2)).add ((hp3 i).const_mul (b i ^ 2))
  have hEnergyInt : ∀ i : Fin N, Integrable
      (fun q : (Fin N → ℝ) × ℝ => (G q.1 - G (Function.update q.1 i q.2)) ^ 2)
      (π.prod ν) := by
    intro i
    refine Integrable.mono' (hdomint i)
      ((((hGm.comp measurable_fst).sub
        (hGm.comp (LatticeProb.measurable_update_pair i))).pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [hEbound i] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hq
  have hEle : ∀ i : Fin N,
      LatticeProb.resampleEnergy (fun _ : Fin N => ν) G i
        ≤ 4 * L ^ 2 * variance (D i) π + b i ^ 2 * Sandpile.truncatedGap ν L := by
    intro i
    have hmono := integral_mono_ae (hEnergyInt i) (hdomint i) (hEbound i)
    have e1 := integral_add (((hp1 i).add (hp2 i)).const_mul (2 * L ^ 2))
      ((hp3 i).const_mul (b i ^ 2))
    have e2 := integral_add (hp1 i) (hp2 i)
    simp only [Pi.add_apply] at e1 e2
    rw [e1, integral_const_mul, integral_const_mul, e2,
      hp1eval i, hp2eval i, hgapeval i] at hmono
    have hres : LatticeProb.resampleEnergy (fun _ : Fin N => ν) G i
        = ∫ q : (Fin N → ℝ) × ℝ, (G q.1 - G (Function.update q.1 i q.2)) ^ 2
            ∂(π.prod ν) := by
      rw [LatticeProb.resampleEnergy, hπ]
    rw [hres]
    linarith
  -- the Efron-Stein inequality
  have hkey := hES N (fun _ : Fin N => ν) (fun _ => hprob) G hGm (by rwa [← hπ])
    (by intro i; rw [← hπ]; exact hEnergyInt i)
  rw [← hπ, hGmean] at hkey
  have hsumle : ∑ i, LatticeProb.resampleEnergy (fun _ : Fin N => ν) G i
      ≤ ∑ i, (4 * L ^ 2 * variance (D i) π + b i ^ 2 * Sandpile.truncatedGap ν L) :=
    Finset.sum_le_sum fun i _ => hEle i
  have hsplit : ∑ i, (4 * L ^ 2 * variance (D i) π
        + b i ^ 2 * Sandpile.truncatedGap ν L)
      = 4 * L ^ 2 * (∑ i, variance (D i) π)
        + Sandpile.truncatedGap ν L * ∑ i, b i ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hsplit] at hsumle
  have hv1 : 0 ≤ ∑ i, variance (D i) π := Finset.sum_nonneg fun i _ => hvar0 i
  have hb1 : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  have h2 : 0 ≤ L ^ 2 * ∑ i, variance (D i) π := mul_nonneg hL2 hv1
  have h3 : 0 ≤ Sandpile.truncatedGap ν L * ∑ i, b i ^ 2 := mul_nonneg hgap0 hb1
  have h4 : C₀ * (∑ i, LatticeProb.resampleEnergy (fun _ : Fin N => ν) G i)
      ≤ C₀ * (4 * L ^ 2 * (∑ i, variance (D i) π)
        + Sandpile.truncatedGap ν L * ∑ i, b i ^ 2) :=
    mul_le_mul_of_nonneg_left hsumle hC₀pos.le
  have h5 : 0 ≤ (3 * C₀ + 1) * (Sandpile.truncatedGap ν L * ∑ i, b i ^ 2) :=
    mul_nonneg (by linarith) h3
  nlinarith [hkey, h4, h2, h5]

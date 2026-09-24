/-
Corollary of sandpile.tex, frozen.  `sandpile.tex:4299-4314`
(label `cor:dgt4-mean-lower`, parts (i) and (ii)):

  "(i) Let $(\zeta(x))_{x\in\Z^d}$ be i.i.d., mean zero, integrable, and
   nondegenerate.  There are $c>0$ and $t_0<\infty$, depending on $d$ and the
   one-site law, such that, for every $t\geq t_0$,
     $\E u_t(0)\geq c(\log t)^{2/d}$.
   (ii) If $a>0$ and $q\in(0,1]$ are fixed, then the constants in (i) can be
   chosen depending only on $d,a,q$ over all such fields satisfying
     $\P(\zeta(0)\leq-a)\geq q$."

Both parts are present, as the two conjuncts of the conclusion.  In (i) the
constants depend on `d` and the one-site law, so `c` and `t₀` are bound after
`ν`; in (ii) they depend only on `d, a, q`, so they are bound after `a, q` and
before `ν`.  This is the only difference between the two conjuncts apart from
the extra lower-tail hypothesis.  Integrability of `ζ(0)` is `Integrable id ν`
and mean zero is `∫ z, z ∂ν = 0`; the exponential moment of the section is
deliberately absent, since this corollary removes it.  Nondegeneracy is "the
law is not a point mass", written `∀ z, ν ≠ Measure.dirac z`, rather than
`0 < Var`, because only integrability is assumed and the variance may be
infinite.  `P(ζ(0) ≤ -a) ≥ q` is `ENNReal.ofReal q ≤ ν (Set.Iic (-a))`.
-/
import Sandpile.Law
import Sandpile.Support.IncrementBall
import Sandpile.Support.Increment
import Sandpile.Support.SceneryBridge

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_mean_lower
    (d : ℕ) (hd : 5 ≤ d) :
    (∀ ν : Measure ℝ, IsProbabilityMeasure ν → Integrable id ν → ∫ z, z ∂ν = 0 →
        (∀ z : ℝ, ν ≠ Measure.dirac z) →
        ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
          c * (Real.log t) ^ ((2 : ℝ) / d) ≤
            Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) ∧
      ∀ a q : ℝ, 0 < a → q ∈ Set.Ioc (0 : ℝ) 1 →
        ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ,
          ∀ ν : Measure ℝ, IsProbabilityMeasure ν → Integrable id ν → ∫ z, z ∂ν = 0 →
            (∀ z : ℝ, ν ≠ Measure.dirac z) →
            ENNReal.ofReal q ≤ ν (Set.Iic (-a)) →
            ∀ t : ℕ, t₀ ≤ t →
              c * (Real.log t) ^ ((2 : ℝ) / d) ≤
                Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t
-- FROZEN-STATEMENT-END
:= by
  classical
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hd2 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hd
    linarith
  have hexp : (1 : ℝ) / ((d : ℝ) / 2) = (2 : ℝ) / (d : ℝ) := by rw [one_div, inv_div]
  -- part (ii): the constants depend only on the fixed lower-tail bound
  have hII : ∀ a q : ℝ, 0 < a → q ∈ Set.Ioc (0 : ℝ) 1 →
      ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ,
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → Integrable id ν → ∫ z, z ∂ν = 0 →
          (∀ z : ℝ, ν ≠ Measure.dirac z) →
          ENNReal.ofReal q ≤ ν (Set.Iic (-a)) →
          ∀ t : ℕ, t₀ ≤ t →
            c * (Real.log t) ^ ((2 : ℝ) / d) ≤
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t := by
    intro a q ha hq
    obtain ⟨hq0, hq1⟩ := hq
    obtain ⟨c, hc, t₀, hbnd⟩ := Sandpile.exists_mean_lower_uniform hd1 hd2 a q ha hq0 hq1
    refine ⟨c, hc, t₀, fun ν hprob hintν hmean _hnondeg htail t ht => ?_⟩
    haveI := hprob
    rw [Sandpile.meanOdometer_eq d ν hd1 t]
    exact hbnd ν hprob hintν hmean htail t ht
  refine ⟨fun ν hprob hintν hmean hnondeg => ?_, hII⟩
  haveI := hprob
  obtain ⟨a, ha, hpa⟩ := Sandpile.exists_left_tail_pos ν hintν hmean hnondeg
  obtain ⟨q, hqdef⟩ : ∃ x : ℝ, x = min 1 (ν (Set.Iic (-a))).toReal := ⟨_, rfl⟩
  have hq0 : 0 < q := by
    rw [hqdef]
    exact lt_min one_pos (ENNReal.toReal_pos (ne_of_gt hpa) (measure_ne_top _ _))
  have hqle : ENNReal.ofReal q ≤ ν (Set.Iic (-a)) := by
    rw [hqdef]
    refine le_trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)) ?_
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  obtain ⟨c, hc, t₀, hbound⟩ := hII a q ha ⟨hq0, by rw [hqdef]; exact min_le_left _ _⟩
  exact ⟨c, hc, t₀, fun t ht => hbound ν hprob hintν hmean hnondeg hqle t ht⟩

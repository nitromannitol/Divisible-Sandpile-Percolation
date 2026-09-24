/-
Uniform resampling moments under the common exponential-moment bound of
`sandpile.tex:1950-1955,2630-2647`. All constants precede the scenery law.+-/
import Sandpile.Support.ExpMomentRpow
import LatticeProb.Prob.LpSmooth
import Sandpile.Support.Norms

open LatticeProb

open MeasureTheory ProbabilityTheory

namespace Sandpile

/-- The resampling moment is uniformly bounded over the entire class of laws.
The product moment is integrable, so neither integral uses a totalized value. -/
theorem resampleMoment_le_of_exp_bound
    (θ K p : ℝ) (hθ : 0 < θ) (hp : 1 ≤ p)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hK : ∫ z, Real.exp (θ * |z|) ∂ν ≤ K) :
    Integrable (fun q : ℝ × ℝ => |q.1 - q.2| ^ p) (ν.prod ν) ∧
      resampleMoment ν p ≤ 2 ^ p * (2 * ((p / θ) ^ p * K)) := by
  have hp0 : 0 ≤ p := by linarith
  have hi := integrable_abs_rpow_of_exp_moment ν θ hθ hexp p hp0
  have hb : (∫ z, |z| ^ p ∂ν) ≤ (p / θ) ^ p * K := by
    calc
      (∫ z, |z| ^ p ∂ν) ≤ ∫ z, (p / θ) ^ p * Real.exp (θ * |z|) ∂ν := by
        apply integral_mono hi (hexp.const_mul _)
        intro z
        simpa only [abs_of_pos hθ] using rpow_abs_le_mul_exp_abs z hp0 hθ.ne'
      _ = (p / θ) ^ p * ∫ z, Real.exp (θ * |z|) ∂ν := integral_const_mul _ _
      _ ≤ (p / θ) ^ p * K := mul_le_mul_of_nonneg_left hK (by positivity)
  have hpair := integrable_pair_rpow ν hp hi
  refine ⟨hpair, ?_⟩
  have hdom : Integrable (fun q : ℝ × ℝ =>
      (2 : ℝ) ^ p * (|q.1| ^ p + |q.2| ^ p)) (ν.prod ν) :=
    ((hi.comp_fst ν).add (hi.comp_snd ν)).const_mul _
  have hle : (∫ q : ℝ × ℝ, |q.1 - q.2| ^ p ∂(ν.prod ν)) ≤
      ∫ q : ℝ × ℝ, (2 : ℝ) ^ p * (|q.1| ^ p + |q.2| ^ p) ∂(ν.prod ν) := by
    apply integral_mono hpair hdom
    intro q
    exact (Real.rpow_le_rpow (abs_nonneg _) (abs_sub _ _) (by linarith)).trans
      (rpow_add_le_two hp (abs_nonneg _) (abs_nonneg _))
  rw [integral_prod _ hpair] at hle
  change resampleMoment ν p ≤ _ at hle
  rw [integral_const_mul, integral_add (hi.comp_fst ν) (hi.comp_snd ν)] at hle
  simp only [integral_prod _ (hi.comp_fst ν), integral_prod _ (hi.comp_snd ν),
    integral_const, probReal_univ, one_smul] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end Sandpile

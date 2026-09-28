import Sandpile.Support.LinL2Split

/-! # L² Assembly of Step 2

The `L²` assembly of Step 2 of `lem:dgt4-linearization-from-survival`
(`sandpile.tex:5803-5845`): the frozen integrand is `(A - B - C)²` with
`A = F_R`, `B = E F_R` and `C` the weighted linear field; the convex-linear
remainder `(A - B - D)²` and the coefficient replacement `(D - C)²` both vanish
in `L²`, and `(A-B-C)² ≤ 2(A-B-D)² + 2(D-C)²`.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Two vanishing `L²` remainders give the vanishing of the frozen integrand. -/
theorem tendsto_l2_of_two_remainders {l : Filter ℝ} (P : Measure Ω) (A B C D : ℝ → Ω → ℝ)
    (h1 : ∀ R, Integrable (fun ω => (A R ω - B R ω - D R ω) ^ 2) P)
    (h2 : ∀ R, Integrable (fun ω => (D R ω - C R ω) ^ 2) P)
    (h3 : ∀ R, Integrable (fun ω => (A R ω - B R ω - C R ω) ^ 2) P)
    (hl1 : Tendsto (fun R => ∫ ω, (A R ω - B R ω - D R ω) ^ 2 ∂P) l (𝓝 0))
    (hl2 : Tendsto (fun R => ∫ ω, (D R ω - C R ω) ^ 2 ∂P) l (𝓝 0)) :
    Tendsto (fun R => ∫ ω, (A R ω - B R ω - C R ω) ^ 2 ∂P) l (𝓝 0) := by
  have hb : ∀ R, ∫ ω, (A R ω - B R ω - C R ω) ^ 2 ∂P
      ≤ 2 * (∫ ω, (A R ω - B R ω - D R ω) ^ 2 ∂P)
        + 2 * (∫ ω, (D R ω - C R ω) ^ 2 ∂P) := by
    intro R
    have hpt : ∀ ω, (A R ω - B R ω - C R ω) ^ 2
        ≤ 2 * (A R ω - B R ω - D R ω) ^ 2 + 2 * (D R ω - C R ω) ^ 2 := by
      intro ω
      have h : A R ω - B R ω - C R ω = (A R ω - B R ω - D R ω) + (D R ω - C R ω) := by ring
      rw [h]
      nlinarith [sq_nonneg ((A R ω - B R ω - D R ω) - (D R ω - C R ω))]
    have h2i : Integrable (fun ω => 2 * (A R ω - B R ω - D R ω) ^ 2
        + 2 * (D R ω - C R ω) ^ 2) P := ((h1 R).const_mul 2).add ((h2 R).const_mul 2)
    calc ∫ ω, (A R ω - B R ω - C R ω) ^ 2 ∂P
        ≤ ∫ ω, (2 * (A R ω - B R ω - D R ω) ^ 2 + 2 * (D R ω - C R ω) ^ 2) ∂P :=
          integral_mono (h3 R) h2i hpt
      _ = 2 * (∫ ω, (A R ω - B R ω - D R ω) ^ 2 ∂P)
          + 2 * (∫ ω, (D R ω - C R ω) ^ 2 ∂P) := by
          rw [integral_add ((h1 R).const_mul 2) ((h2 R).const_mul 2), integral_const_mul,
            integral_const_mul]
  have htop : Tendsto (fun R => 2 * (∫ ω, (A R ω - B R ω - D R ω) ^ 2 ∂P)
      + 2 * (∫ ω, (D R ω - C R ω) ^ 2 ∂P)) l (𝓝 (2 * 0 + 2 * 0)) :=
    (hl1.const_mul 2).add (hl2.const_mul 2)
  refine squeeze_zero (fun R => integral_nonneg fun ω => sq_nonneg _) hb ?_
  simpa using htop

end Sandpile

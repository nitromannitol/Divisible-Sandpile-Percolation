/-
Weighted exponential concentration lemma of sandpile.tex, frozen.
`sandpile.tex:1345-1405` (label `lem:weighted-exp-conc`), all four parts:

  "Let $\xi_1,\ldots,\xi_N$ be independent real-valued random variables, and let
   $F=F(\xi_1,\ldots,\xi_N)$ be real-valued and measurable.  Let $\xi_i'$ be an
   independent copy of $\xi_i$, independent of all coordinates, and let
   $\xi^{(i)}$ be obtained from $\xi=(\xi_1,\ldots,\xi_N)$ by replacing only
   $\xi_i$ with $\xi_i'$.  Assume that, for deterministic numbers
   $\ell_i\geq0$, not all zero, for every $1\leq i\leq N$,
   $|F(\xi)-F(\xi^{(i)})|\leq \ell_i|\xi_i-\xi_i'|$.  Write
   $\|\ell\|_{\ell^2}:=(\sum_{i=1}^N\ell_i^2)^{1/2}$ and
   $\|\ell\|_{\ell^\infty}:=\max_{1\leq i\leq N}\ell_i$.
   (a) If $p\geq2$ and $\E|\xi_i|^p<\infty$ for every $i$, then there is
   $C=C(p)$ such that
   $(\E|F-\E F|^p)^{1/p}\leq C[(\sum_i\ell_i^2(\E|\xi_i-\xi_i'|^p)^{2/p})^{1/2}
   +(\sum_i\ell_i^p\E|\xi_i-\xi_i'|^p)^{1/p}]$.
   (b) If the $\xi_i$ are i.i.d. and $\E e^{\theta_0|\xi_1|}\leq K_0$, then there
   are $c>0$ and $C<\infty$, depending only on $\theta_0$ and $K_0$, such that,
   for all $r\geq0$,
   $\P(|F-\E F|\geq r)\leq C\exp\{-c\min(r^2/\|\ell\|_{\ell^2}^2,
   r/\|\ell\|_{\ell^\infty})\}$.
   (c) If the $\xi_i$ are i.i.d. with $\E\xi_1=0$ and
   $\E e^{\theta_0|\xi_1|}\leq K_0$, then there are $c>0$ and $C<\infty$,
   depending only on $\theta_0$ and $K_0$, such that, for every
   $\lambda\in\R$ with $|\lambda|\,\|\ell\|_{\ell^\infty}\leq c$,
   $\log\E\exp\{\lambda\sum_i\ell_i\xi_i\}\leq C\lambda^2\|\ell\|_{\ell^2}^2$.
   (d) Under the assumptions of part (b), if
   $|\lambda|\|\ell\|_{\ell^\infty}<\theta_0$, then
   $\E e^{\lambda(F-\E F)}\leq\exp\{C\lambda^2\|\ell\|_{\ell^2}^2\}$, where $C$
   depends only on $\theta_0$, $K_0$, and
   $\theta_0-|\lambda|\|\ell\|_{\ell^\infty}$."

Modelling.  The `N` independent coordinates are the product space
`Fin N → ℝ` under `Measure.pi μ` for a family of one-site laws
`μ : Fin N → Measure ℝ`; in parts (b), (c), (d) the coordinates are i.i.d., so
the family is the constant family `fun _ => ν`.  The resampled configuration
`ξ^{(i)}` is `Function.update ξ i y`, and the coordinate Lipschitz hypothesis is
imposed for every `ξ` and every replacement value `y`, which is the everywhere
form of the paper's almost sure statement.  The resampling moment
`\E|\xi_i-\xi_i'|^p` is the iterated integral `resampleMoment (μ i) p`, and
`\|\ell\|_{\ell^2}`, `\|\ell\|_{\ell^\infty}` are `lTwoNorm`, `lInfNorm` below.
`lInfNorm` is an `iSup` over `Fin N`, whose junk value at `N = 0` is never
reached because the hypothesis `∃ i, ℓ i ≠ 0` forces `N ≥ 1`; the same
hypothesis makes `lTwoNorm ℓ` and `lInfNorm ℓ` strictly positive, so the two
quotients in part (b) are not divisions by zero.

Quantifier order.  The four parts are four conjuncts of one statement, and the
theorem itself has no parameters, so that each part binds its own constants
exactly where the paper does.  In (a), `C = C(p)` is bound after `p` and before
`N`, `μ`, `F` and `ℓ`.  In (b) and (c), `c` and `C` are bound after `θ₀` and
`K₀` and before `N`, `ν`, `F` and `ℓ`.  In (d) the paper lets `C` depend on
`θ₀`, `K₀` and the gap `θ₀ - |λ| \|ℓ\|_{ℓ^∞}` as well, so `C` is a function of
that gap, bound after `θ₀` and `K₀` and before everything else.

Parts (b), (c) and (d) take the integrability of the exponential as a hypothesis
alongside the bound `E e^{θ₀|ξ₁|} ≤ K₀`, as the paper's finiteness requires: the
Bochner integral of a non-integrable nonnegative function is zero, so the bound
alone is satisfied by every law with no exponential moment at all, and for such a
law the conclusions are false rather than merely weak.  Parts (c) and (d) also
assert the integrability of the exponential alongside the bound
on its integral.  Without that conjunct a Bochner integral of a non-integrable
function takes the junk value zero, `Real.log 0 = 0`, and both bounds would hold
for a divergent exponential moment, which is the opposite of what the paper
asserts.
-/
import LatticeProb.Prob.LpSmooth
import LatticeProb.Prob.WeightedConc
import Sandpile.Support.Norms

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.weighted_exp_concentration :
    (∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (μ : Fin N → Measure ℝ), (∀ i, IsProbabilityMeasure (μ i)) →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
            |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
          (∀ i, Integrable (fun z => |z| ^ p) (μ i)) →
          (∫ ξ, |F ξ - ∫ η, F η ∂(Measure.pi μ)| ^ p ∂(Measure.pi μ)) ^ (1 / p) ≤
            C * ((∑ i, ℓ i ^ 2 * Sandpile.resampleMoment (μ i) p ^ (2 / p)) ^ (1 / 2 : ℝ) +
              (∑ i, ℓ i ^ p * Sandpile.resampleMoment (μ i) p) ^ (1 / p))) ∧
    (∀ θ₀ K₀ : ℝ, 0 < θ₀ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
            |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
          ∀ r : ℝ, 0 ≤ r →
            (Measure.pi fun _ : Fin N => ν)
                {ξ | r ≤ |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|} ≤
              ENNReal.ofReal (C * Real.exp (-(c * min (r ^ 2 / Sandpile.lTwoNorm ℓ ^ 2)
                (r / Sandpile.lInfNorm ℓ))))) ∧
    (∀ θ₀ K₀ : ℝ, 0 < θ₀ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          ∀ lam : ℝ, |lam| * Sandpile.lInfNorm ℓ ≤ c →
            Integrable (fun ξ => Real.exp (lam * ∑ i, ℓ i * ξ i))
                (Measure.pi fun _ : Fin N => ν) ∧
              Real.log (∫ ξ, Real.exp (lam * ∑ i, ℓ i * ξ i)
                  ∂(Measure.pi fun _ : Fin N => ν)) ≤
                C * lam ^ 2 * Sandpile.lTwoNorm ℓ ^ 2) ∧
    (∀ θ₀ K₀ : ℝ, 0 < θ₀ → ∃ C : ℝ → ℝ,
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
            |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
          ∀ lam : ℝ, |lam| * Sandpile.lInfNorm ℓ < θ₀ →
            Integrable (fun ξ => Real.exp (lam * (F ξ -
                ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν))))
                (Measure.pi fun _ : Fin N => ν) ∧
              ∫ ξ, Real.exp (lam * (F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)))
                  ∂(Measure.pi fun _ : Fin N => ν) ≤
                Real.exp (C (θ₀ - |lam| * Sandpile.lInfNorm ℓ) * lam ^ 2 *
                  Sandpile.lTwoNorm ℓ ^ 2))
-- FROZEN-STATEMENT-END
:= by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a), the `L^p` bound, from the square-function bound
    intro p hp
    have hp0 : (0 : ℝ) < p := by linarith
    obtain ⟨C, hCpos, hbound⟩ := LatticeProb.exists_lp_square_pi hp
    refine ⟨C ^ ((1 : ℝ) / 2), Real.rpow_pos_of_pos hCpos _, ?_⟩
    intro N μ hμ F hFm ℓ hℓ _hne hLip hmom
    have hkey := hbound N μ hμ F hFm ℓ hℓ hLip hmom
    set S : ℝ := ∑ i, ℓ i ^ 2 * Sandpile.resampleMoment (μ i) p ^ (2 / p) with hS
    set T : ℝ := ∑ i, ℓ i ^ p * Sandpile.resampleMoment (μ i) p with hT
    set I : ℝ := ∫ ξ, |F ξ - ∫ η, F η ∂(Measure.pi μ)| ^ p ∂(Measure.pi μ) with hI
    have hI0 : 0 ≤ I := integral_nonneg fun ξ => Real.rpow_nonneg (abs_nonneg _) _
    have hmom0 : ∀ i, 0 ≤ Sandpile.resampleMoment (μ i) p := fun i =>
      LatticeProb.pairMoment_nonneg (μ i) p
    have hS0 : 0 ≤ S := by
      refine Finset.sum_nonneg fun i _ => ?_
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hmom0 i) _)
    have hT0 : 0 ≤ T := by
      refine Finset.sum_nonneg fun i _ => ?_
      exact mul_nonneg (Real.rpow_nonneg (hℓ i) _) (hmom0 i)
    have hhalf : I ^ ((1 : ℝ) / p) = (I ^ (2 / p)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul hI0]
      congr 1
      field_simp
    have hstep : (I ^ (2 / p)) ^ ((1 : ℝ) / 2) ≤ (C * S) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hkey (by norm_num)
    have hsplit : (C * S) ^ ((1 : ℝ) / 2) = C ^ ((1 : ℝ) / 2) * S ^ ((1 : ℝ) / 2) :=
      Real.mul_rpow hCpos.le hS0
    have hTnn : 0 ≤ T ^ ((1 : ℝ) / p) := Real.rpow_nonneg hT0 _
    have hCnn : 0 ≤ C ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hCpos.le _
    calc I ^ ((1 : ℝ) / p) = (I ^ (2 / p)) ^ ((1 : ℝ) / 2) := hhalf
      _ ≤ (C * S) ^ ((1 : ℝ) / 2) := hstep
      _ = C ^ ((1 : ℝ) / 2) * S ^ ((1 : ℝ) / 2) := hsplit
      _ ≤ C ^ ((1 : ℝ) / 2) * (S ^ ((1 : ℝ) / 2) + T ^ ((1 : ℝ) / p)) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hCnn
  · -- (b)
    intro θ₀ K₀ hθ₀
    exact LatticeProb.weighted_exp_conc_tail θ₀ K₀ hθ₀
  · -- (c)
    intro θ₀ K₀ hθ₀
    exact LatticeProb.weighted_exp_conc_mgf θ₀ K₀ hθ₀
  · -- (d)
    intro θ₀ K₀ hθ₀
    exact ⟨fun g => 4 * (Real.exp K₀ * K₀) / g ^ 2,
      LatticeProb.weighted_exp_conc_exp θ₀ K₀ hθ₀⟩

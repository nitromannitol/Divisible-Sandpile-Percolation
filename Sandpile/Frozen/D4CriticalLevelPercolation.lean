/-
Theorem of Section 5 of sandpile.tex, frozen.  `sandpile.tex:3996-4012`
(label `thm:d4-critical-level-percolation`):

  "Fix $\nu_{0}>0$, $\theta_{0}>0$, and $K_{0}<\infty$.  There are
   $c=c(\nu_{0},\theta_{0},K_{0})>0$ and
   $t_0=t_0(\nu_{0},\theta_{0},K_{0})<\infty$ such that, for every mean-zero
   i.i.d.\ field $(\zeta(x))_{x\in\Z^4}$ satisfying
   $\Var(\zeta(0))\geq\nu_{0}^2$, $\E e^{\theta_{0}|\zeta(0)|}\leq K_{0}$,
   and every $t\geq t_0$, the planar set $\{x\in\Pi:u_t(x)>c\log t\}$ contains
   an infinite nearest-neighbor component almost surely."

Here `Π` is the coordinate plane `Π = ℤ² × {0}²  ⊂ ℤ⁴` of
`eq:d4-coordinate-plane` (`sandpile.tex:3432-3434`).  It is presented by the
embedding `planeEmbed : Site 2 → Site 4` below, and the conclusion is stated
for the pullback subset of `Site 2`: two sites of `Π` are nearest neighbours in
`ℤ⁴` exactly when their preimages are nearest neighbours in `ℤ²`, so
`HasInfiniteComponent` at `d = 2` is the paper's infinite nearest-neighbour
component inside `Π`.  The scenery is carried by its one-site law `ν` and the
field by `centeredMassLaw 4 ν`, the law of `σ = 1 + 8ζ`.  `c` and `t₀` are
bound after `ν₀, θ₀, K₀` and before the law, as the paper orders them.

The exponential-moment bound is stated together with the integrability of the
exponential, as the paper's `K₀ < ∞` requires: the Bochner integral of a
non-integrable nonnegative function is zero, so the bound alone would hold for
every law with no exponential moment.
-/
import Sandpile.Law
import Sandpile.External.BallGreenBounds
import Sandpile.External.PlanarRSW
import Sandpile.External.LSSDomination
import Sandpile.External.VarianceScale
import Sandpile.Support.D4PlaneEmbed
import Sandpile.Support.D4CritBlockEstimate
import Sandpile.Support.D4CritRange
import Sandpile.Support.D4CritScale
import Sandpile.Support.D4GoodBlock
import Sandpile.Support.D4OdometerComponent

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_critical_level_percolation
    (hBallGreen : Sandpile.External.BallGreenBounds)
    (hRSW : Sandpile.External.PlanarRSW)
    (hLSS : Sandpile.External.LSSDomination)
    (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.centeredMassLaw 4 ν),
          Sandpile.HasInfiniteComponent
            {z : Sandpile.Site 2 |
              c * Real.log t < Sandpile.odometer σ t (Sandpile.planeEmbed z)}
-- FROZEN-STATEMENT-END
:= by
  classical
  have hVarScale : Sandpile.External.VarianceScale := Sandpile.External.varianceScale
  obtain ⟨b₀, Aloc, Aex, hb₀, hAloc, hAex, hblock⟩ :=
    Sandpile.exists_block_estimate hBallGreen hRSW hVarScale ν₀ θ₀ K₀ hν₀ hθ₀
  set k : ℕ := ⌈4 * Aloc + 20⌉₊ with hkdef
  have hkle : 4 * Aloc + 20 ≤ (k : ℝ) := Nat.le_ceil _
  obtain ⟨δ, hδ, hLSSmain⟩ := Sandpile.good_block_percolation hLSS k
  obtain ⟨r₀, hr₀1, hbe⟩ := hblock δ hδ
  obtain ⟨R₂, hR₂⟩ := Filter.eventually_atTop.mp
    (Sandpile.Frozen.d4_finite_range_lower_bound Aloc hAloc Aex hAex).2
  set A : ℕ := 4 * Aex + 3 with hA
  set n₀ : ℕ := max (max r₀ R₂) 2 with hn₀
  refine ⟨b₀ / 8, by positivity, max (16 * (A + 1) ^ 2) (n₀ ^ 2 * (A + 1)), ?_⟩
  intro ν hν hmean hvar hexpint hexp t ht
  haveI := hν
  set r : ℕ := ⌊Real.sqrt ((t : ℝ) / ((A : ℝ) + 1))⌋₊ with hr
  have hn₀r : n₀ ≤ r := Sandpile.le_floor_sqrt A t n₀ (le_trans (le_max_right _ _) ht)
  have hr₀r : r₀ ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn₀r
  have hR₂r : R₂ ≤ 2 * r := by
    have h : R₂ ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn₀r
    omega
  have hr2 : 2 ≤ r := le_trans (le_max_right _ _) hn₀r
  have hr1 : 1 ≤ r := by omega
  have hhor : (Aex + 1) * (2 * r) ^ 2 ≤ t := by
    have h := Sandpile.floor_sqrt_sq_le A t
    have hEq : (A + 1) * r ^ 2 = (Aex + 1) * (2 * r) ^ 2 := by rw [hA]; ring
    rw [hEq] at h
    exact h
  have ht0 : 16 * (A + 1) ^ 2 ≤ t := le_trans (le_max_left _ _) ht
  have hpow4 : (t : ℝ) ≤ (r : ℝ) ^ 4 := Sandpile.le_floor_sqrt_pow4 A t ht0
  have htpos : 0 < t := by
    have : 0 < 16 * (A + 1) ^ 2 := by positivity
    omega
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hlogr : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hrR
  have hlogt : Real.log t ≤ 4 * Real.log (r : ℝ) := by
    have h1 : Real.log (t : ℝ) ≤ Real.log ((r : ℝ) ^ 4) :=
      Real.log_le_log htR hpow4
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  set ℓ : ℝ := b₀ * Real.log ((2 * r : ℕ) : ℝ) / 2 with hℓ
  have hlt : Real.log (r : ℝ) < Real.log ((2 * r : ℕ) : ℝ) := by
    refine Real.log_lt_log (by linarith) ?_
    push_cast
    linarith
  have hlevel : b₀ / 8 * Real.log t < ℓ := by
    rw [hℓ]
    nlinarith [hlogt, hlt, hb₀, hlogr]
  -- the one-site probability
  have hone : ∀ z : Sandpile.Site 2, 1 - δ ≤
      ((LatticeProb.iidLaw 4 ν) {ζ : Sandpile.Site 4 → ℝ |
        decide (Sandpile.BlockGood r
          (Sandpile.frBlockField Aex Aloc (2 * r) ζ) ℓ z) = true}).toReal := by
    intro z
    have hbad := hbe ν hν hmean hvar hexpint hexp r hr₀r z
    have hms := Sandpile.measurableSet_blockGood_frBlockField Aex Aloc (2 * r) r ℓ z
    have hset : {ζ : Sandpile.Site 4 → ℝ |
        decide (Sandpile.BlockGood r (Sandpile.frBlockField Aex Aloc (2 * r) ζ) ℓ z) = true}
        = {ζ : Sandpile.Site 4 → ℝ |
          Sandpile.BlockGood r (Sandpile.frBlockField Aex Aloc (2 * r) ζ) ℓ z} := by
      ext ζ; simp
    rw [hset]
    have hsum := measure_add_measure_compl (μ := LatticeProb.iidLaw 4 ν) hms
    have h2 : ((LatticeProb.iidLaw 4 ν) {ζ : Sandpile.Site 4 → ℝ |
          Sandpile.BlockGood r (Sandpile.frBlockField Aex Aloc (2 * r) ζ) ℓ z}).toReal
        + ((LatticeProb.iidLaw 4 ν) {ζ : Sandpile.Site 4 → ℝ |
          Sandpile.BlockGood r (Sandpile.frBlockField Aex Aloc (2 * r) ζ) ℓ z}ᶜ).toReal = 1 := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum]
      simp
    have h3 : ((LatticeProb.iidLaw 4 ν) {ζ : Sandpile.Site 4 → ℝ |
        Sandpile.BlockGood r (Sandpile.frBlockField Aex Aloc (2 * r) ζ) ℓ z}ᶜ).toReal ≤ δ :=
      ENNReal.toReal_le_of_le_ofReal hδ.le hbad
    linarith
  have hLSSconc := hLSSmain (Sandpile.Site 4 → ℝ) (LatticeProb.iidLaw 4 ν) r hr1
    (fun ζ => Sandpile.frBlockField Aex Aloc (2 * r) ζ) ℓ
    (fun z => Sandpile.measurable_decide_blockGood Aex Aloc (2 * r) r ℓ z)
    (fun w => Sandpile.blockGood_law_stationary ν Aex Aloc (2 * r) r ℓ w)
    (fun S T _ _ hdist => Sandpile.indep_blockGood_of_dist ν Aex Aloc r hr1 ℓ (k : ℝ)
      hkle (hR₂ (2 * r) hR₂r) S T hdist)
    hone
  exact Sandpile.infinite_odometer_component_of_field ν
    (fun ζ y => Sandpile.frGreenFieldTime (2 * r) (Aex * (2 * r) ^ 2) ζ y
      + Sandpile.frExitValue Aex Aloc (2 * r) ζ y)
    (b₀ / 8) ℓ t ((Aex + 1) * (2 * r) ^ 2) hhor
    (fun ζ y => (Sandpile.Frozen.d4_finite_range_lower_bound Aloc hAloc Aex hAex).1 ζ (2 * r) y)
    hlevel hLSSconc


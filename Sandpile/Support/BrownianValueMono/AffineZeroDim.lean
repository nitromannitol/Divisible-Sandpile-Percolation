import Sandpile.Support.BrownianValueMono.GreenZeroDim
import Sandpile.Support.ExplHorizon

/-!
# The Gaussian heat potential is affine in time when the space is a point

In dimension zero, `Space 0` has a single point, so the finite-time Green kernel of the
dimension-zero Brownian motion does not see the spatial variable at all and equals the time
argument exactly (`greenTimeBM_zero_dim`). Linearity of white noise then makes the Gaussian
heat potential `Z(t,x,ω)` an exactly affine function of `t`, samplewise: `Z(t,x,ω) = t · c(ω)`
for the slope `c(ω) = √ν2 · 𝒲(1)(ω)`. This module proves the affine identity first at every
rational time (`gaussianPotential_eq_affine_of_rat`), then extends it to every time in a finite
strip by density of the rationals and the continuity of the locally continuous version
(`gaussianPotential_eq_affine_zero_dim`). Nothing here assumes any regularity of the field beyond
what the frozen node's hypotheses already supply.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

theorem gaussianPotential_eq_affine_of_rat {ΩW : Type*} [MeasurableSpace ΩW]
    {PW : Measure ΩW} {W : (Space 0 → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise 0 W PW) (ν2 : ℝ) (Z : ℝ → Space 0 → ΩW → ℝ)
    (hmod : ∀ (t : ℝ) (x : Space 0), Z t x =ᵐ[PW] gaussianPotential 0 ν2 W t x)
    (t : ℝ) (x : Space 0) :
    Z t x =ᵐ[PW] fun ω => t * (Real.sqrt ν2 * W (fun _ : Space 0 => (1 : ℝ)) ω) := by
  have hmem : MemLp (fun _ : Space 0 => (1 : ℝ)) 2 (volume : Measure (Space 0)) := MemLp.of_discrete
  have hker : (fun y : Space 0 => greenTimeBM 0 t x y) = t • fun _ : Space 0 => (1 : ℝ) := by
    funext y
    rw [greenTimeBM_zero_dim]
    simp
  have hsmul := hW.smul t (fun _ : Space 0 => (1 : ℝ)) hmem
  filter_upwards [hmod t x, hsmul] with ω h1 h2
  rw [h1]
  unfold gaussianPotential
  rw [hker, h2]
  ring

/-- A continuous function on `[0, T]` that agrees with an affine function of slope `c` at every
rational point of `[0, T]` agrees with it on all of `[0, T]`: the rationals are dense in the
reals, and both sides are continuous. -/
theorem eq_affine_of_continuousOn_of_eq_rat (T : ℝ) (c : ℝ) (Z : ℝ → ℝ)
    (hcont : ContinuousOn Z (Set.Icc (0 : ℝ) T)) (hrat : ∀ q : ℚ, Z (q : ℝ) = (q : ℝ) * c) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, Z s = s * c := by
  intro s hs
  set qr : ℕ → ℚ := fun n => (⌊s * ((n : ℝ) + 1)⌋₊ : ℚ) / ((n : ℚ) + 1) with hqr
  set q : ℕ → ℝ := fun n => (qr n : ℝ) with hqdef
  have hqcast : ∀ n : ℕ, q n = (⌊s * ((n : ℝ) + 1)⌋₊ : ℝ) / ((n : ℝ) + 1) := by
    intro n
    rw [hqdef, hqr]
    push_cast
    ring
  have hqle : ∀ n : ℕ, q n ≤ s := by
    intro n
    rw [hqcast, div_le_iff₀ (by positivity)]
    exact Nat.floor_le (mul_nonneg hs.1 (by positivity))
  have hqge : ∀ n : ℕ, 0 ≤ q n := by
    intro n
    rw [hqcast]
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hqmem : ∀ n : ℕ, q n ∈ Set.Icc (0 : ℝ) T := fun n => ⟨hqge n, (hqle n).trans hs.2⟩
  have hqclose : ∀ n : ℕ, s - 1 / ((n : ℝ) + 1) ≤ q n := by
    intro n
    rw [hqcast, le_div_iff₀ (by positivity)]
    have h1 := Nat.lt_floor_add_one (s * ((n : ℝ) + 1))
    have hinv : (1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = 1 := by
      rw [div_mul_cancel₀]
      positivity
    nlinarith [h1, hinv]
  have hqtendsto : Tendsto q atTop (nhds s) := by
    have hlo : Tendsto (fun n : ℕ => s - 1 / ((n : ℝ) + 1)) atTop (nhds s) := by
      have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => s - 1 / ((n : ℝ) + 1)) atTop (nhds (s - 0)) :=
        tendsto_const_nhds.sub h0
      simpa using h2
    have hhi : Tendsto (fun _ : ℕ => s) atTop (nhds s) := tendsto_const_nhds
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi hqclose hqle
  have hqtendstoWithin : Tendsto q atTop (nhdsWithin s (Set.Icc (0 : ℝ) T)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqtendsto, Eventually.of_forall hqmem⟩
  have hZtendsto : Tendsto (fun t => Z t) (nhdsWithin s (Set.Icc (0 : ℝ) T)) (nhds (Z s)) :=
    hcont s hs
  have h1 : Tendsto (fun n => Z (q n)) atTop (nhds (Z s)) := hZtendsto.comp hqtendstoWithin
  have h2 : Tendsto (fun n => q n * c) atTop (nhds (s * c)) := hqtendsto.mul tendsto_const_nhds
  have h3 : (fun n => Z (q n)) = fun n => q n * c := by
    funext n
    rw [hqdef]
    exact hrat (qr n)
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- **In dimension zero, the Gaussian heat potential is exactly affine in time.**  Samplewise, on
every finite time strip: `Z(s,x,ω) = s · c(ω)` for the slope `c(ω) = √ν2 · 𝒲(1)(ω)`, since the
finite-time Green kernel of dimension-zero Brownian motion is the identity function of the time
argument (`greenTimeBM_zero_dim`). -/
theorem gaussianPotential_eq_affine_zero_dim {ΩW : Type*} [MeasurableSpace ΩW]
    {PW : Measure ΩW} [IsProbabilityMeasure PW] {W : (Space 0 → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise 0 W PW) (ν2 : ℝ) (Z : ℝ → Space 0 → ΩW → ℝ)
    (hmod : ∀ (t : ℝ) (x : Space 0), Z t x =ᵐ[PW] gaussianPotential 0 ν2 W t x)
    (T : ℝ) (_hT : 0 < T)
    (hc : ∀ᵐ ω ∂PW, ContinuousOn (fun p : ℝ × Space 0 => Z p.1 p.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ∀ᵐ ω ∂PW, ∀ x : Space 0, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Z s x ω = s * (Real.sqrt ν2 * W (fun _ : Space 0 => (1 : ℝ)) ω) := by
  have hrat : ∀ᵐ ω ∂PW, ∀ p : ℚ × Space 0,
      Z (p.1 : ℝ) p.2 ω = (p.1 : ℝ) * (Real.sqrt ν2 * W (fun _ : Space 0 => (1 : ℝ)) ω) :=
    ae_all_iff.mpr fun p => gaussianPotential_eq_affine_of_rat hW ν2 Z hmod (p.1 : ℝ) p.2
  filter_upwards [hrat, hc] with ω hratω hcω x s hs
  have hcontx : ContinuousOn (fun t : ℝ => Z t x ω) (Set.Icc (0 : ℝ) T) :=
    hcω.comp (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, trivial⟩)
  exact eq_affine_of_continuousOn_of_eq_rat T (Real.sqrt ν2 * W (fun _ : Space 0 => (1 : ℝ)) ω)
    (fun t => Z t x ω) hcontx (fun q => hratω (q, x)) s hs

end Sandpile.Continuum

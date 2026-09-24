/-
The cube-killed Brownian stopping value `𝒰_{Z,□}` of `rem:dlt4-killed-scaling`
(`sandpile.tex:1929-1950`).

The remark reads: "Let `𝒰_{Z,□}(T,u)` be the Brownian stopping value from
`eq:continuum-membrane-stopping-value`, with stopping rules killed on exiting the
cube `u+[-1,1]^d`."  That value is defined here in exactly the shape of
`Sandpile.Continuum.brownianDiscountBall` and `brownianValueBall`, with the
Euclidean ball condition `‖B_s - u‖ ≤ A` replaced by the cube condition
`∀ i, |B_s(i) - u(i)| ≤ L`; the remark's cube is the case `L = 1`, since
`u+[-1,1]^d` is the set of points whose coordinates differ from those of `u` by at
most one.

The remark's own inequality `𝒰_{Z,□}(T,u) ≥ 𝒰_{Z,1}(T,u)`, "since the Euclidean
unit ball is contained in this cube", is `brownianValueBall_le_brownianValueCube`:
a coordinate of a vector is bounded by its Euclidean norm, so a stopping rule that
has not left the ball of radius `A` has not left the cube of half-width `L` as soon
as `A ≤ L`, and the attainable set of the ball value is a subset of the attainable
set of the cube value.  That statement asks the payoffs of the unrestricted family to be
bounded above; `brownianValueBall_le_brownianValueCube_of_bddAbove_cube` asks only that the
cube payoffs be, which is what a continuous reward provides.

The cube value is positively homogeneous in the reward (`brownianValueCube_const_mul`); with the
identification of the potential of variance `v` as `√v` times the potential of unit variance,
that is the remark's sentence that the limit for a scenery law of variance `ν²` is `ν` times the
value for unit-variance scenery.

No node of the ledger is registered for the remark; these are the objects its
coupling will be stated with.
-/
import Sandpile.Support.ExplBallGap

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- The payoffs attainable in the cube-killed discount `𝒟_{h,□}(T,u)`: the payoffs of the
stopping times bounded by `T` which have not left the cube of half-width `L` about `u`
strictly before they stop. -/
def cubeStoppingPayoffs (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) (h : ℝ → Space d → ℝ)
    (T L : ℝ) (u : Space d) : Set ℝ :=
  {a : ℝ | ∃ τ : ΩB → ℝ≥0, IsBrownianStopping B τ ∧ (∀ ω, (τ ω : ℝ) ≤ T) ∧
    (∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < τ ω → ∀ i, |B s ω i - u i| ≤ L) ∧
    a = ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P}

/-- `𝒟_{h,□}(T,u)`, the discount of the value killed on exiting the cube of half-width `L`
about `u`. -/
noncomputable def brownianDiscountCube (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L : ℝ) (u : Space d) : ℝ :=
  sSup (cubeStoppingPayoffs B P h T L u)

/-- `𝒰_{h,□}(T,u)`, the cube-killed value of `rem:dlt4-killed-scaling`. -/
noncomputable def brownianValueCube (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L : ℝ) (u : Space d) : ℝ :=
  h T u + brownianDiscountCube B P h T L u

theorem brownianDiscountCube_eq_sSup (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L : ℝ) (u : Space d) :
    brownianDiscountCube B P h T L u = sSup (cubeStoppingPayoffs B P h T L u) := rfl

theorem brownianValueCube_eq (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L : ℝ) (u : Space d) :
    brownianValueCube B P h T L u = h T u + brownianDiscountCube B P h T L u := rfl

/-- The attainable set of the cube-killed value is a subset of the attainable set of the
value: the cube-killed family is cut out of the full one by one further clause. -/
theorem cubeStoppingPayoffs_subset (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L : ℝ) (u : Space d) :
    cubeStoppingPayoffs B P h T L u ⊆ stoppingPayoffs B P h T := by
  rintro a ⟨τ, hτ, hb, -, rfl⟩
  exact ⟨τ, hτ, hb, rfl⟩

/-- **The Euclidean ball is contained in the cube**: a coordinate of a vector is bounded by
its Euclidean norm, so a rule that has not left the ball of radius `A` has not left the cube
of half-width `L` as soon as `A ≤ L`.  This is the sentence of `rem:dlt4-killed-scaling`,
"since the Euclidean unit ball is contained in this cube". -/
theorem ballStoppingPayoffs_subset_cube (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A L : ℝ) (hAL : A ≤ L) (u : Space d) :
    ballStoppingPayoffs B P h T A u ⊆ cubeStoppingPayoffs B P h T L u := by
  rintro a ⟨τ, hτ, hb, hball, rfl⟩
  refine ⟨τ, hτ, hb, ?_, rfl⟩
  filter_upwards [hball] with ω hω
  intro s hs i
  have h1 : |B s ω i - u i| = ‖(B s ω - u) i‖ := by
    rw [Real.norm_eq_abs]
    rfl
  rw [h1]
  exact le_trans (PiLp.norm_apply_le _ i) (le_trans (hω s hs) hAL)

/-- The attainable set of the cube-killed value grows with the cube. -/
theorem cubeStoppingPayoffs_mono (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L L' : ℝ) (hL : L ≤ L') (u : Space d) :
    cubeStoppingPayoffs B P h T L u ⊆ cubeStoppingPayoffs B P h T L' u := by
  rintro a ⟨τ, hτ, hb, hcube, rfl⟩
  exact ⟨τ, hτ, hb, hcube.mono (fun ω hω s hs i => le_trans (hω s hs i) hL), rfl⟩

/-- `𝒟_{h,□}(T,u) ≥ -h(T,u)` for a motion that starts at `u` only almost surely: the
stopping time `τ = 0` never leaves the cube, because no element of `ℝ≥0` is negative. -/
theorem neg_le_brownianDiscountCube_ae (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T L : ℝ) (hT : 0 ≤ T) (u : Space d)
    (hstart : ∀ᵐ ω ∂P, B 0 ω = u) (hbdd : BddAbove (cubeStoppingPayoffs B P h T L u)) :
    -h T u ≤ brownianDiscountCube B P h T L u := by
  refine le_csSup hbdd ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using hT,
    Filter.Eventually.of_forall (fun ω s hs => absurd hs (by simp)), ?_⟩
  have hcongr : ∫ ω, -h (T - ((0 : ℝ≥0) : ℝ)) (B 0 ω) ∂P = ∫ _ω : ΩB, -h T u ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hstart] with ω hω
    rw [hω]
    norm_num
  rw [hcongr, integral_const]
  simp

/-- The cube-killed attainable set is nonempty: `τ = 0` is admissible. -/
theorem cubeStoppingPayoffs_nonempty (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L : ℝ) (hT : 0 ≤ T) (u : Space d) :
    (cubeStoppingPayoffs B P h T L u).Nonempty :=
  ⟨∫ ω, -h (T - ((0 : ℝ≥0) : ℝ)) (B 0 ω) ∂P,
    ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using hT,
      Filter.Eventually.of_forall (fun ω s hs => absurd hs (by simp)), rfl⟩⟩

/-- The ball-localized attainable set is nonempty: `τ = 0` is admissible. -/
theorem ballStoppingPayoffs_nonempty (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A : ℝ) (hT : 0 ≤ T) (u : Space d) :
    (ballStoppingPayoffs B P h T A u).Nonempty :=
  ⟨∫ ω, -h (T - ((0 : ℝ≥0) : ℝ)) (B 0 ω) ∂P,
    ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using hT,
      Filter.Eventually.of_forall (fun ω s hs => absurd hs (by simp)), rfl⟩⟩

/-- The cube-killed attainable set is bounded above as soon as the full one is. -/
theorem bddAbove_cubeStoppingPayoffs (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L : ℝ) (u : Space d)
    (hbdd : BddAbove (stoppingPayoffs B P h T)) :
    BddAbove (cubeStoppingPayoffs B P h T L u) :=
  hbdd.mono (cubeStoppingPayoffs_subset B P h T L u)

/-- `𝒟_{h,□}(T,u) ≤ 𝒟_h(T,u)`. -/
theorem brownianDiscountCube_le (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L : ℝ) (hT : 0 ≤ T) (u : Space d)
    (hbdd : BddAbove (stoppingPayoffs B P h T)) :
    brownianDiscountCube B P h T L u ≤ brownianDiscount B P h T :=
  csSup_le (cubeStoppingPayoffs_nonempty B P h T L hT u) fun _a ha =>
    le_csSup hbdd (cubeStoppingPayoffs_subset B P h T L u ha)

/-- `𝒟_{h,A}(T,u) ≤ 𝒟_{h,□}(T,u)` for `A ≤ L`. -/
theorem brownianDiscountBall_le_brownianDiscountCube (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A L : ℝ) (hT : 0 ≤ T) (hAL : A ≤ L) (u : Space d)
    (hbdd : BddAbove (stoppingPayoffs B P h T)) :
    brownianDiscountBall B P h T A u ≤ brownianDiscountCube B P h T L u :=
  csSup_le (ballStoppingPayoffs_nonempty B P h T A hT u) fun _a ha =>
    le_csSup (bddAbove_cubeStoppingPayoffs B P h T L u hbdd)
      (ballStoppingPayoffs_subset_cube B P h T A L hAL u ha)

/-- **`𝒰_{h,□}(T,u) ≥ 𝒰_{h,A}(T,u)` for `A ≤ L`**, the inequality of
`rem:dlt4-killed-scaling` at `sandpile.tex:1946-1948`, whose case is `A = L = 1`. -/
theorem brownianValueBall_le_brownianValueCube (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A L : ℝ) (hT : 0 ≤ T) (hAL : A ≤ L) (u : Space d)
    (hbdd : BddAbove (stoppingPayoffs B P h T)) :
    brownianValueBall B P h T A u ≤ brownianValueCube B P h T L u := by
  unfold brownianValueBall brownianValueCube
  have := brownianDiscountBall_le_brownianDiscountCube B P h T A L hT hAL u hbdd
  linarith

/-- The cube-killed discount is nondecreasing in the cube. -/
theorem brownianDiscountCube_mono (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L L' : ℝ) (hT : 0 ≤ T) (hL : L ≤ L') (u : Space d)
    (hbdd : BddAbove (stoppingPayoffs B P h T)) :
    brownianDiscountCube B P h T L u ≤ brownianDiscountCube B P h T L' u :=
  csSup_le (cubeStoppingPayoffs_nonempty B P h T L hT u) fun _a ha =>
    le_csSup (bddAbove_cubeStoppingPayoffs B P h T L' u hbdd)
      (cubeStoppingPayoffs_mono B P h T L L' hL u ha)

/-- The cube-killed value is nondecreasing in the cube. -/
theorem brownianValueCube_mono (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L L' : ℝ) (hT : 0 ≤ T) (hL : L ≤ L') (u : Space d)
    (hbdd : BddAbove (stoppingPayoffs B P h T)) :
    brownianValueCube B P h T L u ≤ brownianValueCube B P h T L' u := by
  unfold brownianValueCube
  have := brownianDiscountCube_mono B P h T L L' hT hL u hbdd
  linarith

/-- **`0 ≤ 𝒰_{h,□}(T,u) ≤ 𝒰_h(T,u)`**, the cube-killed form of the sentence at
`sandpile.tex:1645`. -/
theorem zero_le_brownianValueCube_le (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T L : ℝ) (hT : 0 ≤ T) (u : Space d)
    (hstart : ∀ᵐ ω ∂P, B 0 ω = u)
    (hbdd : BddAbove (stoppingPayoffs B P h T)) :
    0 ≤ brownianValueCube B P h T L u ∧
      brownianValueCube B P h T L u ≤ brownianValue B P h T u := by
  have h1 : -h T u ≤ brownianDiscountCube B P h T L u :=
    neg_le_brownianDiscountCube_ae B P h T L hT u hstart
      (bddAbove_cubeStoppingPayoffs B P h T L u hbdd)
  have h2 : brownianDiscountCube B P h T L u ≤ brownianDiscount B P h T :=
    brownianDiscountCube_le B P h T L hT u hbdd
  constructor
  · unfold brownianValueCube
    linarith
  · unfold brownianValueCube brownianValue
    linarith

/-- **`𝒰_{h,□}(T,u) ≥ 𝒰_{h,A}(T,u)` for `A ≤ L`, asking only that the cube payoffs be bounded
above.**  The ball payoffs sit inside the cube payoffs, so the supremum over the cube is an upper
bound for the supremum over the ball as soon as it is finite; the payoffs of the unrestricted
family, which `brownianValueBall_le_brownianValueCube` asks to be bounded, play no role. -/
theorem brownianValueBall_le_brownianValueCube_of_bddAbove_cube
    (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A L : ℝ) (hT : 0 ≤ T) (hAL : A ≤ L) (u : Space d)
    (hbdd : BddAbove (cubeStoppingPayoffs B P h T L u)) :
    brownianValueBall B P h T A u ≤ brownianValueCube B P h T L u := by
  unfold brownianValueBall brownianValueCube
  have hdisc : brownianDiscountBall B P h T A u ≤ brownianDiscountCube B P h T L u :=
    csSup_le (ballStoppingPayoffs_nonempty B P h T A hT u) fun _a ha =>
      le_csSup hbdd (ballStoppingPayoffs_subset_cube B P h T A L hAL u ha)
  linarith

open scoped Pointwise in
/-- The cube payoffs of a multiple of the reward are the same multiple of the cube payoffs. -/
theorem cubeStoppingPayoffs_const_mul (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L : ℝ) (u : Space d) (c : ℝ) :
    cubeStoppingPayoffs B P (fun t y => c * h t y) T L u = c • cubeStoppingPayoffs B P h T L u := by
  have hint : ∀ τ : ΩB → ℝ≥0,
      ∫ ω, -(c * h (T - τ ω) (B (τ ω) ω)) ∂P = c * ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P := by
    intro τ
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  ext a
  constructor
  · rintro ⟨τ, hτ, hb, hcube, rfl⟩
    exact ⟨∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P, ⟨τ, hτ, hb, hcube, rfl⟩, (hint τ).symm⟩
  · rintro ⟨b, ⟨τ, hτ, hb, hcube, rfl⟩, rfl⟩
    exact ⟨τ, hτ, hb, hcube, (hint τ).symm⟩

/-- **The cube-killed value is positively homogeneous in the reward**: the multiplier passes
through the supremum.  This is the identity behind the sentence of `rem:dlt4-killed-scaling`
that the limit is `ν` times the value for unit-variance scenery, since the Gaussian potential
of variance `ν²` is `ν` times the one of unit variance. -/
theorem brownianValueCube_const_mul (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L : ℝ) (u : Space d) (c : ℝ) (hc : 0 ≤ c) :
    brownianValueCube B P (fun t y => c * h t y) T L u = c * brownianValueCube B P h T L u := by
  rw [brownianValueCube_eq, brownianValueCube_eq, brownianDiscountCube_eq_sSup,
    brownianDiscountCube_eq_sSup, cubeStoppingPayoffs_const_mul, Real.sSup_smul_of_nonneg hc,
    smul_eq_mul]
  ring

end Sandpile.Continuum

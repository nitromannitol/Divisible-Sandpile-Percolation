/-
**The Lipschitz step of Step 2** (`sandpile.tex:5111-5126`): "Raising `b` to `b+s` shifts
`\zeta(z)` by `-s\Var(\zeta(0))G(0,z)/\Sigma^2` ... By
\eqref{eq:dgt4-infinite-field-stopping}, the scenery shift then changes `V_\infty(x)-u_r(x)`
by at most `s\,\Cov(V_\infty(x),V_\infty(0))/\Sigma^2`."

At the conditioned level the scenery is `\zeta_s(z)=c(r(z)+s\,e(z))` with
`e=G(0,\cdot)/\|G(0,\cdot)\|` and `c=\sqrt{\Var(\zeta(0))}`, so that the conditioned value is
`V_\infty(0)=c\,s\,\|G(0,\cdot)\|=\Sigma s` and the parameter `s` is the level in units of
`\Sigma`.  Raising `s` by `\delta`, that is raising the conditioned value by `\Sigma\delta`,
shifts the field at a site by the DETERMINISTIC amount
`c\,\delta\,\|G(0,\cdot)\|^{-1}\sum_zG(x,z)G(0,z)
=\Sigma\delta\,\Cov(V_\infty(x),V_\infty(0))/\Sigma^2`, which is the paper's constant per
unit of level.

The optimal-stopping representation `infiniteGreenField_sub_odometer_eq_sInf`
(`eq:dgt4-infinite-field-stopping`) turns that into the same bound for `V_\infty-u_n`: an
infimum over stopping times of two functions whose stopped expectations differ by at most a
constant differs by at most that constant, and the stopped expectation of the shift is at
most its value at the start by `integral_stopped_greenCovariance_le`.
-/
import Sandpile.Support.Dgt4ACovStop
import Sandpile.Support.Dgt4AConditionSite
import Sandpile.Support.Dgt4FieldRecursion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- Two sceneries whose stopped field expectations differ by at most `c` have `V_∞-u_n`
differing by at most `c`. -/
theorem abs_infiniteGreenField_sub_odometer_gap_le (hd : 3 ≤ d) (ξ η : Site d → ℝ)
    (hξ : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m => infiniteGreenFieldPartial m ξ y) atTop (𝓝 L))
    (hη : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m => infiniteGreenFieldPartial m η y) atTop (𝓝 L))
    (n : ℕ) (x : Site d) (c : ℝ)
    (hgap : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      |(∫ X, infiniteGreenField ξ (X (τ X)) ∂(walkLaw d x))
        - ∫ X, infiniteGreenField η (X (τ X)) ∂(walkLaw d x)| ≤ c) :
    |(infiniteGreenField ξ x - odometerOf ξ n x)
      - (infiniteGreenField η x - odometerOf η n x)| ≤ c := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  have hkey : ∀ a b : Site d → ℝ,
      (∀ y : Site d, ∃ L : ℝ,
        Tendsto (fun m => infiniteGreenFieldPartial m a y) atTop (𝓝 L)) →
      (∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
        (∫ X, infiniteGreenField a (X (τ X)) ∂(walkLaw d x))
          ≤ (∫ X, infiniteGreenField b (X (τ X)) ∂(walkLaw d x)) + c) →
      sInf {t : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
          t = ∫ X, infiniteGreenField a (X (τ X)) ∂(walkLaw d x)}
        ≤ sInf {t : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
          t = ∫ X, infiniteGreenField b (X (τ X)) ∂(walkLaw d x)} + c := by
    intro a b _ hper
    rw [← sub_le_iff_le_add]
    refine le_csInf ⟨_, ⟨fun _ => 0, isWalkStopping_zero, fun _ => Nat.zero_le n, rfl⟩⟩ ?_
    rintro t ⟨τ, hτ, hτn, rfl⟩
    have h1 := csInf_le (bddBelow_stoppedField hd1 a x n)
      (show (∫ X, infiniteGreenField a (X (τ X)) ∂(walkLaw d x)) ∈ _ from ⟨τ, hτ, hτn, rfl⟩)
    have h2 := hper τ hτ hτn
    linarith
  rw [infiniteGreenField_sub_odometer_eq_sInf hd ξ hξ n x,
    infiniteGreenField_sub_odometer_eq_sInf hd η hη n x, abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · have := hkey ξ η hξ fun τ hτ hτn => by
      have h := abs_le.mp (hgap τ hτ hτn)
      linarith [h.2]
    linarith
  · have := hkey η ξ hη fun τ hτ hτn => by
      have h := abs_le.mp (hgap τ hτ hτn)
      linarith [h.1]
    linarith

/-- The scenery conditioned at level `s`: `\zeta_s(z)=c(r(z)+s\,e(z))`. -/
noncomputable def condScenery (d : ℕ) (hd : 5 ≤ d) (c : ℝ) (r : Site d → ℝ) (s : ℝ) :
    Site d → ℝ := fun z => c * (r z + s * (greenUnit d hd : Site d → ℝ) z)

theorem condScenery_apply (hd : 5 ≤ d) (c : ℝ) (r : Site d → ℝ) (s : ℝ) (z : Site d) :
    condScenery d hd c r s z = c * (r z + s * (greenUnit d hd : Site d → ℝ) z) := rfl

theorem condScenery_eq (hd : 5 ≤ d) (c : ℝ) (r : Site d → ℝ) (s : ℝ) :
    condScenery d hd c r s = fun z => c * (r z + s * (greenUnit d hd : Site d → ℝ) z) := rfl

/-- The box partial sums of the conditioned scenery converge. -/
theorem tendsto_infiniteGreenFieldPartial_shift (hd : 5 ≤ d) (c : ℝ) (x : Site d)
    {r : Site d → ℝ} {L : ℝ}
    (hr : Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n, green d x z * r z) atTop (𝓝 L))
    (s : ℝ) :
    Tendsto (fun n : ℕ => infiniteGreenFieldPartial n (condScenery d hd c r s) x) atTop
      (𝓝 (c * L + c * s * (‖greenLp d hd (0 : Site d)‖⁻¹
        * ∑' z : Site d, green d x z * green d 0 z))) := by
  have hsum : ∀ n : ℕ,
      infiniteGreenFieldPartial n (condScenery d hd c r s) x
        = c * (∑ z ∈ boxFinset (0 : Site d) n, green d x z * r z)
          + c * s * ∑ z ∈ boxFinset (0 : Site d) n,
            green d x z * (greenUnit d hd : Site d → ℝ) z := by
    intro n
    rw [infiniteGreenFieldPartial_boxFinset_site, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by rw [condScenery_apply]; ring
  simp only [hsum]
  exact (hr.const_mul c).add
    ((tendsto_greenPartialSum_greenUnit_site hd x).const_mul (c * s))

/-- The conditioned scenery has a Green field at every site. -/
theorem exists_tendsto_infiniteGreenFieldPartial_shift (hd : 5 ≤ d) (c : ℝ) {r : Site d → ℝ}
    (hr : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m : ℕ => ∑ z ∈ boxFinset (0 : Site d) m, green d y z * r z) atTop (𝓝 L))
    (s : ℝ) (y : Site d) :
    ∃ M : ℝ, Tendsto (fun m : ℕ => infiniteGreenFieldPartial m (condScenery d hd c r s) y)
      atTop (𝓝 M) :=
  ⟨_, tendsto_infiniteGreenFieldPartial_shift hd c y (hr y).choose_spec s⟩

/-- **Raising the conditioned level shifts the field by a deterministic multiple of the Green
covariance** (`sandpile.tex:5106-5109`). -/
theorem infiniteGreenField_condScenery_sub (hd : 5 ≤ d) (c : ℝ) (y : Site d) {r : Site d → ℝ}
    (hr : ∃ L : ℝ,
      Tendsto (fun m : ℕ => ∑ z ∈ boxFinset (0 : Site d) m, green d y z * r z) atTop (𝓝 L))
    (s δ : ℝ) :
    infiniteGreenField (condScenery d hd c r (s + δ)) y
        - infiniteGreenField (condScenery d hd c r s) y
      = c * δ * ‖greenLp d hd (0 : Site d)‖⁻¹
        * ∑' z : Site d, green d y z * green d 0 z := by
  obtain ⟨L, hL⟩ := hr
  rw [condScenery_eq, condScenery_eq, infiniteGreenField_shift_eq_site hd c y hL (s + δ),
    infiniteGreenField_shift_eq_site hd c y hL s]
  ring

/-- The stopped expectations of the two conditioned fields differ by at most
`|c\delta|\,\Cov(V_\infty(x),V_\infty(0))/\|G(0,\cdot)\|`, by optional stopping for the
superharmonic covariance. -/
theorem abs_integral_stopped_condScenery_sub_le (hd : 5 ≤ d) (c : ℝ) (x : Site d) (n : ℕ)
    {r : Site d → ℝ}
    (hr : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m : ℕ => ∑ z ∈ boxFinset (0 : Site d) m, green d y z * r z) atTop (𝓝 L))
    (s δ : ℝ) {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτn : ∀ X, τ X ≤ n) :
    |(∫ X, infiniteGreenField (condScenery d hd c r (s + δ)) (X (τ X)) ∂(walkLaw d x))
      - ∫ X, infiniteGreenField (condScenery d hd c r s) (X (τ X)) ∂(walkLaw d x)|
      ≤ |c * δ| * (‖greenLp d hd (0 : Site d)‖⁻¹
        * ∑' z : Site d, green d x z * green d 0 z) := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  have hint1 := integrable_stopped_value hd1 x n
    (fun _ => infiniteGreenField (condScenery d hd c r (s + δ))) hτ hτn
  have hint2 := integrable_stopped_value hd1 x n
    (fun _ => infiniteGreenField (condScenery d hd c r s)) hτ hτn
  rw [← integral_sub hint1 hint2]
  have hpt : ∀ X : ℕ → Site d,
      infiniteGreenField (condScenery d hd c r (s + δ)) (X (τ X))
          - infiniteGreenField (condScenery d hd c r s) (X (τ X))
        = (c * δ * ‖greenLp d hd (0 : Site d)‖⁻¹)
          * ∑' z : Site d, green d (X (τ X)) z * green d 0 z := by
    intro X
    rw [infiniteGreenField_condScenery_sub hd c (X (τ X)) (hr _) s δ]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  obtain ⟨hlo, hhi⟩ := integral_stopped_greenCovariance_le hd x n hτ hτn
  have hgpos : (0 : ℝ) < ‖greenLp d hd (0 : Site d)‖⁻¹ := inv_pos.mpr (norm_greenLp_pos hd)
  rw [abs_mul, abs_mul, abs_of_pos hgpos,
    abs_of_nonneg hlo]
  have hcd : (0 : ℝ) ≤ |c * δ| := abs_nonneg _
  have hstep : ‖greenLp d hd (0 : Site d)‖⁻¹ *
      (∫ X, (∑' z : Site d, green d (X (τ X)) z * green d 0 z) ∂walkLaw d x)
      ≤ ‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' z : Site d, green d x z * green d 0 z :=
    mul_le_mul_of_nonneg_left hhi hgpos.le
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hstep hcd

/-- **The Lipschitz bound of Step 2** (`sandpile.tex:5117-5119`): raising the conditioned
level by `\delta` changes `V_\infty(x)-u_n(x)` by at most
`|\delta|\Cov(V_\infty(x),V_\infty(0))/\Sigma`, here in the normalisation
`\Sigma=c\|G(0,\cdot)\|`. -/
theorem abs_condScenery_sub_odometer_le (hd : 5 ≤ d) (c : ℝ) (x : Site d) (n : ℕ)
    {r : Site d → ℝ}
    (hr : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m : ℕ => ∑ z ∈ boxFinset (0 : Site d) m, green d y z * r z) atTop (𝓝 L))
    (s δ : ℝ) :
    |(infiniteGreenField (condScenery d hd c r (s + δ)) x
          - odometerOf (condScenery d hd c r (s + δ)) n x)
        - (infiniteGreenField (condScenery d hd c r s) x
          - odometerOf (condScenery d hd c r s) n x)|
      ≤ |c * δ| * (‖greenLp d hd (0 : Site d)‖⁻¹
        * ∑' z : Site d, green d x z * green d 0 z) :=
  abs_infiniteGreenField_sub_odometer_gap_le (by omega) _ _
    (exists_tendsto_infiniteGreenFieldPartial_shift hd c hr (s + δ))
    (exists_tendsto_infiniteGreenFieldPartial_shift hd c hr s) n x _
    fun τ hτ hτn => abs_integral_stopped_condScenery_sub_le hd c x n hr s δ hτ hτn

end Sandpile

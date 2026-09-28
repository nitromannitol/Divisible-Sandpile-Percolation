import Sandpile.Support.Odometer
import Sandpile.Law

/-!
# The Mass Shift of Theorem 1.1

The mass shift of the proof of Theorem 1.1 (`sandpile.tex:317-342`).  The proof
of `thm:main-nontriviality` from `thm:main-critical-level-percolation` raises
every mass by `1-ρ`,

  `σ̂^{(ρ)}(x) = σ^{(ρ)}(x) + (1-ρ)`,

so that "the shifted field has mean one and the same fluctuations about its
mean".  This module is that sentence: the law of the shifted field, its mean,
its variance and its centred exponential moment, together with the comparison of
the two odometers,

  `0 ≤ û_t(x) - u_t(x) ≤ (1-ρ)t/(2d)`,

which is the display at `sandpile.tex:327-329`.

The odometer comparison is an induction on the recursion
`u_{t+1} = (relax σ u_t)`.  Raising `σ` by `2db` raises the numerator of one
relaxation step by `2db` plus `2d` times the increment already accumulated in
the neighbour sum, so the increment grows by exactly `b` per step; the positive
part only helps, because `max 0 (A + c) ≤ max 0 A + c` for `c ≥ 0`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile.Support

open Sandpile LatticeProb

variable {d : ℕ}

/-! ### The two odometer comparisons -/

/-- A neighbour sum increases by at most `2d c` when the field does. -/
theorem nbrSum_add_const_le {u v : Site d → ℝ} (c : ℝ) (h : ∀ y, u y ≤ v y + c)
    (x : Site d) : nbrSum u x ≤ nbrSum v x + 2 * (d : ℝ) * c := by
  classical
  have hstep : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      u (x + unit i) + u (x - unit i)
        ≤ (v (x + unit i) + v (x - unit i)) + 2 * c := by
    intro i _
    have h1 := h (x + unit i)
    have h2 := h (x - unit i)
    linarith
  have hsum := Finset.sum_le_sum hstep
  have hsplit : (∑ _i : Fin d, (2 : ℝ) * c) = 2 * (d : ℝ) * c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
    ring
  have hdist : (∑ i : Fin d, ((v (x + unit i) + v (x - unit i)) + 2 * c))
      = (∑ i : Fin d, (v (x + unit i) + v (x - unit i))) + ∑ _i : Fin d, (2 : ℝ) * c :=
    Finset.sum_add_distrib
  show (∑ i : Fin d, (u (x + unit i) + u (x - unit i)))
      ≤ (∑ i : Fin d, (v (x + unit i) + v (x - unit i))) + 2 * (d : ℝ) * c
  rw [hdist, hsplit] at hsum
  exact hsum

/-- One relaxation step is monotone in the mass field as well as in the
odometer. -/
theorem relax_mono_mass {σ σ' u v : Site d → ℝ} (hσ : ∀ y, σ y ≤ σ' y)
    (h : ∀ y, u y ≤ v y) (x : Site d) : relax σ u x ≤ relax σ' v x := by
  unfold relax
  refine max_le_max le_rfl ?_
  have h1 : σ x - 1 + nbrSum u x ≤ σ' x - 1 + nbrSum v x := by
    have hx := hσ x
    have hn := nbrSum_mono h x
    linarith
  exact div_le_div_of_nonneg_right h1 (by positivity)

/-- **The odometer is monotone in the mass field.**  This is the left half of
the display at `sandpile.tex:327-329`. -/
theorem odometer_mono_mass {σ σ' : Site d → ℝ} (hσ : ∀ y, σ y ≤ σ' y) :
    ∀ (t : ℕ) (x : Site d), odometer σ t x ≤ odometer σ' t x := by
  intro t
  induction t with
  | zero => intro x; simp [odometer]
  | succ n ih => intro x; exact relax_mono_mass hσ ih x

/-- **Raising every mass by `2db` raises the odometer at time `t` by at most
`tb`.**  This is the right half of the display at `sandpile.tex:327-329`, in the
form in which the induction runs: the paper's bound `(1-ρ)t/(2d)` is the case
`2db = 1-ρ`. -/
theorem odometer_add_const_le (hd : 1 ≤ d) (σ : Site d → ℝ) (b : ℝ) (hb : 0 ≤ b) :
    ∀ (t : ℕ) (x : Site d),
      odometer (fun y => σ y + 2 * (d : ℝ) * b) t x ≤ odometer σ t x + t * b := by
  have hd0 : (0 : ℝ) < 2 * (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  intro t
  induction t with
  | zero => intro x; simp [odometer]
  | succ n ih =>
    intro x
    have hnb : nbrSum (odometer (fun y => σ y + 2 * (d : ℝ) * b) n) x
        ≤ nbrSum (odometer σ n) x + 2 * (d : ℝ) * ((n : ℝ) * b) :=
      nbrSum_add_const_le ((n : ℝ) * b) (fun y => ih y) x
    have hmax := le_max_left (0 : ℝ) ((σ x - 1 + nbrSum (odometer σ n) x) / (2 * (d : ℝ)))
    have hmax2 := le_max_right (0 : ℝ) ((σ x - 1 + nbrSum (odometer σ n) x) / (2 * (d : ℝ)))
    have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1) * b := by positivity
    have hkey : ((σ x + 2 * (d : ℝ) * b) - 1
          + nbrSum (odometer (fun y => σ y + 2 * (d : ℝ) * b) n) x) / (2 * (d : ℝ))
        ≤ (σ x - 1 + nbrSum (odometer σ n) x) / (2 * (d : ℝ)) + ((n : ℝ) + 1) * b := by
      rw [div_add' _ _ _ (ne_of_gt hd0), div_le_div_iff_of_pos_right hd0]
      nlinarith [hnb]
    show max 0 (((fun y => σ y + 2 * (d : ℝ) * b) x - 1
          + nbrSum (odometer (fun y => σ y + 2 * (d : ℝ) * b) n) x) / (2 * (d : ℝ)))
        ≤ max 0 ((σ x - 1 + nbrSum (odometer σ n) x) / (2 * (d : ℝ))) + ((n : ℕ) + 1 : ℕ) * b
    simp only []
    push_cast
    refine max_le (by linarith) (by linarith)

/-- **The display of `sandpile.tex:327-329`**: `0 ≤ û_t(x) - u_t(x) ≤ (1-ρ)t/(2d)`,
here for a general nonnegative shift `a` of every mass. -/
theorem odometer_shift_bounds (hd : 1 ≤ d) (σ : Site d → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (t : ℕ) (x : Site d) :
    0 ≤ odometer (fun y => σ y + a) t x - odometer σ t x ∧
      odometer (fun y => σ y + a) t x - odometer σ t x ≤ a * t / (2 * (d : ℝ)) := by
  have hdpos : (0 : ℝ) < 2 * (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hb : (0 : ℝ) ≤ a / (2 * (d : ℝ)) := by positivity
  have hfun : (fun y => σ y + 2 * (d : ℝ) * (a / (2 * (d : ℝ)))) = fun y => σ y + a := by
    funext y
    field_simp
  have hup := odometer_add_const_le hd σ (a / (2 * (d : ℝ))) hb t x
  rw [hfun] at hup
  have hlow := odometer_mono_mass (σ := σ) (σ' := fun y => σ y + a) (fun y => by linarith) t x
  refine ⟨by linarith, ?_⟩
  have hrw : (t : ℝ) * (a / (2 * (d : ℝ))) = a * (t : ℝ) / (2 * (d : ℝ)) := by ring
  linarith [hup, hrw]

/-! ### The law of the shifted field -/

/-- **The i.i.d. mass law of the shifted field.**  Raising every coordinate by
`a` pushes the i.i.d. law of `μ` forward to the i.i.d. law of the shift of
`μ`. -/
theorem massLaw_map_add_const (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) :
    (Sandpile.massLaw d μ).map (fun (σ : Site d → ℝ) (i : Site d) => σ i + a)
      = Sandpile.massLaw d (μ.map fun s => s + a) := by
  unfold Sandpile.massLaw LatticeProb.iidLaw
  exact MeasureTheory.Measure.infinitePi_map_pi (μ := fun _ : Site d => μ)
    (fun _ => measurable_add_const a)

/-- The mean of the shifted law. -/
theorem integral_id_map_add_const (m : Measure ℝ) [IsProbabilityMeasure m] (a : ℝ)
    (hint : Integrable (id : ℝ → ℝ) m) :
    ∫ s, s ∂(m.map fun s => s + a) = (∫ s, s ∂m) + a := by
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  have h : ∫ x : ℝ, (x + a) ∂m = (∫ x : ℝ, x ∂m) + ∫ _x : ℝ, a ∂m :=
    MeasureTheory.integral_add hint (MeasureTheory.integrable_const a)
  rw [h, MeasureTheory.integral_const]
  simp

/-- The variance of the shifted law is the variance of the law. -/
theorem evariance_id_map_add_const (m : Measure ℝ) [IsProbabilityMeasure m] (a : ℝ)
    (hint : Integrable (id : ℝ → ℝ) m) :
    evariance (id : ℝ → ℝ) (m.map fun s => s + a) = evariance (id : ℝ → ℝ) m := by
  have hmean := integral_id_map_add_const m a hint
  rw [evariance_eq_lintegral_ofReal, evariance_eq_lintegral_ofReal]
  simp only [id_eq] at hmean ⊢
  rw [hmean, MeasureTheory.lintegral_map (by fun_prop) (measurable_add_const a)]
  refine lintegral_congr fun x => ?_
  congr 1
  ring

/-- The centred exponential moment of the shifted law is the exponential moment
of the law centred at its own mean. -/
theorem integral_exp_map_add_const (m : Measure ℝ) [IsProbabilityMeasure m] (θ ρ : ℝ) :
    ∫ s, Real.exp (θ * |s - 1|) ∂(m.map fun s => s + (1 - ρ))
      = ∫ s, Real.exp (θ * |s - ρ|) ∂m := by
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [show x + (1 - ρ) - 1 = x - ρ from by ring]

/-- Integrability of the centred exponential transfers to the shifted law. -/
theorem integrable_exp_map_add_const (m : Measure ℝ) [IsProbabilityMeasure m] (θ ρ : ℝ)
    (hint : Integrable (fun s => Real.exp (θ * |s - ρ|)) m) :
    Integrable (fun s => Real.exp (θ * |s - 1|)) (m.map fun s => s + (1 - ρ)) := by
  rw [MeasureTheory.integrable_map_measure (by fun_prop) (by fun_prop)]
  refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply]
  rw [show x + (1 - ρ) - 1 = x - ρ by ring]

/-- A law with an exponential moment centred at `ρ` has an integrable identity. -/
theorem integrable_id_of_exp_moment_at (m : Measure ℝ) [IsProbabilityMeasure m]
    (θ ρ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun s => Real.exp (θ * |s - ρ|)) m) :
    Integrable (id : ℝ → ℝ) m := by
  have hsub : Integrable (fun s : ℝ => s - ρ) m := by
    refine (hexp.const_mul (1 / θ)).mono' (by fun_prop)
      (Filter.Eventually.of_forall fun s => ?_)
    have h1 : θ * |s - ρ| ≤ Real.exp (θ * |s - ρ|) := by
      have := Real.add_one_le_exp (θ * |s - ρ|)
      linarith
    rw [Real.norm_eq_abs,
      show (1 : ℝ) / θ * Real.exp (θ * |s - ρ|) = Real.exp (θ * |s - ρ|) / θ by ring,
      le_div_iff₀ hθ]
    nlinarith [h1]
  refine (hsub.add (MeasureTheory.integrable_const ρ)).congr
    (Filter.Eventually.of_forall fun s => ?_)
  simp

end Sandpile.Support

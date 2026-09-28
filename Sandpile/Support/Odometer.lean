import Sandpile.Walk

/-!
# Elementary properties of the odometer

Basic facts about the odometer of `Sandpile/Basic.lean`: it is nonnegative, nondecreasing in
time, monotone in the mass field, and its recursion is the one `sandpile.tex` writes in the
scenery variable.
-/

namespace Sandpile

variable {d : ℕ}

/-- The neighbour sum is monotone. -/
theorem nbrSum_mono {u v : Site d → ℝ} (h : ∀ y, u y ≤ v y) (x : Site d) :
    nbrSum u x ≤ nbrSum v x :=
  Finset.sum_le_sum fun _ _ => add_le_add (h _) (h _)

/-- One relaxation step, written in the scenery `ζ = (σ - 1)/(2d)`. -/
theorem relax_eq_scenery (σ u : Site d → ℝ) (x : Site d) :
    relax σ u x = max 0 (scenery d σ x + avg u x) := by
  unfold relax scenery avg LatticeProb.walkOp
  rw [add_div]

/-- The odometer is nonnegative. -/
theorem odometer_nonneg (σ : Site d → ℝ) (t : ℕ) (x : Site d) :
    0 ≤ odometer σ t x := by
  cases t with
  | zero => simp [odometer]
  | succ n => exact le_max_left _ _

/-- The odometer written in the scenery is nonnegative. -/
theorem odometerOf_nonneg (ζ : Site d → ℝ) (t : ℕ) (x : Site d) :
    0 ≤ odometerOf ζ t x := by
  cases t with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

/-- The neighbour average of a nonnegative field is nonnegative. -/
theorem avg_nonneg {f : Site d → ℝ} (hf : ∀ y, 0 ≤ f y) (x : Site d) : 0 ≤ avg f x := by
  show (0:ℝ) ≤ (∑ i : Fin d, (f (x + unit i) + f (x - unit i))) / (2 * (d : ℝ))
  refine div_nonneg (Finset.sum_nonneg fun i _ => add_nonneg (hf _) (hf _)) ?_
  positivity

/-- One relaxation step is monotone in its second argument. -/
theorem relax_mono (σ : Site d → ℝ) {u v : Site d → ℝ} (h : ∀ y, u y ≤ v y)
    (x : Site d) : relax σ u x ≤ relax σ v x := by
  unfold relax
  refine max_le_max le_rfl ?_
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp
  · have hc : (0 : ℝ) < 2 * (d : ℝ) := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
      linarith
    gcongr
    exact nbrSum_mono h x

/-- The odometer is nondecreasing in time. -/
theorem odometer_le_succ (σ : Site d → ℝ) :
    ∀ (t : ℕ) (x : Site d), odometer σ t x ≤ odometer σ (t + 1) x := by
  intro t
  induction t with
  | zero => intro x; exact odometer_nonneg _ _ _
  | succ n ih => intro x; exact relax_mono σ ih x

/-- The odometer is monotone in time. -/
theorem odometer_mono (σ : Site d → ℝ) (x : Site d) :
    Monotone fun t => odometer σ t x :=
  monotone_nat_of_le_succ fun t => odometer_le_succ σ t x

/-- The odometer limit is the supremum of an increasing sequence, so it is
approached from below at every site. -/
theorem le_odometerLimit (σ : Site d → ℝ) (t : ℕ) (x : Site d) :
    ENNReal.ofReal (odometer σ t x) ≤ odometerLimit σ x :=
  le_iSup (fun t : ℕ => ENNReal.ofReal (odometer σ t x)) t

end Sandpile

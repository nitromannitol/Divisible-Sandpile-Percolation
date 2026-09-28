import Sandpile.Support.HeatPotentialDefs
import Sandpile.Frozen.DifferenceRepresentation
import Sandpile.External.BPSHProved
import Sandpile.Support.Membrane
import Sandpile.Support.Walk

/-!
# The exact identity of the parabolic-scale rescaling

The exact identity of the proof of Theorem 1.3(i)(b) at the parabolic scale
(`sandpile.tex:1881-1890`), and the two facts about optimal-stopping values it is
read through.

The proof of Theorem 1.3(i)(b) starts from the exact identity for `u_t - V_t`
(`thm:difference-representation`), rescaled: with `t_R = ⌊R^2T⌋` and
`x_R = ⌊Rx⌋`,

  `𝒰_R(T,x) = Z_R^{lin}(t_R/R^2, x_R/R)
              + sup_{τ ≤ t_R} E_{x_R}[ -Z_R^{lin}((t_R-τ)/R^2, X_τ/R) ]`.

Both sides of that display are the values of the FIELD `Z_R` at mesh points of
`R^{-2}ℤ_+ × R^{-1}ℤ^d`, so the identity is proved here in the mesh vocabulary
`Sandpile.Frozen.HeatPotentialInvariance.meshValue` of
`prop:dlt4-heat-potential-invariance`, and `linInterp_of_mesh` says that the
interpolated field `Z_R^{lin}` of that proposition returns `Z_R` at those mesh
points, which is how the identity meets the proposition.

Two facts carry the rescaling.  The optimal-stopping value is positively
homogeneous in the reward (`stoppingSup_const_mul`), which is what lets the scale
factor `R^{d/2-2}` pass through the supremum; and two values built from rewards
whose payoffs differ by at most `E` differ by at most `E`
(`abs_stoppingSup_sub_le`), which is the form in which the cutoff error of
`sandpile.tex:1908-1921` is paid.
-/

open MeasureTheory
open scoped Pointwise

namespace Sandpile

variable {d : ℕ}

/-- The optimal-stopping value is positively homogeneous in the reward: the scale factor
of the parabolic rescaling passes through the supremum. -/
theorem stoppingSup_const_mul (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (x : Site d)
    (F : ℕ → (ℕ → Site d) → ℝ) :
    stoppingSup n x (fun k X => c * F k X) = c * stoppingSup n x F := by
  have hset : {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      a = ∫ X, c * F (τ X) X ∂(walkLaw d x)}
      = c • {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
        a = ∫ X, F (τ X) X ∂(walkLaw d x)} := by
    ext a
    constructor
    · rintro ⟨τ, hτ, hτn, rfl⟩
      refine ⟨∫ X, F (τ X) X ∂(walkLaw d x), ⟨τ, hτ, hτn, rfl⟩, ?_⟩
      show c * (∫ X, F (τ X) X ∂(walkLaw d x)) = ∫ X, c * F (τ X) X ∂(walkLaw d x)
      rw [MeasureTheory.integral_const_mul]
    · rintro ⟨b, ⟨τ, hτ, hτn, rfl⟩, rfl⟩
      refine ⟨τ, hτ, hτn, ?_⟩
      show c * (∫ X, F (τ X) X ∂(walkLaw d x)) = ∫ X, c * F (τ X) X ∂(walkLaw d x)
      rw [MeasureTheory.integral_const_mul]
  unfold stoppingSup
  rw [hset, Real.sSup_smul_of_nonneg hc, smul_eq_mul]

/-- Two optimal-stopping values built from rewards whose payoffs differ by at most `E`
differ by at most `E`.  This is the shape in which the cutoff error of
`sandpile.tex:1908-1921` is paid: the bound is uniform over stopping times, so it bounds
the gap between the two suprema. -/
theorem abs_stoppingSup_sub_le (n : ℕ) (x : Site d) (F G : ℕ → (ℕ → Site d) → ℝ) (E : ℝ)
    (hbddF : BddAbove {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      a = ∫ X, F (τ X) X ∂(walkLaw d x)})
    (hbddG : BddAbove {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      a = ∫ X, G (τ X) X ∂(walkLaw d x)})
    (hFG : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      |(∫ X, F (τ X) X ∂(walkLaw d x)) - ∫ X, G (τ X) X ∂(walkLaw d x)| ≤ E) :
    |stoppingSup n x F - stoppingSup n x G| ≤ E := by
  rw [abs_sub_le_iff]
  constructor
  · refine sub_le_iff_le_add.2 (csSup_le ⟨_, stoppingSup_mem n x F⟩ ?_)
    rintro a ⟨τ, hτ, hτn, rfl⟩
    have h1 := hFG τ hτ hτn
    rw [abs_sub_le_iff] at h1
    have h2 : (∫ X, G (τ X) X ∂(walkLaw d x)) ≤ stoppingSup n x G :=
      le_csSup hbddG ⟨τ, hτ, hτn, rfl⟩
    linarith [h1.1]
  · refine sub_le_iff_le_add.2 (csSup_le ⟨_, stoppingSup_mem n x G⟩ ?_)
    rintro a ⟨τ, hτ, hτn, rfl⟩
    have h1 := hFG τ hτ hτn
    rw [abs_sub_le_iff] at h1
    have h2 : (∫ X, F (τ X) X ∂(walkLaw d x)) ≤ stoppingSup n x F :=
      le_csSup hbddF ⟨τ, hτ, hτn, rfl⟩
    linarith [h1.2]

/-- `Z_R` at a mesh point is the rescaled membrane field: both are the Green average of
the scenery, and the scale factor is `R^{d/2-2}`. -/
theorem meshValue_eq_membrane (R : ℝ) (ζ : Site d → ℝ) (k : ℕ) (z : Site d) :
    Frozen.HeatPotentialInvariance.meshValue d R ζ k z
      = R ^ ((d : ℝ) / 2 - 2) * membrane ζ k z := by
  simp only [Frozen.HeatPotentialInvariance.meshValue, membrane_eq_greenTime]

/-- At a mesh point of `R^{-2}ℤ_+ × R^{-1}ℤ^d` the interpolated field `Z_R^{lin}` of
`prop:dlt4-heat-potential-invariance` returns `Z_R`: every fractional part vanishes, so
only the corner `ε = 0` of the cell survives and the time weight is `1`. -/
theorem linInterp_of_mesh (R : ℝ) (ζ : Site d → ℝ) (r : ℝ)
    (w : Sandpile.Continuum.Space d) (k : ℕ) (z : Site d)
    (hk : R ^ 2 * r = (k : ℝ)) (hz : ∀ i, R * w i = (z i : ℝ)) :
    Frozen.HeatPotentialInvariance.linInterp d R ζ r w
      = Frozen.HeatPotentialInvariance.meshValue d R ζ k z := by
  classical
  have ha : ⌊R ^ 2 * r⌋₊ = k := by rw [hk]; exact Nat.floor_natCast k
  have hs : R ^ 2 * r - ((k : ℕ) : ℝ) = 0 := by rw [hk]; ring
  have hb : ∀ i, ⌊R * w i⌋ = z i := fun i => by rw [hz i]; exact Int.floor_intCast (z i)
  have ht : ∀ i, R * w i - ((z i : ℤ) : ℝ) = 0 := fun i => by rw [hz i]; ring
  unfold Frozen.HeatPotentialInvariance.linInterp
  rw [Finset.sum_eq_single (fun _ : Fin d => false)]
  · simp [ha, hs, hb, ht, Finset.prod_const_one]
  · intro ε _ hne
    obtain ⟨i, hi⟩ : ∃ i : Fin d, ε i = true := by
      by_contra hall
      exact hne (funext fun i => by simpa using not_exists.mp hall i)
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) ?_) _
    simp [hi, ht i, hb i]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- **The exact identity of `sandpile.tex:1881-1890`**: the rescaled odometer at a lattice
point is the rescaled membrane field there plus the optimal-stopping value of the negated
rescaled field along the walk.  It is `thm:difference-representation` multiplied by
`R^{d/2-2}`, the scale factor passing through the supremum by positive homogeneity. -/
theorem rescaled_difference_representation (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R)
    (ζ : Site d → ℝ) (t : ℕ) (x : Site d) :
    R ^ ((d : ℝ) / 2 - 2) * odometerOf ζ t x
      = Frozen.HeatPotentialInvariance.meshValue d R ζ t x
        + stoppingSup t x
            (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k)) := by
  have hdr := Sandpile.Frozen.difference_representation d hd ζ t x
  have hc : (0 : ℝ) ≤ R ^ ((d : ℝ) / 2 - 2) := (Real.rpow_pos_of_pos hR _).le
  have hfun : (fun (k : ℕ) (X : ℕ → Site d) =>
        -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
      = fun (k : ℕ) (X : ℕ → Site d) =>
        R ^ ((d : ℝ) / 2 - 2) * -(membrane ζ (t - k) (X k)) := by
    funext k X
    rw [meshValue_eq_membrane]
    ring
  rw [hfun, stoppingSup_const_mul _ hc, meshValue_eq_membrane R ζ t x, ← hdr]
  ring

/-- The payoff gap between a reward and its cut-off version is paid by the cutoff error
`E_x[(1 - χ)|F|]`, which is the quantity the display at `sandpile.tex:1908-1921` bounds. -/
theorem abs_integral_sub_cutoff_le (x : Site d) (τ : (ℕ → Site d) → ℕ)
    (F : ℕ → (ℕ → Site d) → ℝ) (χ : ℕ → (ℕ → Site d) → ℝ) (E : ℝ)
    (hχ1 : ∀ k X, χ k X ≤ 1)
    (hF : Integrable (fun X => F (τ X) X) (walkLaw d x))
    (hχF : Integrable (fun X => χ (τ X) X * F (τ X) X) (walkLaw d x))
    (hE : (∫ X, (1 - χ (τ X) X) * |F (τ X) X| ∂(walkLaw d x)) ≤ E) :
    |(∫ X, F (τ X) X ∂(walkLaw d x)) - ∫ X, χ (τ X) X * F (τ X) X ∂(walkLaw d x)| ≤ E := by
  have hdiff : (∫ X, F (τ X) X ∂(walkLaw d x)) - ∫ X, χ (τ X) X * F (τ X) X ∂(walkLaw d x)
      = ∫ X, (1 - χ (τ X) X) * F (τ X) X ∂(walkLaw d x) := by
    rw [← MeasureTheory.integral_sub hF hχF]
    congr 1
    funext X
    ring
  rw [hdiff]
  calc |∫ X, (1 - χ (τ X) X) * F (τ X) X ∂(walkLaw d x)|
      ≤ ∫ X, |(1 - χ (τ X) X) * F (τ X) X| ∂(walkLaw d x) :=
        MeasureTheory.abs_integral_le_integral_abs
    _ = ∫ X, (1 - χ (τ X) X) * |F (τ X) X| ∂(walkLaw d x) := by
        congr 1
        funext X
        rw [abs_mul, abs_of_nonneg (by linarith [hχ1 (τ X) X])]
    _ ≤ E := hE

end Sandpile

import Sandpile.Support.ExplScalingId
import Sandpile.Support.Localization

/-!
# The killed form of the exact difference representation

The exact identity of `rem:dlt4-killed-scaling` (`sandpile.tex:1929-1950`): the cube-killed form,
at the parabolic scale, of the identity the proof of Theorem 1.3(i)(b) starts from
(`sandpile.tex:1881-1890`). The remark reads: "The same proof applies, without change, to the
values killed on exiting the lattice box `Q(⌊Ru⌋,R)`." The first step of that proof is the exact
identity for `u_t - V_t`; its killed form is proved here as `killed_difference_representation`
and, at the parabolic scale, as `rescaled_killed_difference_representation`.

The localized value `u_t^D(x) = sup_{τ≤t} E_x ∑_{k<τ∧τ_D} ζ(X_k)` of `eq:localized-odometer` is a
supremum over all stopping times bounded by `t` of the scenery sum stopped at `τ ∧ τ_D`
(`killedStoppingSup`); since `τ ∧ τ_D` is itself a stopping time bounded by `t` which has not left
`D` strictly before it stops (`stopBeforeExit_eq_self`, `stopBeforeExit_kill`), and since every
such stopping time is its own `τ ∧ τ_D`, that supremum is the supremum over the killed stopping
times, those bounded by `t` which have not left `D` strictly before stopping. The optimal-stopping
identity `E_x S_σ = V_t(x) - E_x V_{t-σ}(X_σ)` of `Sandpile.integral_neg_stoppedMembrane` then
applies to each killed stopping time separately (`killedSet_membrane_eq_image`), and translating a
set of reals translates its supremum.
-/

open MeasureTheory
open scoped Pointwise

namespace Sandpile

variable {d : ℕ}

/-- The payoffs of the killed optimal-stopping problem on `D`: the payoffs of the
stopping times bounded by `n` which have not left `D` strictly before they stop. -/
def killedSet (D : Set (Site d)) (n : ℕ) (x : Site d) (F : ℕ → (ℕ → Site d) → ℝ) : Set ℝ :=
  {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
    (∀ X, ∀ j < τ X, X j ∈ D) ∧ a = ∫ X, F (τ X) X ∂(walkLaw d x)}

/-- The value of the killed optimal-stopping problem on `D`. -/
noncomputable def killedStoppingSup (D : Set (Site d)) (n : ℕ) (x : Site d)
    (F : ℕ → (ℕ → Site d) → ℝ) : ℝ :=
  sSup (killedSet D n x F)

/-- `killedStoppingSup D n x F` unfolds definitionally to `sSup (killedSet D n x F)`. -/
theorem killedStoppingSup_eq_sSup (D : Set (Site d)) (n : ℕ) (x : Site d)
    (F : ℕ → (ℕ → Site d) → ℝ) :
    killedStoppingSup D n x F = sSup (killedSet D n x F) := rfl

/-- The killed payoff set is a subset of the unkilled one. -/
theorem killedSet_subset (D : Set (Site d)) (n : ℕ) (x : Site d)
    (F : ℕ → (ℕ → Site d) → ℝ) :
    killedSet D n x F ⊆ {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧
      (∀ X, τ X ≤ n) ∧ a = ∫ X, F (τ X) X ∂(walkLaw d x)} := by
  rintro a ⟨τ, hτ, hτn, -, rfl⟩
  exact ⟨τ, hτ, hτn, rfl⟩

/-- The killed payoff set is nonempty: `τ = 0` is admissible. -/
theorem killedSet_nonempty (D : Set (Site d)) (n : ℕ) (x : Site d)
    (F : ℕ → (ℕ → Site d) → ℝ) : (killedSet D n x F).Nonempty :=
  ⟨_, ⟨fun _ => 0, isWalkStopping_zero, fun _ => Nat.zero_le n,
    fun X j hj => absurd hj (by simp), rfl⟩⟩

/-- A stopping time which has not left `D` strictly before it stops is its own
`τ ∧ τ_D`. -/
theorem stopBeforeExit_eq_self {D : Set (Site d)} {n : ℕ} {τ : (ℕ → Site d) → ℕ}
    (hτn : ∀ X, τ X ≤ n) (hkill : ∀ X, ∀ j < τ X, X j ∈ D) (X : ℕ → Site d) :
    stopBeforeExit D n τ X = τ X := by
  unfold stopBeforeExit
  refine min_eq_left ?_
  by_contra hc
  have hlt : exitNat D n X < τ X := not_le.mp hc
  have hle : exitNat D n X ≤ n := le_trans hlt.le (hτn X)
  exact (notMem_exitNat hle) (hkill X (exitNat D n X) hlt)

/-- `τ ∧ τ_D` has not left `D` strictly before it stops. -/
theorem stopBeforeExit_kill {D : Set (Site d)} {n : ℕ} {τ : (ℕ → Site d) → ℕ}
    (hτn : ∀ X, τ X ≤ n) (X : ℕ → Site d) (j : ℕ) (hj : j < stopBeforeExit D n τ X) :
    X j ∈ D := by
  unfold stopBeforeExit at hj
  have h1 : j < exitNat D n X := lt_of_lt_of_le hj (min_le_right _ _)
  have h2 : j ≤ n := le_trans (le_of_lt (lt_of_lt_of_le hj (min_le_left _ _))) (hτn X)
  exact mem_of_lt_exitNat h1 h2

/-- **The killed payoff set of the membrane reward is the localized payoff set,
translated by the membrane field**, which is `Sandpile.integral_neg_stoppedMembrane`
applied to each killed stopping time. -/
theorem killedSet_membrane_eq_image (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (n : ℕ) (x : Site d) :
    killedSet D n x (fun k X => -(membrane ζ (n - k) (X k)))
      = (fun a => a - membrane ζ n x) '' localizedSet D ζ n x := by
  ext a
  constructor
  · rintro ⟨σ, hσ, hσn, hkill, rfl⟩
    have hself : ∀ X, stopBeforeExit D n σ X = σ X := stopBeforeExit_eq_self hσn hkill
    refine ⟨∫ X, sceneryPartialSum ζ (stopBeforeExit D n σ X) X ∂(walkLaw d x),
      ⟨σ, hσ, hσn, rfl⟩, ?_⟩
    simp only [hself]
    exact (integral_neg_stoppedMembrane hd x ζ n hσ hσn).symm
  · rintro ⟨b, ⟨τ, hτ, hτn, rfl⟩, rfl⟩
    refine ⟨stopBeforeExit D n τ, isWalkStopping_stopBeforeExit hτ hτn,
      stopBeforeExit_le hτn, stopBeforeExit_kill hτn, ?_⟩
    exact (integral_neg_stoppedMembrane (τ := stopBeforeExit D n τ) hd x ζ n
      (isWalkStopping_stopBeforeExit hτ hτn) (stopBeforeExit_le hτn)).symm

/-- **The killed exact identity**: the localized value minus the membrane field is the
value of the killed optimal-stopping problem at the negated membrane reward.  This is
the killed form of `lem:difference-representation`. -/
theorem killed_difference_representation (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (n : ℕ) (x : Site d) (hx : x ∈ D) :
    localizedOdometer D ζ n x - membrane ζ n x
      = killedStoppingSup D n x (fun k X => -(membrane ζ (n - k) (X k))) := by
  rw [localizedOdometer_eq_sSup D ζ n x hx, killedStoppingSup_eq_sSup,
    killedSet_membrane_eq_image hd D ζ n x,
    sSup_image_sub (localizedSet D ζ n x) (localizedSet_nonempty D ζ n x)
      (bddAbove_localizedSet hd D ζ n x) (membrane ζ n x)]

/-- The killed value is positively homogeneous in the reward. -/
theorem killedStoppingSup_const_mul (D : Set (Site d)) (c : ℝ) (hc : 0 ≤ c) (n : ℕ)
    (x : Site d) (F : ℕ → (ℕ → Site d) → ℝ) :
    killedStoppingSup D n x (fun k X => c * F k X) = c * killedStoppingSup D n x F := by
  have hset : killedSet D n x (fun k X => c * F k X) = c • killedSet D n x F := by
    ext a
    constructor
    · rintro ⟨τ, hτ, hτn, hkill, rfl⟩
      refine ⟨∫ X, F (τ X) X ∂(walkLaw d x), ⟨τ, hτ, hτn, hkill, rfl⟩, ?_⟩
      show c * (∫ X, F (τ X) X ∂(walkLaw d x)) = ∫ X, c * F (τ X) X ∂(walkLaw d x)
      rw [MeasureTheory.integral_const_mul]
    · rintro ⟨b, ⟨τ, hτ, hτn, hkill, rfl⟩, rfl⟩
      refine ⟨τ, hτ, hτn, hkill, ?_⟩
      show c * (∫ X, F (τ X) X ∂(walkLaw d x)) = ∫ X, c * F (τ X) X ∂(walkLaw d x)
      rw [MeasureTheory.integral_const_mul]
  unfold killedStoppingSup
  rw [hset, Real.sSup_smul_of_nonneg hc, smul_eq_mul]

/-- **The killed exact identity at the parabolic scale** (`sandpile.tex:1881-1890` in its
killed form): the rescaled localized value at a lattice point is the rescaled field there
plus the killed optimal-stopping value of the negated rescaled field along the walk. -/
theorem rescaled_killed_difference_representation (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R)
    (D : Set (Site d)) (ζ : Site d → ℝ) (n : ℕ) (x : Site d) (hx : x ∈ D) :
    R ^ ((d : ℝ) / 2 - 2) * localizedOdometer D ζ n x
      = Frozen.HeatPotentialInvariance.meshValue d R ζ n x
        + killedStoppingSup D n x
            (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (n - k) (X k)) := by
  have hc : (0 : ℝ) ≤ R ^ ((d : ℝ) / 2 - 2) := (Real.rpow_pos_of_pos hR _).le
  have hfun : (fun (k : ℕ) (X : ℕ → Site d) =>
        -Frozen.HeatPotentialInvariance.meshValue d R ζ (n - k) (X k))
      = fun (k : ℕ) (X : ℕ → Site d) =>
        R ^ ((d : ℝ) / 2 - 2) * -(membrane ζ (n - k) (X k)) := by
    funext k X
    rw [meshValue_eq_membrane]
    ring
  rw [hfun, killedStoppingSup_const_mul D _ hc n x, meshValue_eq_membrane R ζ n x,
    ← killed_difference_representation hd D ζ n x hx]
  ring

end Sandpile

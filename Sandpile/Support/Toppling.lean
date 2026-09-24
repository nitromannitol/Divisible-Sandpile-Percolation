/-
The parallel toppling dynamics of `sandpile.tex`, Section 2 (`sandpile.tex:802-816`).

The paper fixes an initial configuration `σ`, lets `σ_n` be the mass field after `n`
rounds in which every site topples in parallel, and lets `u_n(x)` be the mass sent
from `x` to each neighbour up to that time:

  `σ_0 = σ`,   `u_0 = 0`,
  `u_{n+1}(x) = u_n(x) + (σ_n(x) - 1)₊ / (2d)`                   (`eq:u-update`),
  `σ_{n+1}   = σ_n + Δ[(σ_n - 1)₊ / (2d)]`                       (`eq:sigma-update`),

with `a₊ = max(a, 0)` and `Δ` the graph Laplacian.  This file defines that pair of
sequences and proves the facts `lem:recursion` uses.

How the paper's objects are modelled here:

- `laplacian f x = ∑_{y ∼ x} (f(y) - f(x))` is `nbrSum f x - 2d f(x)`: the `2d`
  neighbours of `x` are counted with multiplicity by direction, as in `nbrSum`.
- `topplingStep d` is one round `(σ_n, u_n) ↦ (σ_{n+1}, u_{n+1})` on pairs of fields,
  the first component `eq:sigma-update` and the second `eq:u-update`.  A single
  recursion returns the pair because the two equations feed each other.
  `topplingPair d σ` iterates it from `(σ, 0)`, and `topplingMass d σ n = σ_n`,
  `topplingOdometer d σ n = u_n` are its two projections.  The four defining
  equations are stated as `@[simp]` lemmas, in the paper's form.
- The dynamics is defined for every `d`.  At `d = 0` the divisions by `2d` take the
  junk value `0`, no site ever topples and both sequences are constant; the bridge
  to `Sandpile.odometer` holds there for that reason.  The recursion of
  `lem:recursion` itself carries `1 ≤ d`.
- `topplingMass_eq` is the telescoping `σ_n = σ + Δu_n` of the paper's proof, and
  `min_le_topplingMass_succ`, `one_le_topplingMass_of_pos` are its remark that a site
  keeps mass at least one from its first toppling on.
- `topplingOdometer_recursion` is `lem:recursion` for the toppling odometer, proved as
  the paper proves it, and `topplingOdometer_eq_odometer` identifies the toppling
  odometer with the `Sandpile.odometer` of `Sandpile/Basic.lean`, so that the rest of
  the development, which is written for `Sandpile.odometer`, applies to the dynamics
  the paper starts from.
-/
import Sandpile.Walk

namespace Sandpile

/-- The graph Laplacian `Δf(x) = ∑_{y ∼ x} (f(y) - f(x)) = ∑_{y ∼ x} f(y) - 2d f(x)`. -/
noncomputable def laplacian {d : ℕ} (f : Site d → ℝ) (x : Site d) : ℝ :=
  nbrSum f x - 2 * d * f x

/-- One round of parallel toppling, `(σ_n, u_n) ↦ (σ_{n+1}, u_{n+1})`.  The first
component is `eq:sigma-update`, `σ_{n+1} = σ_n + Δ[(σ_n - 1)₊ / (2d)]`, and the second
is `eq:u-update`, `u_{n+1} = u_n + (σ_n - 1)₊ / (2d)`. -/
noncomputable def topplingStep (d : ℕ) (p : (Site d → ℝ) × (Site d → ℝ)) :
    (Site d → ℝ) × (Site d → ℝ) :=
  (p.1 + laplacian (fun y => max (p.1 y - 1) 0 / (2 * d)),
    p.2 + fun x => max (p.1 x - 1) 0 / (2 * d))

/-- The pair `(σ_n, u_n)` of the toppling dynamics started from the mass field `σ`:
`(σ_0, u_0) = (σ, 0)` and each round is `topplingStep`. -/
noncomputable def topplingPair (d : ℕ) (σ : Site d → ℝ) :
    ℕ → (Site d → ℝ) × (Site d → ℝ)
  | 0 => (σ, 0)
  | n + 1 => topplingStep d (topplingPair d σ n)

/-- The mass field `σ_n` after `n` rounds of parallel toppling. -/
noncomputable def topplingMass (d : ℕ) (σ : Site d → ℝ) (n : ℕ) : Site d → ℝ :=
  (topplingPair d σ n).1

/-- The odometer `u_n` of the toppling dynamics: `u_n(x)` is the mass sent from `x` to
each neighbour during the first `n` rounds. -/
noncomputable def topplingOdometer (d : ℕ) (σ : Site d → ℝ) (n : ℕ) : Site d → ℝ :=
  (topplingPair d σ n).2

variable {d : ℕ}

/-! ### The four defining equations -/

/-- `σ_0 = σ`. -/
@[simp]
theorem topplingMass_zero (σ : Site d → ℝ) : topplingMass d σ 0 = σ := rfl

/-- `u_0 = 0`. -/
@[simp]
theorem topplingOdometer_zero (σ : Site d → ℝ) : topplingOdometer d σ 0 = 0 := rfl

/-- `eq:sigma-update`: `σ_{n+1} = σ_n + Δ[(σ_n - 1)₊ / (2d)]`. -/
@[simp]
theorem topplingMass_succ (σ : Site d → ℝ) (n : ℕ) :
    topplingMass d σ (n + 1) =
      topplingMass d σ n + laplacian (fun y => max (topplingMass d σ n y - 1) 0 / (2 * d)) :=
  rfl

/-- `eq:u-update`: `u_{n+1}(x) = u_n(x) + (σ_n(x) - 1)₊ / (2d)`. -/
@[simp]
theorem topplingOdometer_succ (σ : Site d → ℝ) (n : ℕ) :
    topplingOdometer d σ (n + 1) =
      topplingOdometer d σ n + fun x => max (topplingMass d σ n x - 1) 0 / (2 * d) :=
  rfl

/-! ### The Laplacian -/

/-- The neighbour sum is additive. -/
theorem nbrSum_add (u v : Site d → ℝ) (x : Site d) :
    nbrSum (u + v) x = nbrSum u x + nbrSum v x := by
  unfold nbrSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring

/-- The neighbour sum of the zero field is zero. -/
theorem nbrSum_zero (x : Site d) : nbrSum (0 : Site d → ℝ) x = 0 := by
  simp [nbrSum]

/-- The neighbour sum of a nonnegative field is nonnegative. -/
theorem nbrSum_nonneg {u : Site d → ℝ} (h : ∀ y, 0 ≤ u y) (x : Site d) : 0 ≤ nbrSum u x :=
  Finset.sum_nonneg fun _ _ => add_nonneg (h _) (h _)

/-- The Laplacian is additive. -/
theorem laplacian_add (u v : Site d → ℝ) : laplacian (u + v) = laplacian u + laplacian v := by
  funext x
  simp only [laplacian, nbrSum_add, Pi.add_apply]
  ring

/-- The Laplacian of the zero field is zero. -/
theorem laplacian_zero : laplacian (0 : Site d → ℝ) = 0 := by
  funext x
  simp [laplacian, nbrSum_zero]

/-! ### The paper's proof of `lem:recursion` -/

/-- The mass sent by a site in one round is nonnegative. -/
theorem sent_nonneg (a : ℝ) : 0 ≤ max (a - 1) 0 / (2 * (d : ℝ)) :=
  div_nonneg (le_max_right _ _) (by positivity)

/-- The odometer of the toppling dynamics is nonnegative. -/
theorem topplingOdometer_nonneg (σ : Site d → ℝ) (n : ℕ) (x : Site d) :
    0 ≤ topplingOdometer d σ n x := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [topplingOdometer_succ, Pi.add_apply]
    exact add_nonneg ih (sent_nonneg _)

/-- Telescoping `eq:sigma-update`: `σ_n = σ + Δu_n`. -/
theorem topplingMass_eq (σ : Site d → ℝ) (n : ℕ) :
    topplingMass d σ n = σ + laplacian (topplingOdometer d σ n) := by
  induction n with
  | zero => simp [laplacian_zero]
  | succ n ih =>
    rw [topplingMass_succ, topplingOdometer_succ, laplacian_add, ← add_assoc, ← ih]

/-- A site keeps mass at least one from its first toppling on:
`σ_{m+1}(x) ≥ σ_m(x) - (σ_m(x) - 1)₊ = min {σ_m(x), 1}`. -/
theorem min_le_topplingMass_succ (σ : Site d → ℝ) (m : ℕ) (x : Site d) :
    min (topplingMass d σ m x) 1 ≤ topplingMass d σ (m + 1) x := by
  have hnb : 0 ≤ nbrSum (fun y => max (topplingMass d σ m y - 1) 0 / (2 * (d : ℝ))) x :=
    nbrSum_nonneg (fun y => sent_nonneg _) x
  have hle : 2 * (d : ℝ) * (max (topplingMass d σ m x - 1) 0 / (2 * (d : ℝ))) ≤
      max (topplingMass d σ m x - 1) 0 := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
      rw [mul_div_cancel₀ _ (by positivity)]
  have hmin : min (topplingMass d σ m x) 1 =
      topplingMass d σ m x - max (topplingMass d σ m x - 1) 0 := by
    rcases le_total (topplingMass d σ m x) 1 with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [min_eq_right h, max_eq_left (by linarith)]
      ring
  simp only [topplingMass_succ, Pi.add_apply, laplacian]
  linarith

/-- A site that has sent mass holds mass at least one: `u_n(x) > 0` gives `σ_n(x) ≥ 1`. -/
theorem one_le_topplingMass_of_pos (σ : Site d → ℝ) (n : ℕ) (x : Site d)
    (h : 0 < topplingOdometer d σ n x) : 1 ≤ topplingMass d σ n x := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    have hmin := min_le_topplingMass_succ σ n x
    simp only [topplingOdometer_succ, Pi.add_apply] at h
    by_cases hs : 0 < max (topplingMass d σ n x - 1) 0 / (2 * (d : ℝ))
    · have hpos : 0 < max (topplingMass d σ n x - 1) 0 := by
        by_contra hneg
        exact absurd hs (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg)
          (by positivity)))
      have ha : 1 < topplingMass d σ n x := by
        rcases lt_max_iff.mp hpos with h1 | h1
        · linarith
        · exact absurd h1 (lt_irrefl _)
      rw [min_eq_right ha.le] at hmin
      exact hmin
    · have hu : 0 < topplingOdometer d σ n x := by
        have := sent_nonneg (d := d) (topplingMass d σ n x)
        linarith [not_lt.mp hs]
      have h1 := ih hu
      rw [min_eq_right h1] at hmin
      exact hmin

/-- The recursion of `lem:recursion` for the odometer of the toppling dynamics:
`u_{n+1}(x) = ((2d)⁻¹ ∑_{y ∼ x} u_n(y) + ζ(x))₊`.

Telescoping gives `σ_n = σ + Δu_n`, so `eq:u-update` reads
`u_{n+1} = u_n + (ζ + Pu_n - u_n)₊ = max {u_n, ζ + Pu_n}`.  If `u_n(x) = 0` the maximum
is `(ζ(x) + Pu_n(x))₊`.  If `u_n(x) > 0`, then `x` has toppled and holds mass at least
one, which makes `ζ(x) + Pu_n(x) - u_n(x)` nonnegative and the maximum `ζ(x) + Pu_n(x)`,
which is positive. -/
theorem topplingOdometer_recursion (hd : 1 ≤ d) (σ : Site d → ℝ) (n : ℕ) (x : Site d) :
    topplingOdometer d σ (n + 1) x =
      max 0 ((1 / (2 * (d : ℝ))) * nbrSum (topplingOdometer d σ n) x + scenery d σ x) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hD : (0 : ℝ) < 2 * d := by linarith
  have htel : topplingMass d σ n x =
      σ x + (nbrSum (topplingOdometer d σ n) x - 2 * d * topplingOdometer d σ n x) := by
    have := congrFun (topplingMass_eq σ n) x
    simpa [laplacian] using this
  have hkey : (topplingMass d σ n x - 1) / (2 * d) =
      scenery d σ x + (1 / (2 * (d : ℝ))) * nbrSum (topplingOdometer d σ n) x
        - topplingOdometer d σ n x := by
    rw [htel]
    unfold scenery
    field_simp
    ring
  have hmax : max (topplingMass d σ n x - 1) 0 / (2 * (d : ℝ)) =
      max (scenery d σ x + (1 / (2 * (d : ℝ))) * nbrSum (topplingOdometer d σ n) x
        - topplingOdometer d σ n x) 0 := by
    rw [← hkey, ← max_div_div_right hD.le, zero_div]
  have hpos : 0 < topplingOdometer d σ n x →
      0 ≤ scenery d σ x + (1 / (2 * (d : ℝ))) * nbrSum (topplingOdometer d σ n) x
        - topplingOdometer d σ n x := by
    intro h
    rw [← hkey]
    have := one_le_topplingMass_of_pos σ n x h
    exact div_nonneg (by linarith) hD.le
  have hfin : ∀ u Z : ℝ, 0 ≤ u → (0 < u → 0 ≤ Z - u) → u + max (Z - u) 0 = max 0 Z := by
    intro u Z hu hZ
    rcases hu.eq_or_lt with h0 | hu0
    · subst h0
      simp [max_comm]
    · have h1 := hZ hu0
      rw [max_eq_left h1, max_eq_right (by linarith)]
      ring
  have hsucc : topplingOdometer d σ (n + 1) x =
      topplingOdometer d σ n x + max (topplingMass d σ n x - 1) 0 / (2 * (d : ℝ)) := by
    simp
  rw [hsucc, hmax, add_comm (1 / (2 * (d : ℝ)) * nbrSum (topplingOdometer d σ n) x)]
  exact hfin _ _ (topplingOdometer_nonneg σ n x) hpos

/-- The odometer of the toppling dynamics is the odometer `Sandpile.odometer` of
`Sandpile/Basic.lean`, defined by the recursion `u_{t+1} = relax σ u_t`. -/
theorem topplingOdometer_eq_odometer (d : ℕ) (σ : Site d → ℝ) :
    topplingOdometer d σ = odometer σ := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have hzero : ∀ m : ℕ, odometer σ m x = 0 := by
        intro m
        cases m <;> simp [odometer, relax]
      have := congrFun ih x
      simp only [topplingOdometer_succ, Pi.add_apply]
      simp [this, hzero]
    · rw [topplingOdometer_recursion hd σ n x, ih]
      show _ = relax σ (odometer σ n) x
      unfold relax scenery
      congr 1
      field_simp
      ring

end Sandpile

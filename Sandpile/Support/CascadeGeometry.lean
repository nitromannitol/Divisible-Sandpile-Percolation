import Sandpile.Support.StarCrossings
import Sandpile.Support.CoarseBoxes

/-!
# Separated subcrossings of an annular crossing

Two separated subcrossings extracted from a larger annular crossing. `HasStarAnnularCrossing O x
R` records a `∗`-connected subset of `O`, inside the box of radius `2R` about `x`, that meets
both the inner box of radius `R` and the boundary at radius `2R`. The main result,
`exists_separated_subcrossings`, splits a `HasStarAnnularCrossing O x (64 * R)` witness into two
smaller annular crossings at radius `R`, centered at grid points `x₁, x₂ ∈ coarseCenters x R`
whose radius-`2R` boxes are at distance at least `4R` apart, by rounding the crossing's near and
far endpoints to grid centers (`exists_coarseCenter`) and extracting the two half-crossings
between them (`exists_star_subcrossing`). `hasStarAnnularCrossing_iff_lowCrossing` identifies this
notion with the paper's `Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent` for the sublevel sets
of the odometer.
-/

namespace Sandpile

/-- `O` contains a `∗`-connected subset meeting both the box of radius `R` about `x` and the
boundary at radius `2R`, while staying inside the box of radius `2R`: an annular crossing of
width `R` at scale `x`. -/
def HasStarAnnularCrossing {d : ℕ} (O : Set (Site d)) (x : Site d) (R : ℕ) : Prop :=
  ∃ T : Set (Site d), T ⊆ O ∧ T ⊆ {z | boxDist z x ≤ 2 * R} ∧
    ((starLatticeGraph d).induce T).Connected ∧
    (∃ z ∈ T, boxDist z x ≤ R) ∧ (∃ z ∈ T, boxDist z x = 2 * R)

/-- Splits a `HasStarAnnularCrossing O x (64 * R)` witness into two separated annular crossings
of radius `R`: grid centers `x₁, x₂ ∈ coarseCenters x R`, each carrying a
`HasStarAnnularCrossing O · R` witness, whose radius-`2R` boxes are at distance at least `4R`
apart. Obtained by rounding the original crossing's near and far endpoints to grid centers via
`exists_coarseCenter` and splitting the connected crossing into two half-crossings via
`exists_star_subcrossing`. -/
lemma exists_separated_subcrossings {d : ℕ} (O : Set (Site d)) (x : Site d)
    (R : ℕ) (hR : 1 ≤ R) (h : HasStarAnnularCrossing O x (64 * R)) :
    ∃ x₁ ∈ coarseCenters x R, ∃ x₂ ∈ coarseCenters x R,
      HasStarAnnularCrossing O x₁ R ∧ HasStarAnnularCrossing O x₂ R ∧
      (∀ z₁ : Site d, boxDist z₁ x₁ ≤ 2 * R →
        ∀ z₂ : Site d, boxDist z₂ x₂ ≤ 2 * R → 4 * R ≤ boxDist z₁ z₂) := by
  obtain ⟨T, hTO, _hTbox, hTconn, ⟨a, haT, haR⟩, ⟨b, hbT, hbR⟩⟩ := h
  obtain ⟨x₁, hx₁, ha⟩ := exists_coarseCenter x a R hR (by omega)
  obtain ⟨x₂, hx₂, hb⟩ := exists_coarseCenter x b R hR (by omega)
  have hab : 64 * R ≤ boxDist a b := by
    have htri := boxDist_trans b a x
    rw [boxDist_comm b a] at htri
    omega
  have hbfar : 2 * R < boxDist b x₁ := by
    have htri := boxDist_trans a x₁ b
    rw [boxDist_comm x₁ b] at htri
    omega
  have hafar : 2 * R < boxDist a x₂ := by
    have htri := boxDist_trans a x₂ b
    rw [boxDist_comm x₂ b] at htri
    omega
  obtain ⟨U₁, hU₁T, hU₁box, hU₁conn, hU₁in, hU₁out⟩ :=
    exists_star_subcrossing T hTconn haT hbT x₁ R ha hbfar
  obtain ⟨U₂, hU₂T, hU₂box, hU₂conn, hU₂in, hU₂out⟩ :=
    exists_star_subcrossing T hTconn hbT haT x₂ R hb hafar
  refine ⟨x₁, hx₁, x₂, hx₂,
    ⟨U₁, hU₁T.trans hTO, hU₁box, hU₁conn, hU₁in, hU₁out⟩,
    ⟨U₂, hU₂T.trans hTO, hU₂box, hU₂conn, hU₂in, hU₂out⟩, ?_⟩
  have hc : 62 * R ≤ boxDist x₁ x₂ := by
    have ht₁ := boxDist_trans a x₁ b
    have ht₂ := boxDist_trans x₁ x₂ b
    rw [boxDist_comm x₂ b] at ht₂
    omega
  intro z₁ hz₁ z₂ hz₂
  have ht₁ := boxDist_trans x₁ z₁ x₂
  have ht₂ := boxDist_trans z₁ z₂ x₂
  rw [boxDist_comm x₁ z₁] at ht₁
  omega

/-- `HasStarAnnularCrossing` for the sublevel set `{y | odometerOf ω t y - m ≤ -s}` coincides
with the paper's `Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m x R s`, translating the
natural-number `boxDist` inequalities to the real inequalities of `lowCrossingEvent` via
`exact_mod_cast` and `innerBoundary_nat_box_iff` for the outer-boundary membership. -/
lemma hasStarAnnularCrossing_iff_lowCrossing {d : ℕ} [NeZero d]
    (ω : Site d → ℝ) (t : ℕ) (m : ℝ) (x : Site d) (R : ℕ) (s : ℝ) :
    HasStarAnnularCrossing {y | odometerOf ω t y - m ≤ -s} x R ↔
      ω ∈ Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m x (R : ℝ) s := by
  constructor
  · rintro ⟨T, hTO, hTbox, hTconn, ⟨a, haT, haR⟩, ⟨b, hbT, hbR⟩⟩
    refine ⟨T, fun y hy => ⟨?_, hTO hy⟩, hTconn, ⟨a, haT, ?_⟩, ⟨b, hbT, ?_⟩⟩
    · change (boxDist y x : ℝ) ≤ 2 * (R : ℝ)
      exact_mod_cast hTbox hy
    · change (boxDist a x : ℝ) ≤ (R : ℝ)
      exact_mod_cast haR
    · have hh := (innerBoundary_nat_box_iff x b (2 * R)).mpr hbR
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
  · rintro ⟨T, hT, hTconn, ⟨a, haT, haR⟩, ⟨b, hbT, hbR⟩⟩
    refine ⟨T, fun y hy => (hT hy).2, fun y hy => ?_, hTconn,
      ⟨a, haT, ?_⟩, ⟨b, hbT, ?_⟩⟩
    · have hh := (hT hy).1
      change (boxDist y x : ℝ) ≤ 2 * (R : ℝ) at hh
      exact_mod_cast hh
    · change (boxDist a x : ℝ) ≤ (R : ℝ) at haR
      exact_mod_cast haR
    · apply (innerBoundary_nat_box_iff x b (2 * R)).mp
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbR

end Sandpile

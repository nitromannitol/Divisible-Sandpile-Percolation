/-
Two separated subcrossings extracted from a larger annular crossing.
-/
import Sandpile.Support.StarCrossings
import Sandpile.Support.CoarseBoxes

namespace Sandpile

def HasStarAnnularCrossing {d : ℕ} (O : Set (Site d)) (x : Site d) (R : ℕ) : Prop :=
  ∃ T : Set (Site d), T ⊆ O ∧ T ⊆ {z | boxDist z x ≤ 2 * R} ∧
    ((starLatticeGraph d).induce T).Connected ∧
    (∃ z ∈ T, boxDist z x ≤ R) ∧ (∃ z ∈ T, boxDist z x = 2 * R)

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

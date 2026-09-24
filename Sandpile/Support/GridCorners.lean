/-
Star connectivity of bad corners in a finite lattice grid.
-/
import Sandpile.Support.StarCrossings

namespace Sandpile

abbrev primalGrid (m n : ℕ) := Fin (m + 1) × Fin (n + 1)

def gridSite {m n : ℕ} (p : primalGrid m n) : Site 2 := ![(p.1.val : ℤ), (p.2.val : ℤ)]

lemma gridSite_injective {m n : ℕ} : Function.Injective (@gridSite m n) := by
  intro p q hpq
  apply Prod.ext
  · apply Fin.ext
    have hh := congr_fun hpq 0
    change (p.1.val : ℤ) = q.1.val at hh
    exact_mod_cast hh
  · apply Fin.ext
    have hh := congr_fun hpq 1
    change (p.2.val : ℤ) = q.2.val at hh
    exact_mod_cast hh

def IsGridCorner {m n : ℕ} (c : Fin m × Fin n) (p : primalGrid m n) : Prop :=
  c.1.val ≤ p.1.val ∧ p.1.val ≤ c.1.val + 1 ∧ c.2.val ≤ p.2.val ∧ p.2.val ≤ c.2.val + 1

lemma gridCorners_eq_or_star_adj {m n : ℕ} {c : Fin m × Fin n} {p q : primalGrid m n}
    (hp : IsGridCorner c p) (hq : IsGridCorner c q) :
    p = q ∨ (starLatticeGraph 2).Adj (gridSite p) (gridSite q) := by
  by_cases he : p = q
  · exact Or.inl he
  right
  refine ⟨fun hh => he (gridSite_injective hh), ?_⟩
  intro i
  have hcast : ∀ a b : ℕ, |(a : ℤ) - b| ≤ 1 → ((a : ℤ) - b).natAbs ≤ 1 := by
    intro a b hh
    have hh' : (((a : ℤ) - b).natAbs : ℤ) ≤ 1 := by simpa only [Int.natCast_natAbs] using hh
    exact_mod_cast hh'
  dsimp only [IsGridCorner] at hp hq
  fin_cases i
  · change ((p.1.val : ℤ) - q.1.val).natAbs ≤ 1
    apply hcast
    apply abs_le.mpr
    constructor <;> omega
  · change ((p.2.val : ℤ) - q.2.val).natAbs ≤ 1
    apply hcast
    apply abs_le.mpr
    constructor <;> omega

def gridBadGraph {m n : ℕ} (K : Set (primalGrid m n)) : SimpleGraph K :=
  (starLatticeGraph 2).comap (fun p : K => gridSite (p : primalGrid m n))

lemma gridBadGraph_corners_reachable {m n : ℕ} (K : Set (primalGrid m n))
    {c : Fin m × Fin n} (p q : K) (hp : IsGridCorner c p) (hq : IsGridCorner c q) :
    (gridBadGraph K).Reachable p q := by
  rcases gridCorners_eq_or_star_adj hp hq with he | he
  · have hh : p = q := Subtype.ext he
    rw [hh]
  · exact (show (gridBadGraph K).Adj p q from he).reachable

lemma isGridCorner_cast_cast {m n : ℕ} (i : Fin m) (j : Fin n) :
    IsGridCorner (i, j) (i.castSucc, j.castSucc) := by simp [IsGridCorner]

lemma isGridCorner_succ_cast {m n : ℕ} (i : Fin m) (j : Fin n) :
    IsGridCorner (i, j) (i.succ, j.castSucc) := by simp [IsGridCorner]

lemma isGridCorner_cast_succ {m n : ℕ} (i : Fin m) (j : Fin n) :
    IsGridCorner (i, j) (i.castSucc, j.succ) := by simp [IsGridCorner]

lemma isGridCorner_succ_succ {m n : ℕ} (i : Fin m) (j : Fin n) :
    IsGridCorner (i, j) (i.succ, j.succ) := by simp [IsGridCorner]

end Sandpile

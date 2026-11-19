import Sandpile.External.RSW.CenteredCrossing
import Sandpile.Support.GridRectangle

/-!
# Geometric centered crossings

The translated bond crossing event is characterized by nearest-neighbor walks in the
centered rectangle, with endpoints on its left and right sides.
-/

open LatticeProb Set

namespace Sandpile.External.RSW

/-- The integer sites of the centered rectangle with half-side lengths `m` and `n`. -/
def centeredPlaneRectangle (m n : ℕ) : Finset (Site 2) :=
  Fintype.piFinset (fun i => Finset.Icc (- ![(m : ℤ), (n : ℤ)] i)
    (![(m : ℤ), (n : ℤ)] i))

/-- Membership in the centered rectangle in coordinates. -/
theorem mem_centeredPlaneRectangle (m n : ℕ) (z : Site 2) :
    z ∈ centeredPlaneRectangle m n ↔
      -(m : ℤ) ≤ z 0 ∧ z 0 ≤ m ∧ -(n : ℤ) ≤ z 1 ∧ z 1 ≤ n := by
  simp only [centeredPlaneRectangle, Fintype.mem_piFinset, Finset.mem_Icc,
    Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

/-- Translation from an origin-based box to its centered counterpart. -/
def toCenteredRectangle (m n : ℕ) :
    rectangleGraph (planeRectangle (2 * m) (2 * n)) →g
      rectangleGraph (centeredPlaneRectangle m n) where
  toFun z := ⟨(z : Site 2) + (- ![(m : ℤ), (n : ℤ)]), by
    rw [mem_centeredPlaneRectangle, ← mem_shifted_planeRectangle_iff]
    have he : ((z : Site 2) + (- ![(m : ℤ), (n : ℤ)])) +
        ![(m : ℤ), (n : ℤ)] = z := by abel
    rw [he]
    exact z.property⟩
  map_rel' hab := lattice_adj_translate _ hab

/-- Translation from a centered box to the corresponding origin-based box. -/
def fromCenteredRectangle (m n : ℕ) :
    rectangleGraph (centeredPlaneRectangle m n) →g
      rectangleGraph (planeRectangle (2 * m) (2 * n)) where
  toFun z := ⟨(z : Site 2) + ![(m : ℤ), (n : ℤ)], by
    rw [mem_shifted_planeRectangle_iff, ← mem_centeredPlaneRectangle]
    exact z.property⟩
  map_rel' hab := lattice_adj_translate _ hab

/-- Translating both endpoints of each edge preserves walk openness. -/
theorem isBondOpenWalk_map {Q R : Finset (Site 2)} (g : Site 2 → Site 2)
    (f : rectangleGraph Q →g rectangleGraph R) (hf : ∀ z, (f z : Site 2) = g z)
    (ω : Sym2 (Site 2) → Bool) {a b : Q} (p : (rectangleGraph Q).Walk a b) :
    IsBondOpenWalk ω (p.map f) ↔ IsBondOpenWalk (ω ∘ Sym2.map g) p := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
    simp only [SimpleGraph.Walk.map_cons, IsBondOpenWalk, Function.comp_apply,
      Sym2.map_mk, hf, ih]

/-- The centered event is a crossing by an open walk in the centered coordinate rectangle. -/
theorem mem_centeredBondCrossingEvent_iff (m n : ℕ) (ω : Sym2 (Site 2) → Bool) :
    ω ∈ centeredBondCrossingEvent m n ↔
      ∃ (a b : centeredPlaneRectangle m n)
        (p : (rectangleGraph (centeredPlaneRectangle m n)).Walk a b),
        (a : Site 2) 0 = -(m : ℤ) ∧ (b : Site 2) 0 = m ∧ IsBondOpenWalk ω p := by
  change (∃ (a b : planeRectangle (2 * m) (2 * n))
    (p : (rectangleGraph (planeRectangle (2 * m) (2 * n))).Walk a b),
      a ∈ rectangleLeft (planeRectangle (2 * m) (2 * n)) ∧
      b ∈ rectangleRight (planeRectangle (2 * m) (2 * n)) ∧
      IsBondOpenWalk (ω ∘ Sym2.map (fun z => z + (- ![(m : ℤ), (n : ℤ)]))) p) ↔ _
  constructor
  · rintro ⟨a, b, p, ha, hb, hp⟩
    refine ⟨toCenteredRectangle m n a, toCenteredRectangle m n b,
      p.map (toCenteredRectangle m n), ?_, ?_, ?_⟩
    · have ha' := (mem_rectangleLeft_planeRectangle a).mp ha
      change (a : Site 2) 0 + -(m : ℤ) = -(m : ℤ)
      omega
    · have hb' := (mem_rectangleRight_planeRectangle b).mp hb
      change (b : Site 2) 0 + -(m : ℤ) = m
      push_cast at hb'
      omega
    · exact (isBondOpenWalk_map _ _ (fun _ => rfl) ω p).mpr hp
  · rintro ⟨a, b, p, ha, hb, hp⟩
    refine ⟨fromCenteredRectangle m n a, fromCenteredRectangle m n b,
      p.map (fromCenteredRectangle m n), ?_, ?_, ?_⟩
    · apply (mem_rectangleLeft_planeRectangle _).mpr
      change (a : Site 2) 0 + (m : ℤ) = 0
      omega
    · apply (mem_rectangleRight_planeRectangle _).mpr
      change (b : Site 2) 0 + (m : ℤ) = ((2 * m : ℕ) : ℤ)
      push_cast
      omega
    · have hh := (isBondOpenWalk_map (fun z => z + ![(m : ℤ), (n : ℤ)])
        (fromCenteredRectangle m n) (fun _ => rfl)
        (ω ∘ Sym2.map (fun z => z + (- ![(m : ℤ), (n : ℤ)]))) p).mpr ?_
      · exact hh
      · convert hp using 1
        ext e
        induction e using Sym2.ind with
        | _ x y => simp only [Function.comp_apply, Sym2.map_mk, add_neg_cancel_right]

end Sandpile.External.RSW

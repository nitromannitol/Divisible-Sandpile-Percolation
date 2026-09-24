/-
The three heat-kernel estimates of `sandpile.tex:1126-1140` are proved.
The existing input proposition and all dependent statements remain unchanged;
this theorem supplies a witness of that proposition.
-/
import Sandpile.Support.HeatKernelGradient

-- FROZEN-STATEMENT-BEGIN
/-- The three heat-kernel estimates in `sandpile.tex:1126-1140`
(label `ssec-green-estimates`): Gaussian upper bound, total-variation gradient
between same-parity starts, and maximal displacement. All three are proved. -/
theorem Sandpile.External.heatKernelBounds : Sandpile.External.HeatKernelBounds
-- FROZEN-STATEMENT-END
:= by
  intro d hd
  exact ⟨Sandpile.External.gaussianUpper d hd, Sandpile.exists_heatKernel_tv_gradient d hd,
    Sandpile.External.maxDisplacement d hd⟩

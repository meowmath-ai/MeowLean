import JSP000930FiniteOldMarkChoices

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.Cohen

open JSP000930.Positive JSP000930.BooleanAnalysis JSP000930.Positive.Cohen JSP000930.Positive.Dyadic

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

set_option maxHeartbeats 400000 in
theorem distanceLe_from_narrow_cohen_words
    (i j : I) (s t : Interval) (u v : List Bool)
    (c : ℚ × ℚ) (e : ℚ) (he : 0 < e) (m : CohenBA B (I × ℕ))
    (hmU : m ≤ wordValue B i u) (hmV : m ≤ wordValue B j v)
    (hLa : c.1-e/4 < (s.follow u).left) (hRa : (s.follow u).right < c.1+e/4)
    (hLb : c.2-e/4 < (t.follow v).left) (hRb : (t.follow v).right < c.2+e/4) :
    m ≤ distanceLe (intervalPointBits B i j s t) (ComplexBits.checked (gaussianRat c)) e := by
  obtain ⟨a,ha⟩ := ratPresentation_value_surjective (c.1 - e/4)
  obtain ⟨A,hA⟩ := ratPresentation_value_surjective (c.1 + e/4)
  obtain ⟨d,hd⟩ := ratPresentation_value_surjective (c.2 - e/4)
  obtain ⟨D,hD⟩ := ratPresentation_value_surjective (c.2 + e/4)
  let x := intervalPointBits B i j s t
  let y := ComplexBits.checked (B := CohenBA B (I × ℕ)) (gaussianRat c)
  have hxr : RationalEncloses x.re a A m :=
    ⟨hmU.trans (intervalCut_below_left i s u a (by simpa only [ha] using hLa)),
      hmU.trans (intervalCut_above_right i s u A (by simpa only [hA] using hRa.le))⟩
  have hxi : RationalEncloses x.im d D m :=
    ⟨hmV.trans (intervalCut_below_left j t v d (by simpa only [hd] using hLb)),
      hmV.trans (intervalCut_above_right j t v D (by simpa only [hD] using hRb.le))⟩
  have hyr : RationalEncloses y.re a A m := checked_rationalEnclosure _ _ _ m
    (by change (a.value : ℝ) < (c.1 : ℝ); rw [ha]; exact_mod_cast (show c.1-e/4 < c.1 by linarith))
    (by change (c.1 : ℝ) ≤ (A.value : ℝ); rw [hA]; exact_mod_cast (show c.1 ≤ c.1+e/4 by linarith))
  have hyi : RationalEncloses y.im d D m := checked_rationalEnclosure _ _ _ m
    (by change (d.value : ℝ) < (c.2 : ℝ); rw [hd]; exact_mod_cast (show c.2-e/4 < c.2 by linarith))
    (by change (c.2 : ℝ) ≤ (D.value : ℝ); rw [hD]; exact_mod_cast (show c.2 ≤ c.2+e/4 by linarith))
  exact distanceLe_of_common_box x y m (intervalPointBits_valid i j s t m)
    (ComplexBits.checked_cutOn _ _) a A d D hxr hxi hyr hyi e
    (by rw [ha,hA,hd,hD]; ring_nf <;> exact le_rfl)

end JSP000930.Negative.Cohen

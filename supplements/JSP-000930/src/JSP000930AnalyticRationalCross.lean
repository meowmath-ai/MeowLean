import JSP000930AnalyticRoundedLimit
import Mathlib.Tactic.LinearCombination

namespace JSP000930.BooleanAnalysis

theorem ratPresentation_cross_add (x y z : RatPresentation) :
    x.value + y.value = z.value ↔
      (x.pos*y.den + y.pos*x.den)*z.den + z.neg*(x.den*y.den) =
        z.pos*(x.den*y.den) + (x.neg*y.den + y.neg*x.den)*z.den := by
  have hx : (x.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt x.den_pos)
  have hy : (y.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt y.den_pos)
  have hz : (z.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt z.den_pos)
  unfold RatPresentation.value
  constructor
  · intro h
    field_simp [hx,hy,hz] at h
    have h' :
        ((x.pos : ℚ)*y.den + (y.pos : ℚ)*x.den)*z.den + (z.neg : ℚ)*(x.den*(y.den : ℚ)) =
          (z.pos : ℚ)*(x.den*(y.den : ℚ)) + ((x.neg : ℚ)*y.den + (y.neg : ℚ)*x.den)*z.den := by
      linear_combination h
    exact_mod_cast h'
  · intro h
    have h' :
        ((x.pos : ℚ)*y.den + (y.pos : ℚ)*x.den)*z.den + (z.neg : ℚ)*(x.den*(y.den : ℚ)) =
          (z.pos : ℚ)*(x.den*(y.den : ℚ)) + ((x.neg : ℚ)*y.den + (y.neg : ℚ)*x.den)*z.den := by
      exact_mod_cast h
    field_simp [hx,hy,hz]
    linear_combination h'

theorem ratPresentation_cross_mul (x y z : RatPresentation) :
    x.value * y.value = z.value ↔
      (x.pos*y.pos + x.neg*y.neg)*z.den + z.neg*(x.den*y.den) =
        z.pos*(x.den*y.den) + (x.pos*y.neg + x.neg*y.pos)*z.den := by
  have hx : (x.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt x.den_pos)
  have hy : (y.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt y.den_pos)
  have hz : (z.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt z.den_pos)
  unfold RatPresentation.value
  constructor
  · intro h
    field_simp [hx,hy,hz] at h
    have h' :
        ((x.pos : ℚ)*y.pos + (x.neg : ℚ)*y.neg)*z.den + (z.neg : ℚ)*(x.den*(y.den : ℚ)) =
          (z.pos : ℚ)*(x.den*(y.den : ℚ)) + ((x.pos : ℚ)*y.neg + (x.neg : ℚ)*y.pos)*z.den := by
      linear_combination h
    exact_mod_cast h'
  · intro h
    have h' :
        ((x.pos : ℚ)*y.pos + (x.neg : ℚ)*y.neg)*z.den + (z.neg : ℚ)*(x.den*(y.den : ℚ)) =
          (z.pos : ℚ)*(x.den*(y.den : ℚ)) + ((x.pos : ℚ)*y.neg + (x.neg : ℚ)*y.pos)*z.den := by
      exact_mod_cast h
    field_simp [hx,hy,hz]
    linear_combination h'

end JSP000930.BooleanAnalysis

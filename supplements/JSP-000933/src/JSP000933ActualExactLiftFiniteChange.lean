import JSP000933ActualExactContinuousLift

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def actualPrefixPatch (a : ℕ) (u x : ℕ → B) (m : ℕ) : B :=
  if m<a then u m else x m

theorem actualPrefixPatch_prefix_r347 (a : ℕ) (u : ℕ → B) :
    NamedPrefixMap (actualPrefixPatch a u) := by
  intro q N x y h m hm
  by_cases ha : m<a
  · simp only [actualPrefixPatch,ite_eq_left ha]
  · simpa only [actualPrefixPatch,ite_eq_right ha] using h m hm

theorem actualPrefixPatch_ofAgree_r347 {q : B} {a : ℕ} {u v x : ℕ → B}
    (h : ∀ m<a, q⊓u m=q⊓v m) :
    q≤realEqValue (actualPrefixPatch a u x) (actualPrefixPatch a v x) := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro m
  by_cases ha : m<a
  · simpa only [actualPrefixPatch,ite_eq_left ha] using h m ha
  · simp only [actualPrefixPatch,ite_eq_right ha]

theorem actualPrefixPatch_overPatch_r347 (a : ℕ) (u v x : ℕ → B) :
    actualPrefixPatch a u (actualPrefixPatch a v x)=actualPrefixPatch a u x := by
  funext m
  by_cases hm : m<a <;> simp [actualPrefixPatch,hm]

theorem actualPrefixPatch_self_r347 (a : ℕ) (x : ℕ → B) :
    actualPrefixPatch a x x=x := by
  funext m
  simp [actualPrefixPatch]

theorem exactLift_prefixChange_null_r347 {p : B} (F : CoherentSelectedIso B p)
    (c : ℕ → B) (L : (ℕ → B) → ℕ → B)
    (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (a : ℕ) (u v x : ℕ → B) :
    LocalEq true p (L (actualPrefixPatch a u x)) (L (actualPrefixPatch a v x)) := by
  let X := actualPrefixPatch a u x
  let Y := actualPrefixPatch a v x
  have hO : LocalEq false p (bitsMeet c X) (bitsMeet c Y) := by
    apply ordinaryLocalEq_late_agreement_r333 _ _ a
    intro m hm
    simp only [bitsMeet,X,Y,actualPrefixPatch,ite_eq_right (Nat.not_lt_of_ge hm)]
  have hMap := (F.restrict_r246 (show p≤p from le_rfl)).mapLocalEq_r239 hO
  exact (hL X).trans_r236 (hMap.trans_r236 (hL Y).symm_r236)

end SetLanguage
end JSP000933

import JSP000933ActualFaceRefinementMasks

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bitsBelowValue_trans_r324 {p : B} {a b c : ℕ → B}
    (hab : p≤bitsBelowValue a b) (hbc : p≤bitsBelowValue b c) : p≤bitsBelowValue a c := by
  unfold bitsBelowValue
  apply le_iInf
  intro m
  change p≤(a m)ᶜ⊔c m
  apply (le_materialImp_iff_r126 _ _ _).mpr
  exact (le_inf inf_le_left (bitsBelowValue_apply_r256 hab m)).trans (bitsBelowValue_apply_r256 hbc m)

theorem namedBadTails_from_allOpen_r324 {p q : B} {f : (ℕ → B) → ℕ → B}
    (hF : NamedContinuousOn p f) (hq : q≤p) (R : ℕ → B) (k : ℕ) (x : ℕ → B)
    (hOpen : ∀ N, q≤openValue (actualErrorTailBadCode f (fun _ => R) true k N) x) :
    q≤(eventuallySmallError true k (f x) R)ᶜ := by
  unfold eventuallySmallError eventualBudgetAt
  rw [compl_iSup]
  apply le_iInf
  intro N
  have hM := mask_under_r302 hq
    (actualErrorTailBadCode_mask_r302 hF (namedConstant_continuous_r302 p R) true k N x)
  exact ((le_inf le_rfl (hOpen N)).trans_eq hM).trans inf_le_right

theorem namedBadMasked_forces_originalFailure_r324 {p q : B}
    (F : CoherentSelectedIso B p) (hF : NameMapExt F.toName) (hqp : q≤p)
    (G : (ℕ → B) → ℕ → B) (c a b z x y : ℕ → B) (k : ℕ) (hk : k≠0)
    (hA : q≤bitsBelowValue a c) (hD : ∀ m, a m⊓b m=⊥)
    (hBad : q≤(eventuallySmallError true (32*k)
      (bitsMeet (F.toName a) (G (namedSplitMerge a b z x y))) (F.toName (bitsMeet a x)))ᶜ) :
    q≤(eventuallySmallError true (64*k) (G (namedSplitMerge a b z x y))
      (F.toName (bitsMeet c (namedSplitMerge a b z x y))))ᶜ := by
  let m := namedSplitMerge a b z x y
  let u := bitsMeet c m
  let E := eventuallySmallError true (64*k) (G m) (F.toName u)
  let r := q⊓E
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  change r≤⊥
  have hMask := (show r≤E from inf_le_right).trans
    (eventuallySmallError_mask_r298 true (64*k) (G m) (F.toName u) (F.toName a))
  have he := (F.restrict_r246 hqp).mapMeet_r237 a u
  have hExact := hF q _ _ (namedSplitMerge_payload_first_mask_r323 c a b z x y hA hD)
  have hNull : LocalEq true q (bitsMeet (F.toName a) (F.toName u)) (F.toName (bitsMeet a x)) :=
    he.symm_r236.trans_r236 (LocalEq.of_realEq_r246 true hExact)
  have hNear := (show r≤q from inf_le_left).trans (hNull.eventuallySmallError_r290 (64*k)
    (Nat.mul_ne_zero (by decide) hk))
  have hTr := eventuallySmallError_triangle_r290 true (32*k)
    (bitsMeet (F.toName a) (G m)) (bitsMeet (F.toName a) (F.toName u)) (F.toName (bitsMeet a x))
  rw [show 2*(32*k)=64*k by omega] at hTr
  exact (le_inf ((le_inf hMask hNear).trans hTr) (inf_le_left.trans hBad)).trans_eq inf_compl_eq_bot'

end SetLanguage
end JSP000933

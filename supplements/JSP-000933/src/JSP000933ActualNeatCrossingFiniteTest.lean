import JSP000933CommonCrossingLabelPrefixes

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def capNeatValue (e : ℕ ↪ Word) (a : ℕ → B) : B :=
  ⨅ i : ℕ, ⨅ j : ℕ, imp (a i ⊓ a j) (crispTruth B (labelsComparable (e i) (e j)))

noncomputable def bitsBelowValue (a b : ℕ → B) : B := ⨅ i : ℕ, imp (a i) (b i)

theorem bitsBelowValue_apply_r256 {p : B} {a b : ℕ → B}
    (h : p≤bitsBelowValue a b) (i : ℕ) : p⊓a i≤b i :=
  (le_materialImp_iff_r126 _ _ _).mp (h.trans (iInf_le _ i))

theorem capNeatValue_test_r256 (e : ℕ ↪ Word) (a : ℕ → B)
    {p : B} (hp : p≤capNeatValue e a) (i j : ℕ) (hi : p≤a i) (hj : p≤a j) :
    p≤crispTruth B (labelsComparable (e i) (e j)) :=
  _root_.context_imp_elim (hp.trans ((iInf_le _ i).trans (iInf_le _ j))) (le_inf hi hj)

theorem capPair_outside_shared_r256 (e : ℕ ↪ Word) (a b : ℕ → B)
    {p : B} (hA : p≤capNeatValue e a) (hB : p≤capNeatValue e b)
    (i j m : ℕ) (hi : p≤a i) (hj : p≤b j) (hInc : labelsIncomp (e i) (e j))
    (hm : m∉sharedLabelIndices e i j) : p ⊓ (a m ⊓ b m) ≤ ⊥ := by
  let q := p⊓(a m⊓b m)
  by_contra hn
  have hq : q≠⊥ := fun he => hn he.le
  have hl : labelsComparable (e m) (e i) := prop_of_le_crisp_nonzero_r190 hq
    (capNeatValue_test_r256 e a (inf_le_left.trans hA) m i
      (inf_le_right.trans inf_le_left) (inf_le_left.trans hi))
  have hr : labelsComparable (e m) (e j) := prop_of_le_crisp_nonzero_r190 hq
    (capNeatValue_test_r256 e b (inf_le_left.trans hB) m j
      (inf_le_right.trans inf_le_right) (inf_le_left.trans hj))
  exact hm (commonComparable_mem_shared_r255 e i j m hInc hl hr)

noncomputable def finiteSourceCrossValue (e : ℕ ↪ Word) (i j : ℕ) (x y : ℕ → B) : B :=
  ⨅ m : ↥(sharedLabelIndices e i j),
    bitEq (bitsMeet (crossCap x) (crossPay y) m.val) (bitsMeet (crossCap y) (crossPay x) m.val)

theorem finiteSourceCross_suffices_r256 (e : ℕ ↪ Word) (i j : ℕ) (x y : ℕ → B)
    {p : B} (hI : labelsIncomp (e i) (e j))
    (hAx : p≤capNeatValue e (crossCap x)) (hAy : p≤capNeatValue e (crossCap y))
    (hBx : p≤bitsBelowValue (crossPay x) (crossCap x))
    (hBy : p≤bitsBelowValue (crossPay y) (crossCap y))
    (hi : p≤crossCap x i) (hj : p≤crossCap y j)
    (hT : p≤finiteSourceCrossValue e i j x y) : p ≤ sourceCrossEq x y := by
  unfold sourceCrossEq realEqValue
  apply le_iInf
  intro m
  by_cases hm : m∈sharedLabelIndices e i j
  · exact hT.trans (iInf_le (fun l : ↥(sharedLabelIndices e i j) =>
      bitEq (bitsMeet (crossCap x) (crossPay y) l.val) (bitsMeet (crossCap y) (crossPay x) l.val)) ⟨m,hm⟩)
  · let a := crossCap x m
    let b := crossCap y m
    let u := crossPay x m
    let v := crossPay y m
    have hz : p⊓(a⊓b)≤⊥ := capPair_outside_shared_r256 e (crossCap x) (crossCap y)
      hAx hAy i j m hi hj hI hm
    have hl : p⊓(a⊓v)≤⊥ := by
      apply (le_inf inf_le_left (le_inf (inf_le_right.trans inf_le_left) ?_)).trans hz
      exact (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans (bitsBelowValue_apply_r256 hBy m)
    have hr : p⊓(b⊓u)≤⊥ := by
      apply (le_inf inf_le_left (le_inf ?_ (inf_le_right.trans inf_le_left))).trans hz
      exact (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans (bitsBelowValue_apply_r256 hBx m)
    exact (le_bitEq_iff_r126 p (a⊓v) (b⊓u)).mpr ((le_bot_iff.mp hl).trans (le_bot_iff.mp hr).symm)

theorem capNeatValue_mask_r256 (e : ℕ ↪ Word) {p : B} {x y : ℕ → B} (h : p≤realEqValue x y) :
    p⊓capNeatValue e x = p⊓capNeatValue e y := by
  unfold capNeatValue
  apply mask_iInf_congr_r126
  intro i
  apply mask_iInf_congr_r126
  intro j
  exact mask_imp_ante_congr_r211 (mask_inf_congr_r126
    ((le_realEqValue_iff_r126 _ _ _).mp h i) ((le_realEqValue_iff_r126 _ _ _).mp h j))

theorem bitsBelowValue_mask_r256 {p : B} {x x' y y' : ℕ → B} (hx : p≤realEqValue x x')
    (hy : p≤realEqValue y y') :
    p⊓bitsBelowValue x y = p⊓bitsBelowValue x' y' := by
  unfold bitsBelowValue
  apply mask_iInf_congr_r126
  intro i
  exact mask_sup_congr_r211 (mask_compl_congr_r126 ((le_realEqValue_iff_r126 _ _ _).mp hx i))
    ((le_realEqValue_iff_r126 _ _ _).mp hy i)

end SetLanguage
end JSP000933

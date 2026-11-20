import JSP000933ActualCrossingPayloadUnion

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

theorem liveLE_symmDiff_bot_r248 (h : Bool) (x y : ℕ → B) :
    liveLE h (bitsSymmDiff x y) (fun _ => ⊥) = liveLE h x y ⊓ liveLE h y x := by
  have h₁ : liveLE h (bitsMeet x (bitsComplement y)) (fun _ => ⊥) = liveLE h x y := by
    rw [← liveLE_disjoint_r238 h x (bitsComplement y),bitsComplement_compl_r234]
  have h₂ : liveLE h (bitsMeet (bitsComplement x) y) (fun _ => ⊥) = liveLE h y x := by
    rw [bitsMeet_comm_r238 (bitsComplement x) y,← liveLE_disjoint_r238 h y (bitsComplement x),
      bitsComplement_compl_r234]
  unfold bitsSymmDiff
  rw [liveLE_join_left_r235,h₁,h₂]

theorem actualGraph_same_source_outputEq_r248 (G : bSet B) (p : B)
    (hG : p ≤ actualPreserveReflectValue G) (x a b : ℕ → B)
    (ha : p≤graphPairBits G false x a) (hb : p≤graphPairBits G false x b) :
    LocalEq true p a b := by
  have h1 := graph_orderOnSelectedNames_r214 G p hG x x a b ha hb
  have h2 := graph_orderOnSelectedNames_r214 G p hG x x b a hb ha
  have hs (u v : B) : bitEq u v = bitEq v u := inf_comm _ _
  exact ⟨liveLE_topFromBitEq_r236 (h := true) (g := false) (x := a) (y := b) (z := x)
      (h1.trans_eq (hs _ _)),
    liveLE_topFromBitEq_r236 (h := true) (g := false) (x := b) (y := a) (z := x)
      (h2.trans_eq (hs _ _))⟩

theorem activeCrossing_targetError_null_r248 (G : bSet B) {p : B}
    (F : CoherentSelectedIso B p) (hG : p≤actualPreserveReflectValue G)
    (hF : ∀ x, p≤graphPairBits G false x (F.toName x))
    (w : I → B) (cap pay outCap outPay : I → ℕ → B)
    (hw : ∀ x, w x ≤ p)
    (hC : ∀ x, w x ≤ graphPairBits G false (cap x) (outCap x))
    (hD : ∀ x, w x ≤ graphPairBits G false (pay x) (outPay x))
    (hBelow : ∀ x i, w x ⊓ pay x i ≤ cap x i)
    (hCross : ∀ x y, w x ⊓ w y ≤ realEqValue (bitsMeet (cap x) (pay y)) (bitsMeet (cap y) (pay x)))
    (x : I) :
    LocalLE true (w x)
      (bitsSymmDiff (bitsMeet (F.toName (activePayloadUnion w pay)) (outCap x)) (outPay x))
      (fun _ => ⊥) := by
  let J := F.restrict_r246 (hw x)
  let U := activePayloadUnion w pay
  have hCap : LocalEq true (w x) (F.toName (cap x)) (outCap x) :=
    actualGraph_same_source_outputEq_r248 G (w x) ((hw x).trans hG) (cap x) _ _
      ((hw x).trans (hF (cap x))) (hC x)
  have hPay : LocalEq true (w x) (F.toName (pay x)) (outPay x) :=
    actualGraph_same_source_outputEq_r248 G (w x) ((hw x).trans hG) (pay x) _ _
      ((hw x).trans (hF (pay x))) (hD x)
  have hSrc : LocalEq false (w x) (bitsMeet U (cap x)) (pay x) :=
    activePayloadUnion_meet_cap_localEq_r247 w cap pay hBelow hCross x
  have hOut : LocalEq true (w x) (bitsMeet (F.toName U) (outCap x)) (outPay x) := by
    have h1 : LocalEq true (w x) (bitsMeet (F.toName U) (outCap x))
        (bitsMeet (F.toName U) (F.toName (cap x))) :=
      LocalEq.meet_congr_r239 (LocalEq.refl_r239 true (w x) _) hCap.symm_r236
    exact h1.trans_r236 ((J.mapMeet_r237 U (cap x)).symm_r236.trans_r236
      ((J.mapLocalEq_r239 hSrc).trans_r236 hPay))
  unfold LocalLE
  rw [liveLE_symmDiff_bot_r248]
  exact le_inf hOut.1 hOut.2

end SetLanguage
end JSP000933

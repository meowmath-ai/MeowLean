import JSP000930PositiveNativeTypedGraphLaws

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.SetLanguage JSP000933.CantorCodes JSP000933.PreparedModel
  JSP000930.AnalyticSyntax

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem sequenceTaylorGraph_reconstruct {n : ℕ} (v : DVec (V B) n) (a : STerm n)
    (p : B) (hp : p ≤ bTruth v (sequence_f a)) :
    p ≤ bTerm v a =ᴮ taylorCodeName (graphTaylorBits (bTerm v a)) := by
  have h := hp.trans (typedComplexFunction_le_native v a
    (JSP000933.SetLanguage.omega : STerm n))
  rw [show bTerm v (JSP000933.SetLanguage.omega : STerm n) = bSet.omega from
    boolean_realize_bounded_term_omega'] at h
  have hs : p ≤ graphTypedShape (bTerm v a) bSet.omega := h.trans inf_le_left
  have ht : p ≤ graphTypedTotalUnique (bTerm v a) bSet.omega := h.trans inf_le_right
  exact graphTaylorBits_reconstruct (bTerm v a) p (typedGraph_func hs ht)
    (typedGraph_good_total_omega ht) (typedGraph_pairs_omega hs)

theorem entireTaylorGraph_reconstruct {n : ℕ} (v : DVec (V B) n) (a : STerm n)
    (p : B) (hp : p ≤ bTruth v (isEntireCode_f a)) :
    p ≤ bTerm v a =ᴮ taylorCodeName (graphTaylorBits (bTerm v a)) := by
  have hAnd : bTruth v (isEntireCode_f a) =
      bTruth v (sequence_f a) ⊓ bTruth v (entireRadii_f a) :=
    boolean_realize_bounded_formula_and
  rw [hAnd] at hp
  exact sequenceTaylorGraph_reconstruct v a p (hp.trans inf_le_left)

theorem bitCover_covers_entireTaylorNames {n : ℕ}
    (v : DVec (V B) n) (a : STerm n) (p : B)
    (hp : p ≤ bTruth v (isEntireCode_f a))
    (e : GroundContinuumSuccIndex → ℕ → B)
    (hE : ∀ x : ℕ → B,(⨆ i,realEqValue x (e i)) = ⊤) :
    p ≤ ⨆ i,(bTerm v a =ᴮ taylorCodeName (decodeTaylorBits (e i))) := by
  let U := graphTaylorBits (bTerm v a)
  let x := encodeTaylorBits U
  have hR := entireTaylorGraph_reconstruct v a p hp
  have hT : p ≤ p ⊓ (⨆ i,realEqValue x (e i)) := by
    rw [hE,inf_top_eq]
  apply hT.trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  have hEq := taylorCode_decoded_eq_of_realEq
    (inf_le_right : p ⊓ realEqValue x (e i) ≤ realEqValue x (e i))
  have hEq' : p ⊓ realEqValue x (e i) ≤
      taylorCodeName U =ᴮ taylorCodeName (decodeTaylorBits (e i)) := by
    simpa only [x,decode_encode_taylorBits] using hEq
  exact bv_trans (inf_le_left.trans hR) hEq'

namespace Cohen

theorem wetzelCohen_taylorName_cover :
    ∃ e : GroundContinuumSuccIndex → ℕ → WetzelCohenBA,
      ∀ (a : bSet WetzelCohenBA) (p : WetzelCohenBA),
        (let v : DVec (V WetzelCohenBA) 1 := DVec.cons a DVec.nil
         p ≤ bTruth v (isEntireCode_f (bd_var ⟨0,by decide⟩))) →
        p ≤ ⨆ i,a =ᴮ taylorCodeName (decodeTaylorBits (e i)) := by
  obtain ⟨e,hE⟩ := wetzelCohen_kappa_realCover
  refine ⟨e,fun a p hp => ?_⟩
  let v : DVec (V WetzelCohenBA) 1 := DVec.cons a DVec.nil
  let A : STerm 1 := bd_var ⟨0,by decide⟩
  exact bitCover_covers_entireTaylorNames v A p hp e hE

end Cohen
end JSP000930.Positive

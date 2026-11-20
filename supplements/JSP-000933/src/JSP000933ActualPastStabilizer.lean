import JSP000933ActualFinitePastClosedTail

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_finitePast_vector_r349 (x : ℕ → B) (a : ℕ) (p : B) (hp : p≠⊥) :
    ∃ (u : Fin a → Bool) (r : B), r≠⊥ ∧ r≤p ∧
      ∀ m<a, r⊓x m=r⊓finitePastBits u m := by
  let f (i : Fin a) (b : Bool) := literal (x i.val) b
  have hF : p≤⨅ i : Fin a, ⨆ b, f i b := by
    apply le_iInf
    intro i
    exact le_top.trans ((show (⊤ : B)=(x i.val)ᶜ⊔x i.val from compl_sup_eq_top.symm).le.trans
      (sup_le (le_iSup (f i) false) (le_iSup (f i) true)))
  obtain ⟨u,r,hr,hrp,hR⟩ := exists_nonzero_finiteChoices_fin_r135 a f p hp hF
  refine ⟨u,r,hr,hrp,?_⟩
  intro m hm
  have hM : m<(List.ofFn u).length := by simpa only [List.length_ofFn] using hm
  have he : wordBit (List.ofFn u) m=u ⟨m,hm⟩ := by
    rw [wordBit,dite_eq_left hM]
    exact List.getElem_ofFn hM
  have hBit : r≤bitEq (x m) (truthBit (u ⟨m,hm⟩)) :=
    (hR ⟨m,hm⟩).trans_eq (bitEq_truthBit_r175 _ _).symm
  simpa only [finitePastBits,paddedWordBits,he] using (le_bitEq_iff_r126 _ _ _).mp hBit

theorem uniformPastChange_arbitrary_r349 {p q : B} {L : (ℕ → B) → ℕ → B}
    (hC : NamedContinuousOn p L) (hqp : q≤p) (a k N n : ℕ) (hn : N≤n) (u v x : ℕ → B)
    (hU : q≤uniformPastChangeValue L a k N x) :
    q≤nameErrorBudget true k n (L (actualPrefixPatch a u x)) (L (actualPrefixPatch a v x)) := by
  apply le_of_dense_named_refinements_r219
  intro r hr hrq
  obtain ⟨i,s,hs,hsr,hI⟩ := exists_finitePast_vector_r349 u a r hr
  obtain ⟨j,t,ht,hts,hJ⟩ := exists_finitePast_vector_r349 v a s hs
  have htq := hts.trans (hsr.trans hrq)
  have hx := hC.realEq_mask_r323 (htq.trans hqp) (actualPrefixPatch_ofAgree_r347 (x := x)
    (fun m hm => mask_under_r302 hts (hI m hm)))
  have hy := hC.realEq_mask_r323 (htq.trans hqp) (actualPrefixPatch_ofAgree_r347 (x := x) hJ)
  have he := nameErrorBudget_mask_r313 true k n hx hy
  have hT := (htq.trans (hU.trans (iInf_le _ ((i,j) : PastPair a)))).trans
    (budgetTail_apply_r229 _ k N n hn)
  exact ⟨t,ht,hts.trans hsr,((le_inf le_rfl hT).trans_eq he.symm).trans inf_le_right⟩

theorem exists_actualPast_middle_refinement_r349 {p q : B} (F : CoherentSelectedIso B p)
    (c : ℕ → B) (L : (ℕ → B) → ℕ → B)
    (hC : NamedContinuousOn p L)
    (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (a k : ℕ) (hk : k≠0) (hq : q≠⊥) (hqp : q≤p) :
    ∃ (N : ℕ) (w : Word) (r : B), r≠⊥ ∧ r≤q ∧
      ∀ (s : B), s≤r → ∀ x : ℕ → B,
        (∀ m, a≤ m → m<w.length → s⊓x m=s⊓paddedWordBits w m) →
        ∀ (u v : ℕ → B) (n : ℕ), N≤n →
          s≤nameErrorBudget true k n (L (actualPrefixPatch a u x)) (L (actualPrefixPatch a v x)) := by
  let K (N : ℕ) := uniformPastChangeBadCode L a k N
  let V (N : ℕ) (x : ℕ → B) := uniformPastChangeValue L a k N x
  have hCov (x : ℕ → B) : p⊓cylinderValue x []≤⨆ N, (openValue (K N) x)ᶜ := by
    apply inf_le_left.trans
    have hpV := uniformPastChangeValue_covers_r348 F c L hL a k hk x
    apply (le_inf le_rfl hpV).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro N
    exact (closedCode_closedMask_r318 le_rfl (K N) (V N) x
      (uniformPastChangeBadCode_mask_r348 hC a k N x)).ge.trans (inf_le_right.trans (le_iSup (fun M => (openValue (K M) x)ᶜ) N))
  have hI : q≤goodTailInteriorValue K [] := hqp.trans (cylinder_closedCover_has_interior_r304 K [] hCov)
  obtain ⟨N,t,ht,htq,hN⟩ := exists_nonzero_below_choice_r135 q hq
    (fun N => ⨆ w : {w : Word // ExtendsWord [] w}, cylinderInClosedValue (K N) w.val) hI
  obtain ⟨w,r,hr,hrt,hR⟩ := exists_nonzero_below_choice_r135 t ht
    (fun w : {w : Word // ExtendsWord [] w} => cylinderInClosedValue (K N) w.val) hN
  refine ⟨N,w.val,r,hr,hrt.trans htq,?_⟩
  intro s hsr x hX u v n hn
  let y := actualPrefixPatch a (paddedWordBits w.val) x
  have hy : s≤cylinderValue y w.val := by
    apply cylinder_from_all_wordBit_masks_r296
    intro m hm
    change s⊓y m=s⊓paddedWordBits w.val m
    by_cases ha : m<a
    · simp only [y,actualPrefixPatch,ite_eq_left ha]
    · simpa only [y,actualPrefixPatch,ite_eq_right ha] using hX m (Nat.le_of_not_gt ha) hm
  have hsp := hsr.trans (hrt.trans (htq.trans hqp))
  have hGood := cylinderInClosedValue_elim_r280 (K N) w.val y (hsr.trans hR) hy
  have hTail : s≤V N y := ((le_inf le_rfl hGood).trans_eq
    (closedCode_closedMask_r318 hsp (K N) (V N) y (uniformPastChangeBadCode_mask_r348 hC a k N y))).trans inf_le_right
  have he := uniformPastChange_arbitrary_r349 hC hsp a k N n hn u v y hTail
  simpa only [y,actualPrefixPatch_overPatch_r347] using he

end SetLanguage
end JSP000933

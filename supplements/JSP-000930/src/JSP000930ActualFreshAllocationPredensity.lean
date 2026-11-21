import JSP000930RawRowsAfterCohenMove

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen JSP000930.Positive.Dyadic
open JSP000930.Negative.Cohen JSP000933.MarkedForcing JSP000933.ForcingTransport
open JSP000933.BooleanCompletion

variable {B I J X : Type} [NontrivialCompleteBooleanAlgebra B] [Fintype I]

set_option maxHeartbeats 1600000 in
theorem actual_freshAllocation_meets_old_dense_product
    (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
    (site' : J → ComplexBits (CohenBA B (X × ℕ)))
    (H' : I → J → ℕ → ComplexBits (CohenBA B (X × ℕ)))
    (A : J → Prop) (z : J) (hz : ¬ A z)
    (hS : ∀ j,A j ∨ j=z → (site j).map (markedCompleteValueMap (valuedCohen B (X × ℕ))) = site' j)
    (hH : ∀ i j,A j → ∀ n,(H i j n).map (markedCompleteValueMap (valuedCohen B (X × ℕ))) = H' i j n)
    (hSite : ∀ j,(site j).CutOn (⊤ : B))
    (hH0 : ∀ i j,A j → ∀ n,(H i j n).CutOn (⊤ : B))
    (hApart0 : ∀ j,A j ∨ j=z → ∀ u,A u ∨ u=z → j ≠ u →
      (⊤ : B) ≤ ((site j).name =ᴮ (site u).name)ᶜ)
    (hSite' : ∀ j,(site' j).CutOn (⊤ : CohenBA B (X × ℕ)))
    (hH' : ∀ i j,A j ∨ j=z → ∀ n,(H' i j n).CutOn (⊤ : CohenBA B (X × ℕ)))
    (hApart' : ∀ j,A j ∨ j=z → ∀ u,A u ∨ u=z → j ≠ u →
      (⊤ : CohenBA B (X × ℕ)) ≤ ((site' j).name =ᴮ (site' u).name)ᶜ)
    (E : Set (AnalyticRowTotal site H A)) (hE : DenseConditionSet E)
    (q : AnalyticRowTotal site' H' (fun j => A j ∨ j=z))
    (p : I → SymbolicTrace J) (hp : ∀ i,(q.trace i).val = some (p i))
    (t : CohenTotal B (X × ℕ)) (ht : imageCondition t ≤ q.mask)
    (route : FreshRows p z × Bool → X) (hRoute : Function.Injective route)
    (interval : FreshRows p z × Bool → Interval)
    (hValues : ∀ k : FreshRows p z,
      imageCondition t ≤ (H' k.1 z (pinAt (p k.1) (newPinNumber (p k.1) z k.2)).2).name =ᴮ
        (intervalPointBits B (route (k,false)) (route (k,true)) (interval (k,false)) (interval (k,true))).name) :
    let F := markedCompleteValueMap (valuedCohen B (X × ℕ))
    ∃ d : AnalyticRowTotal site H A, d ∈ E ∧
      Compatible q (includeAnalyticProductCondition (fun j hj => Or.inl hj) F site H site' H'
        (fun j hj => hS j (Or.inl hj)) hH d) := by
  classical
  dsimp only
  let F := markedCompleteValueMap (valuedCohen B (X × ℕ))
  let hs (j : J) (hj : A j) := hS j (Or.inl hj)
  obtain ⟨a,ha,haT,⟨S⟩⟩ := exists_fresh_center_batch site H site' H' A z
    (fun j _ => hSite j) hH0 hApart0 hs hH q p hp t ht route interval
  obtain ⟨d,hd,hda,hD⟩ := old_dense_product_refines_actual_centers site H
    (fun j _ => hSite j) hH0 (fun j hj k hk h => hApart0 j (Or.inl hj) k (Or.inl hk) h)
    E hE S.center S.center_support a ha S.center_valid
  choose dLabel hdLabel hdRaw using hD
  let w (i : I) := decodeSymbolicTrace site (H i) (dLabel i)
  have hSuppD (i : I) : SymbolicAt A (dLabel i) := by
    have h := (d.trace i).2
    rw [hdLabel i] at h
    exact h
  have hDP (i : I) : ∀ j ∈ (w i).pins,A j :=
    (decodeSymbolicTrace_support_iff site (H i) (dLabel i)).mpr (hSuppD i)
  have hSep (i : I) (j : J) (hj : j ∈ (w i).pins) :
      (⊤ : B) ≤ ((site z).name =ᴮ (site j).name)ᶜ :=
    hApart0 z (Or.inr rfl) j (Or.inl (hDP i j hj)) (fun h => hz (h.symm ▸ hDP i j hj))
  obtain ⟨s,hs₀,hsD,⟨G⟩⟩ := exists_old_target_batch S w d.nonzero hda hSite hSep hdRaw
  obtain ⟨t',ht'T,ht'S,hMove⟩ := cohen_retarget_many_earlier_named_values t s hs₀
    (hsD.trans (hda.trans haT)) route hRoute interval (fun k => (S.fresh k).c)
    (fun k => (w k.1).eval (site z)) G.query_valid (fun k => (S.fresh k).e) G.ε
    (fun k => (S.fresh k).pos_budget.le) G.pos G.query_near G.inside
  let m := imageCondition t'
  have hm : m ≠ ⊥ := imageCondition_ne_bot_r50 t'
  have hms : m ≤ F.toFun s := (baseEmbed_reflects_mask_r427 t' s).mpr ht'S
  have hmq : m ≤ q.mask := (imageCondition_mono_r50 ht'T).trans ht
  have hmd := hms.trans (F.monotone hsD)
  have hSup (i : I) : SymbolicAt (fun j => A j ∨ j=z) (p i) := by
    have h := (q.trace i).2
    rw [hp i] at h
    exact h
  have hResults := raw_rows_after_actual_cohen_move site H site' H' A z hz p hSup t route interval
    a d.mask s hda hsD S w G hDP hdRaw m hm hms hS hH hSite' hH' hApart'
    (fun k => (imageCondition_mono_r50 ht'T).trans (hValues k)) hMove
  choose r hR hRd hRq using hResults
  have hRvalid (i : I) : m ≤ polyValid site' (H' i) (r i) :=
    (hRd i).trans (inf_le_left.trans inf_le_left)
  obtain ⟨b,u,hb,hbM,hU⟩ := simultaneously_normalize_old_centers site' H'
    (fun j _ => hSite' j) hH' hApart' r hR m hm hRvalid
  let Q (i : I) := supportedSymbolicQ site' (H' i) (fun j => A j ∨ j=z)
  have hu (i : I) : b ≤ (Q i).valid (u i) :=
    ((hU i).trans ((polynomialQ site' (H' i)).refine_valid _ _)).trans inf_le_left
  let common : AnalyticRowTotal site' H' (fun j => A j ∨ j=z) :=
    ⟨b,u,hb,le_iInf hu⟩
  refine ⟨d,hd,common,⟨hbM.trans hmq,?_⟩,⟨hbM.trans hmd,?_⟩⟩
  · apply le_iInf
    intro i
    change b ≤ (polynomialQ site' (H' i)).refines
      ((u i).val.map (decodeSymbolicTrace site' (H' i))) ((q.trace i).val.map (decodeSymbolicTrace site' (H' i)))
    rw [hp i]
    exact (le_inf (hU i) (hbM.trans (hRq i))).trans ((polynomialQ site' (H' i)).trans _ _ _)
  · apply le_iInf
    intro i
    change b ≤ (polynomialQ site' (H' i)).refines
      ((u i).val.map (decodeSymbolicTrace site' (H' i))) ((d.trace i).val.map (decodeSymbolicTrace site' (H' i)))
    rw [hdLabel i]
    have hEq : (w i).map F = decodeSymbolicTrace site' (H' i) (dLabel i) :=
      decodeSymbolicTrace_completeMap_on_log F (dLabel i) site (H i) site' (H' i)
        (fun j hj => hs j (hSuppD i j hj)) (fun j hj => hH i j (hSuppD i j hj))
    rw [Option.map_some,← hEq]
    exact (le_inf (hU i) (hbM.trans (hRd i))).trans ((polynomialQ site' (H' i)).trans _ _ _)

end JSP000930.Negative

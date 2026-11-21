import JSP000930LocalPredensityShrink

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {I B : Type} [LinearOrder I] [WellFoundedLT I] [CompleteBooleanAlgebra B]
variable {T : I → Type} {Q : ∀ i,ValuedPoset B (T i)} {m : B}

theorem telescope_local_predensity930
    (F : ∀ i j,i≤j → LocalTraceInclusion (Q i) (Q j) m)
    (hId : ∀ i t,(F i i le_rfl).label t = t)
    (hComp : ∀ i j k (hij : i≤j) (hjk : j≤k) t,
      (F j k hjk).label ((F i j hij).label t) = (F i k (hij.trans hjk)).label t)
    (hShape : ∀ b, (∃ a,a<b) →
      (∃ c,c<b ∧ ∀ a,a<b → a≤c) ∨
      (∀ q : MaskedCondition (Q b) m,∃ (a : I) (ha : a<b) (r : MaskedCondition (Q a) m),
        (F a b ha.le).insideMap r ≤ q))
    (hNext : ∀ a b (hab : a<b), (∀ i,i<b → i≤a) →
      PreservesPredensity (F a b hab.le).insideMap) :
    ∀ b a (hab : a≤b),PreservesPredensity (F a b hab).insideMap := by
  intro b
  have hWF : WellFounded (fun i j : I => i < j) := wellFounded_lt
  induction b using hWF.induction with
  | h b ih =>
    intro a hab
    by_cases he : a=b
    · subst a
      intro D hD p
      obtain ⟨d,hd,hmem⟩ := hD p
      have h'd : (F b b le_rfl).insideMap d = d := by
        apply Subtype.ext
        exact totalCondition_eq_of_data _ _ rfl (hId b d.val.trace)
      refine ⟨d,hmem,d,hd,?_⟩
      rw [h'd]
    · have hlt := hab.lt_of_ne he
      rcases hShape b ⟨a,hlt⟩ with ⟨c,hcb,hmax⟩ | hD
      · have hac := hmax a hlt
        have hp := (F a c hac).predense_comp930 (F c b hcb.le)
          (ih c hcb a hac) (hNext c b hcb hmax)
        have hMap : ((F a c hac).comp930 (F c b hcb.le)).insideMap = (F a b hab).insideMap :=
          funext (fun p => LocalTraceInclusion.insideMap_ext930 _ _ (hComp a c b hac hcb.le) p)
        rwa [hMap] at hp
      · intro D hPrev p
        obtain ⟨c,hcb,q,hqp⟩ := hD p
        let k := max a c
        have hkb : k<b := max_lt hlt hcb
        have hak : a≤k := le_max_left _ _
        have hck : c≤k := le_max_right _ _
        let q' := (F c k hck).insideMap q
        obtain ⟨d,hd,r,hrq,hrd⟩ := ih k hkb a hak D hPrev q'
        have hCompA : (F k b hkb.le).insideMap ((F a k hak).insideMap d) =
            (F a b hab).insideMap d :=
          ((F a k hak).insideMap_comp930 (F k b hkb.le) d).symm.trans
            (LocalTraceInclusion.insideMap_ext930 _ _ (hComp a k b hak hkb.le) d)
        have hCompC : (F k b hkb.le).insideMap q' = (F c b hcb.le).insideMap q :=
          ((F c k hck).insideMap_comp930 (F k b hkb.le) q).symm.trans
            (LocalTraceInclusion.insideMap_ext930 _ _ (hComp c k b hck hkb.le) q)
        refine ⟨d,hd,(F k b hkb.le).insideMap r,?_,?_⟩
        · exact (((F k b hkb.le).insideMap_mono930 hrq).trans_eq hCompC).trans hqp
        · exact ((F k b hkb.le).insideMap_mono930 hrd).trans_eq hCompA

end JSP000930.Negative

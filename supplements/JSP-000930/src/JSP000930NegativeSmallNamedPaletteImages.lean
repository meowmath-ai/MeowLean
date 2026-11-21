import JSP000930NegativeLiteralFinalContinuum
import JSP000933RelativeMixedEnumTransport

open bSet Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.BooleanNames JSP000933.BooleanCompletion
  JSP000933.OpenGraphForcing JSP000933.RelativeOCA JSP000930.Positive

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def mixedFamilyRow (E : MixedEnumeration OmegaOneIndex I B)
    (X : I → bSet B) (r : OmegaOneIndex) : bSet B :=
  mixture (E.cell r) X

theorem mixedFamilyRow_agrees (E : MixedEnumeration OmegaOneIndex I B)
    (X : I → bSet B) (r : OmegaOneIndex) (i : I) :
    E.cell r i ≤ mixedFamilyRow E X r =ᴮ X i := by
  apply mixing_lemma'
  intro j k
  by_cases hjk : j = k
  · subst k
    exact bv_refl
  · exact (disjoint_iff_inf_le.mp (E.rowApart r hjk)).trans bot_le

theorem mixedFamilyRow_covers (E : MixedEnumeration OmegaOneIndex I B)
    (X : I → bSet B) (a : bSet B) :
    (⨆ i,a =ᴮ X i) ≤ ⨆ r,a =ᴮ mixedFamilyRow E X r := by
  apply iSup_le
  intro i
  rw [← inf_top_eq (a =ᴮ X i),← E.colFull i,inf_iSup_eq]
  apply iSup_le
  intro r
  apply le_iSup_of_le r
  exact bv_trans inf_le_left (bv_symm (inf_le_right.trans (mixedFamilyRow_agrees E X r i)))

theorem mixedNamedFamily_injects_omegaOne (E : MixedEnumeration OmegaOneIndex I B)
    (X : I → bSet B) (S : bSet B)
    (hS : ∀ a,(a ∈ᴮ S) ≤ ⨆ i,a =ᴮ X i) :
    (⊤ : B) ≤ injects_into S (check BaseOmegaOne) :=
  injects_into_of_named_cover (mixedFamilyRow E X) omegaOneCheckName S _
    (fun a => (hS a).trans (mixedFamilyRow_covers E X a))
    checkedOmegaOne_entry_mem (fun _ _ h => omegaOneCheck_eq_bot_r83 h)

theorem prepared_smallNamedFamily_injects_omegaOne [Nonempty I]
    (F : CompleteValueMap PreparedBA B) (hI : Cardinal.mk I ≤ Cardinal.continuum)
    (X : I → bSet B) (S : bSet B)
    (hS : ∀ a,(a ∈ᴮ S) ≤ ⨆ i,a =ᴮ X i) :
    (⊤ : B) ≤ injects_into S (check BaseOmegaOne) := by
  obtain ⟨E⟩ := prepared_smallMixedTraceEnum_r471 I hI
  exact mixedNamedFamily_injects_omegaOne (E.map_r470 F) X S hS

end JSP000930.Negative

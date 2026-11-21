import JSP000930PositiveActualHaymanEvalImage
import JSP000930PositiveActualCohenContinuum
import JSP000930PositiveActualReserveComplexPoint

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive.Cohen

open JSP000933.SetLanguage JSP000933.PreparedModel JSP000933.OpenGraphForcing
  JSP000930.SetLanguage JSP000930.AnalyticSyntax

structure ReserveAnalyticLaw : Prop where
  totalAtReserve : ∀ {n : ℕ} (v : DVec (V WetzelCohenBA) n)
    (F : STerm n) (p : WetzelCohenBA) (i : GroundContinuumSuccIndex)
    (c : OmegaOneIndex) (W : bSet WetzelCohenBA) (x : ℕ → WetzelCohenBA),
    p ≤ bTruth v (familyEntire_f actualAnalyticSyntax F) →
    p ≤ taylorCodeName (decodeTaylorBits x) ∈ᴮ bTerm v F →
    p ≤ availableAtReserve x c →
    p ≤ ⨆ y,valueCertificate v (reservePoint c) W (taylorCodeName (decodeTaylorBits x)) y
  distinctAtReserve : ∀ {n : ℕ} (v : DVec (V WetzelCohenBA) n)
    (F : STerm n) (p : WetzelCohenBA) (c : OmegaOneIndex)
    (W y y' : bSet WetzelCohenBA) (x x' : ℕ → WetzelCohenBA),
    p ≤ bTruth v (familyEntire_f actualAnalyticSyntax F) →
    p ≤ (taylorCodeName (decodeTaylorBits x) ∈ᴮ bTerm v F) ⊓
      (taylorCodeName (decodeTaylorBits x') ∈ᴮ bTerm v F) →
    p ≤ availableAtReserve x c ⊓ availableAtReserve x' c →
    p ≤ (taylorCodeName (decodeTaylorBits x) =ᴮ taylorCodeName (decodeTaylorBits x'))ᶜ →
    p ≤ valueCertificate v (reservePoint c) W (taylorCodeName (decodeTaylorBits x)) y →
    p ≤ valueCertificate v (reservePoint c) W (taylorCodeName (decodeTaylorBits x')) y' →
    p ≤ (y =ᴮ y')ᶜ

theorem actual_pointwise_bound_within_omegaOne
    (hAnalytic : ReserveAnalyticLaw) {n : ℕ} (v : DVec (V WetzelCohenBA) n)
    (F M : STerm n) (p : WetzelCohenBA)
    (hEntire : p ≤ bTruth v (familyEntire_f actualAnalyticSyntax F))
    (hPW : p ≤ bTruth v (pointwiseBound_f actualAnalyticSyntax F M))
    (hCap : p ≤ injects_into (bTerm v M) (check BaseOmegaOne)) :
    p ≤ injects_into (bTerm v F) (check BaseOmegaOne) := by
  classical
  obtain ⟨e,hE⟩ := wetzelCohen_kappa_realCover
  let D := bTerm v F
  let code (i : GroundContinuumSuccIndex) := taylorCodeName (decodeTaylorBits (e i))
  apply checkedOmegaOne_bound_of_actual_reserve_evaluations D code e p
  · intro a
    let t : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    let w := DVec.cons a v
    have h := bitCover_covers_entireTaylorNames w t (p ⊓ (a ∈ᴮ D))
      (with_familyEntire_member v F a p hEntire) e hE
    exact h
  · intro c q hq hqp
    let z := reservePoint c
    let A := fun i => firstFamilyIndices code D i ⊓ availableAtReserve (e i) c
    have hz : q ≤ bTruth (DVec.cons z v) (complex_f (bd_var ⟨0,Nat.succ_pos n⟩)) :=
      le_top.trans (reservePoint_forces_complex (DVec.cons z v) _ c (bTerm_current_r181 v z))
    obtain ⟨W,hImage,hSmall⟩ := actual_pointwise_choose_value_set v F M z q
      (hqp.trans hPW) hz
    choose val hval using fun i : GroundContinuumSuccIndex => choose_actual_eval_name v z W (code i)
    have hMem (i : GroundContinuumSuccIndex) : q ⊓ A i ≤ code i ∈ᴮ D :=
      inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hAv (i : GroundContinuumSuccIndex) : q ⊓ A i ≤ availableAtReserve (e i) c :=
      inf_le_right.trans inf_le_right
    have hCert (i : GroundContinuumSuccIndex) :
        q ⊓ A i ≤ valueCertificate v z W (code i) (val i) :=
      (hAnalytic.totalAtReserve v F _ i c W (e i)
        (inf_le_left.trans (hqp.trans hEntire)) (hMem i) (hAv i)).trans_eq (hval i)
    refine ⟨W,val,injects_into_trans hSmall (hqp.trans hCap),?_,?_⟩
    · intro i
      exact actual_evalImage_contains v F z W (code i) (val i) _
        (inf_le_left.trans hImage) (hMem i) (hCert i)
    · intro i j hij
      let d := (q ⊓ A i) ⊓ (q ⊓ A j)
      have dFirst (k : GroundContinuumSuccIndex) : q ⊓ A k ≤ firstNamedOccurrence code k :=
        inf_le_right.trans (inf_le_left.trans inf_le_left)
      have hNE : d ≤ (code i =ᴮ code j)ᶜ := by
        apply le_compl_iff_disjoint_right.mpr
        apply disjoint_iff_inf_le.mpr
        exact (inf_le_inf (inf_le_inf (dFirst i) (dFirst j)) le_rfl).trans
          (firstNamedOccurrence_separates code hij).le
      have hNo := hAnalytic.distinctAtReserve v F d c W (val i) (val j) (e i) (e j)
        (inf_le_left.trans (inf_le_left.trans (hqp.trans hEntire)))
        (inf_le_inf (hMem i) (hMem j)) (inf_le_inf (hAv i) (hAv j)) hNE
        (inf_le_left.trans (hCert i)) (inf_le_right.trans (hCert j))
      exact (le_compl_iff_disjoint_right.mp hNo).eq_bot

end JSP000930.Positive.Cohen

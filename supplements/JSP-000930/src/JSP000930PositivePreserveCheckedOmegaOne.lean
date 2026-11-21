import JSP000930PositiveInternalCardinalOfReals
import JSP000933RelativeOmegaOnePreservation
import JSP000933FiniteOrdinalLabels
import JSP000933LocalKappaTraceSupport

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.PreparedModel JSP000933.BooleanNames JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA JSP000933.CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem checkedOmegaOne_as_family :
    (check BaseOmegaOne : bSet B) = familyName omegaOneCheckName (fun _ => ⊤) :=
  check_omegaOne_eq_family_r83

theorem omega_not_surjects_checkedOmegaOne (hB : BoundsCountableOmegaOneNames B) :
    (surjects_onto bSet.omega (check BaseOmegaOne) : B) = ⊥ := by
  classical
  apply le_bot_iff.mp
  unfold surjects_onto
  apply iSup_le
  intro G
  let A : bSet B := check BaseOmegaOne
  let m : B := is_surj_onto bSet.omega A G
  change m ≤ ⊥
  by_contra hm
  have hNZ : m ≠ ⊥ := fun he => hm he.le
  let V (n : ℕ) (i : OmegaOneIndex) : B :=
    pair (bSet.of_nat n) (omegaOneCheckName i) ∈ᴮ G
  have hT (n : ℕ) : m ≤ ⨆ i,V n i := by
    have hTotal := is_total_of_is_func' (show m ≤ is_func' bSet.omega A G from inf_le_left)
    have hMem : (⊤ : B) ≤ (bSet.of_nat n : bSet B) ∈ᴮ bSet.omega :=
      bSet.of_nat_mem_omega
    have hs := (le_inf (hTotal.trans (iInf_le _ (bSet.of_nat n)))
      (le_top.trans hMem)).trans Lattice.bv_imp_elim
    change m ≤ ⨆ a : bSet B,(a ∈ᴮ A) ⊓ (pair (bSet.of_nat n) a ∈ᴮ G) at hs
    rw [show A = familyName omegaOneCheckName (fun _ => ⊤) from checkedOmegaOne_as_family,
      ← bounded_exists (h_congr := show B_ext
        (fun a : bSet B => pair (bSet.of_nat n) a ∈ᴮ G) from B_ext_pair_mem_right)] at hs
    simp only [familyName,bSet.bval,bSet.func,top_inf_eq] at hs
    change m ≤ ⨆ i : OmegaOneIndex, pair (bSet.of_nat n) (omegaOneCheckName i) ∈ᴮ G
    exact hs
  let T (b : OmegaOneIndex) : B := ⨅ n,⨆ i : ↥(Set.Iio b),V n i.val
  have hBounds : m ≤ ⨆ b,T b := (le_iInf hT).trans (hB V)
  obtain ⟨b,d,hd,hdm,hdT⟩ := exists_nonzero_below_choice_r135 m hNZ T hBounds
  have hKill (n : ℕ) : d ⊓ V n b ≤ ⊥ := by
    have hD : d ≤ ⨆ j : ↥(Set.Iio b),V n j.val := hdT.trans (iInf_le _ n)
    apply (le_inf le_rfl (inf_le_inf hD le_rfl)).trans
    rw [iSup_inf_eq,inf_iSup_eq]
    apply iSup_le
    intro j
    let c := (V n j.val ⊓ V n b) ⊓ d
    have hFunc : c ≤ is_func G := inf_le_right.trans
      (hdm.trans (inf_le_left.trans inf_le_left))
    have hEq : c ≤ ((omegaOneCheckName j.val : bSet B) =ᴮ omegaOneCheckName b) :=
      eq_of_is_func_of_eq hFunc bv_refl (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right)
    have hc : c ≤ ⊥ := hEq.trans_eq (omegaOneCheck_eq_bot_r83 j.property.ne)
    exact (le_of_eq (inf_comm (d ⊓ V n b) (V n j.val ⊓ V n b))).trans
      ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans hc)
  let a : bSet B := omegaOneCheckName b
  have ha : (⊤ : B) ≤ a ∈ᴮ A := by
    rw [show A = familyName omegaOneCheckName (fun _ => ⊤) from checkedOmegaOne_as_family]
    change (⊤ : B) ≤ omegaOneCheckName b ∈ᴮ
      bSet.mk OmegaOneIndex omegaOneCheckName (fun _ => ⊤)
    exact bSet.mem_mk omegaOneCheckName (fun _ => ⊤) b
  have hs : d ≤ ⨆ z : bSet B,z ∈ᴮ bSet.omega ⊓ (pair z a ∈ᴮ G) :=
    (le_inf ((hdm.trans inf_le_right).trans (iInf_le _ a)) (le_top.trans ha)).trans Lattice.bv_imp_elim
  rw [← bounded_exists (h_congr := show B_ext (fun z : bSet B => pair z a ∈ᴮ G)
    from B_ext_pair_mem_left)] at hs
  have hz : d ≤ ⊥ := by
    apply (le_inf le_rfl hs).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro n
    change d ⊓ (⊤ ⊓ V n.down b) ≤ ⊥
    rw [top_inf_eq]
    exact hKill n.down
  exact hd (le_bot_iff.mp hz)

theorem checkedOmegaOne_not_injects_omega (hB : BoundsCountableOmegaOneNames B) :
    (injects_into (check BaseOmegaOne) bSet.omega : B) = ⊥ := by
  apply le_bot_iff.mp
  exact (surjects_onto_of_injects_into' le_rfl aleph_one_check_exists_mem).trans_eq
    (omega_not_surjects_checkedOmegaOne hB)

end JSP000930.Positive

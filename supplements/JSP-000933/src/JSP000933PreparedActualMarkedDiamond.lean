import JSP000933PreparedActualGuessGraph

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

open BooleanNames

noncomputable def actualDiamondSupport : bSet PreparedBA :=
  familyName
    (fun d : {d : GroundContinuumSuccIndex // OmegaOneCofinalIndex d} => preparedOrdinalEntry d.val)
    (fun _ => ⊤)

theorem actualSupport_mem_r421 (d : GroundContinuumSuccIndex) (h : OmegaOneCofinalIndex d) :
    (⊤ : PreparedBA)≤(preparedOrdinalEntry d : bSet PreparedBA)∈ᴮ actualDiamondSupport := by
  unfold actualDiamondSupport familyName
  exact bSet.mem_mk
    (fun j : {j : GroundContinuumSuccIndex // OmegaOneCofinalIndex j} => (preparedOrdinalEntry j.val : bSet PreparedBA))
    (fun _ => ⊤) ⟨d,h⟩

theorem actualGuesses_prefixes_r421 :
    (⊤ : PreparedBA)≤⨅ d : bSet PreparedBA,(d∈ᴮ check BaseSuccPSet)⟹
      (⨆ g : bSet PreparedBA,(pair d g∈ᴮ actualGuesses)⊓(g⊆ᴮ d)) := by
  let F (d : bSet PreparedBA) := ⨆ g : bSet PreparedBA,(pair d g∈ᴮ actualGuesses)⊓(g⊆ᴮ d)
  have hF : B_ext F :=
    B_ext_iSup (h := fun g => B_ext_inf B_ext_pair_mem_left B_ext_subset_right)
  apply (checkedBoundedAll_iff_r418 BaseSuccPSet preparedOrdinalEntry preparedKappa_basis_r418
    preparedKappa_mem_r418 ⊤ F hF).mpr
  intro d
  exact le_iSup_of_le (actualGuessAt d) (le_inf
    (pair_mem_functionalGraph_self_r102 _ _ d) (actualGuess_subset_r420 d))

noncomputable def actualStationaryAgreement (a c g support : bSet PreparedBA) : PreparedBA :=
  ⨆ d : bSet PreparedBA,(d∈ᴮ support)⊓((d∈ᴮ c)⊓
    (⨆ y : bSet PreparedBA,(pair d y∈ᴮ g)⊓((y⊆ᴮ d)⊓actualPrefixAgreement a y d)))

set_option maxHeartbeats 600000 in
theorem prepared_actualClub_agreement_r421 (a c : bSet PreparedBA) :
    preparedActualClub c≤actualStationaryAgreement a c actualGuesses actualDiamondSupport := by
  let m := preparedActualClub c
  obtain ⟨hU,hC⟩ := prepared_actualClub_reduces_r419 c m le_rfl
  have hCorrect : m ≤ preparedCorrectGuessValue (preparedProfile a) (preparedProfile c) :=
    prepared_actualDiamond_value_r410 (preparedProfile a) (preparedProfile c) m hU hC
  refine hCorrect.trans ?_
  unfold preparedCorrectGuessValue
  apply iSup_le
  intro d
  let D : bSet PreparedBA := preparedOrdinalEntry d.val
  let Y : bSet PreparedBA := actualGuessAt d.val
  let w : PreparedBA := preparedProfile c d.val ⊓ ⨅ i : ↥(Set.Iio d.val),
    booleanAgree (preparedProfile a i.val) (decodePreparedGuess d.val i.val)
  have hMem : w ≤ D ∈ᴮ c := by
    change w ≤ preparedProfile c d.val
    exact inf_le_left
  have hSupport : w ≤ D ∈ᴮ actualDiamondSupport :=
    le_top.trans (actualSupport_mem_r421 d.val d.property)
  have hPair : w ≤ pair D Y ∈ᴮ actualGuesses :=
    le_top.trans (pair_mem_functionalGraph_self_r102 preparedOrdinalEntry actualGuessAt d.val)
  have hSubset : w ≤ Y ⊆ᴮ D := le_top.trans (actualGuess_subset_r420 d.val)
  have hAgreement : w ≤ actualPrefixAgreement a Y D := by
    apply actualPrefixAgreement_of_bits_r420 a d.val w
    intro i hi
    exact inf_le_right.trans (iInf_le (fun j : ↥(Set.Iio d.val) =>
      booleanAgree (preparedProfile a j.val) (decodePreparedGuess d.val j.val)) ⟨i,hi⟩)
  have hInner : w ≤ ⨆ y : bSet PreparedBA, (pair D y ∈ᴮ actualGuesses) ⊓
      ((y ⊆ᴮ D) ⊓ actualPrefixAgreement a y D) := by
    apply le_iSup_of_le Y
    exact le_inf hPair (le_inf hSubset hAgreement)
  unfold actualStationaryAgreement
  apply le_iSup_of_le D
  exact le_inf hSupport (le_inf hMem hInner)

noncomputable def actualDiamondOn (g support : bSet PreparedBA) : PreparedBA :=
  (is_func' (check BaseSuccPSet) (bv_powerset (check BaseSuccPSet)) g)⊓
    ⨅ a : bSet PreparedBA,(a⊆ᴮ check BaseSuccPSet)⟹
      (⨅ c : bSet PreparedBA,((c⊆ᴮ check BaseSuccPSet)⊓preparedActualClub c)⟹
        actualStationaryAgreement a c g support)

theorem prepared_actualDiamondAtSupport_r421 :
    (⊤ : PreparedBA)≤⨆ g : bSet PreparedBA,actualDiamondOn g actualDiamondSupport := by
  apply le_iSup_of_le actualGuesses
  apply le_inf actualGuesses_func_r420
  apply le_iInf
  intro a
  rw [← deduction,top_inf_eq]
  apply le_iInf
  intro c
  rw [← deduction]
  exact (inf_le_right.trans inf_le_right).trans (prepared_actualClub_agreement_r421 a c)

end PreparedModel
end JSP000933

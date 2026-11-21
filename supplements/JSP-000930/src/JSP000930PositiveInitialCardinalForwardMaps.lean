import JSP000930PositiveMixedEnumerationInjection
import JSP000933PreparedSmallTraceEnum

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.BooleanNames
  JSP000933.OpenGraphForcing JSP000933.RelativeOCA

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem checkedOmegaOne_entries_cover (a : bSet B) :
    (a ∈ᴮ check BaseOmegaOne) ≤ ⨆ i : OmegaOneIndex, a =ᴮ omegaOneCheckName i := by
  rw [checkedOmegaOne_as_family,mem_familyName_r70]
  simp only [top_inf_eq,le_rfl]

theorem checkedOmegaOne_entry_mem (i : OmegaOneIndex) :
    (⊤ : B) ≤ (omegaOneCheckName i : bSet B) ∈ᴮ check BaseOmegaOne := by
  rw [checkedOmegaOne_as_family]
  change (⊤ : B) ≤ omegaOneCheckName i ∈ᴮ bSet.mk OmegaOneIndex omegaOneCheckName (fun _ => ⊤)
  exact bSet.mem_mk omegaOneCheckName (fun _ => ⊤) i

theorem omega_entries_cover (a : bSet B) :
    (a ∈ᴮ bSet.omega) ≤ ⨆ n : ℕ, a =ᴮ (bSet.of_nat n : bSet B) := by
  have he : (bSet.omega : bSet B) =
      familyName (fun n : ULift ℕ => (bSet.of_nat n.down : bSet B)) (fun _ => ⊤) := rfl
  rw [he,mem_familyName_r70]
  apply iSup_le
  intro n
  exact le_iSup_of_le n.down inf_le_right

theorem omega_injects_into_checkedOmegaOne :
    (⊤ : B) ≤ injects_into bSet.omega (check BaseOmegaOne) := by
  have he : Cardinal.mk ℕ ≤ Cardinal.mk OmegaOneIndex := by
    rw [Cardinal.mk_nat,mk_OmegaOneIndex_r61]
    exact Cardinal.aleph0_lt_aleph_one.le
  obtain ⟨E⟩ := (Cardinal.le_def ℕ OmegaOneIndex).mp he
  exact injects_into_of_named_cover (fun n : ℕ => bSet.of_nat n)
    (fun n => omegaOneCheckName (E n)) _ _ omega_entries_cover
    (fun n => checkedOmegaOne_entry_mem (E n))
    (fun _ _ hij => omegaOneCheck_eq_bot_r83 (fun h => hij (E.injective h)))

theorem checkedOmegaOne_injects_into_kappa :
    (⊤ : B) ≤ injects_into (check BaseOmegaOne) (check BaseSuccPSet) := by
  have he : Cardinal.mk OmegaOneIndex ≤ Cardinal.mk GroundContinuumSuccIndex := by
    rw [mk_OmegaOneIndex_r61,continuumSuccIndex_card_r406]
    exact Cardinal.aleph_one_le_continuum.trans (Order.le_succ _)
  obtain ⟨E⟩ := (Cardinal.le_def OmegaOneIndex GroundContinuumSuccIndex).mp he
  exact injects_into_of_named_cover (fun i : OmegaOneIndex => omegaOneCheckName i)
    (fun i => preparedOrdinalEntry (E i)) _ _ checkedOmegaOne_entries_cover
    (fun i => preparedKappa_mem_r418 (E i))
    (fun _ _ hij => preparedOrdinalEntry_eq_bot_r416 (fun h => hij (E.injective h)))

theorem checked_predecessor_injects_into_omegaOne
    (F : CompleteValueMap PreparedBA B) (d : GroundContinuumSuccIndex) :
    (⊤ : B) ≤ injects_into (preparedOrdinalEntry d) (check BaseOmegaOne) := by
  classical
  rw [preparedOrdinalEntry_asOrdinal_r416]
  let α := continuumSuccOrdinal d
  let S := PSet.ordinalMk α
  have hS : Cardinal.mk S.Type ≤ 𝔠 := by
    unfold S
    rw [PSet.ordinalMk_card]
    exact Order.lt_succ_iff.mp (Cardinal.lt_ord.mp (continuumSuccOrdinal_lt_r392 d))
  let x (j : S.Type) : bSet B := check (S.Func j)
  have hD (a : bSet B) : (a ∈ᴮ check S) ≤ ⨆ j, a =ᴮ x j := by
    exact (check_mem_as_iSup_930 (f := S) a).le
  by_cases hN : Nonempty S.Type
  · letI : Nonempty S.Type := hN
    obtain ⟨E⟩ := prepared_smallMixedTraceEnum_r471 S.Type hS
    exact mixedEnumeration_injects_into (E.map_r470 F) x omegaOneCheckName _ _ hD
      checkedOmegaOne_entry_mem
      (fun j k hjk => check_bv_eq_bot_of_not_equiv (PSet.ordinalMk_inj α j k hjk))
      (fun _ _ hij => omegaOneCheck_eq_bot_r83 hij)
  · letI : IsEmpty S.Type := ⟨fun j => hN ⟨j⟩⟩
    let y : S.Type → bSet B := fun j => isEmptyElim j
    apply weightedGraph_injects_into x y (fun _ => ⊥)
    · exact fun j => isEmptyElim j
    · exact fun j => isEmptyElim j
    · intro a
      simpa using hD a
    · exact fun j => isEmptyElim j

end JSP000930.Positive

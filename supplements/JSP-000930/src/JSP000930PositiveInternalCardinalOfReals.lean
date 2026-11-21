import JSP000930PositiveFirstNamedOccurrences
import JSP000930PositiveCohenContinuumUpperCover
import JSP000930PositiveDistinctCohenRealRows
import JSP000933RealNameExtensionality
import JSP000933PreparedOrdinalQuantifiers

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.PreparedModel JSP000933.BooleanNames JSP000933.CantorCodes
  JSP000933.MarkedForcing

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem check_mem_as_iSup_930 {f : PSet.{0}} (z : bSet B) :
    z ∈ᴮ (check f : bSet B) = ⨆ k : f.Type, z =ᴮ check (f.Func k) := by
  cases f with
  | mk α A =>
    simp only [mem_unfold, check, bSet.bval, bSet.func, top_inf_eq]
    rfl

theorem checkedKappa_named_entries_cover (x : bSet B) :
    (x ∈ᴮ check BaseSuccPSet) ≤ ⨆ i : GroundContinuumSuccIndex,
      x =ᴮ (preparedOrdinalEntry i : bSet B) := by
  rw [check_mem_as_iSup_930]
  apply iSup_le
  intro j
  obtain ⟨i,hi⟩ := preparedKappa_basis_r418 (B := B) j
  rw [hi]
  exact le_iSup (fun i : GroundContinuumSuccIndex => (x =ᴮ (preparedOrdinalEntry i : bSet B))) i

theorem named_reals_cover_of_bit_cover
    (e : GroundContinuumSuccIndex → ℕ → B)
    (h : ∀ x : ℕ → B,(⨆ i,realEqValue x (e i)) = ⊤) (x : bSet B) :
    (x ∈ᴮ bv_powerset bSet.omega) ≤ ⨆ i, x =ᴮ realBitsName (e i) := by
  let p := x ∈ᴮ bv_powerset bSet.omega
  have hp : p ≤ x ⊆ᴮ bSet.omega := bv_powerset_spec.mpr le_rfl
  change p ≤ _
  rw [← inf_top_eq p,← h (membershipBits x),inf_iSup_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  apply le_nameEq_of_realEq_for_subsets_r128 (inf_le_left.trans hp)
    (le_top.trans (realBitsName_subset_r103 (e i)))
  simpa only [membershipBits_realBitsName_r128] using
    (inf_le_right : p ⊓ realEqValue (membershipBits x) (e i) ≤ _)

theorem named_reals_inject_into_checkedKappa
    (e : GroundContinuumSuccIndex → ℕ → B)
    (h : ∀ x : ℕ → B,(⨆ i,realEqValue x (e i)) = ⊤) :
    (⊤ : B) ≤ injects_into (bv_powerset bSet.omega) (check BaseSuccPSet) :=
  injects_into_of_named_cover (fun i => realBitsName (e i)) preparedOrdinalEntry
    _ _ (named_reals_cover_of_bit_cover e h) preparedKappa_mem_r418
      (fun _ _ hij => preparedOrdinalEntry_eq_bot_r416 hij)

theorem checkedKappa_injects_into_named_reals
    (e : GroundContinuumSuccIndex → ℕ → B)
    (h : ∀ i j, i ≠ j → realEqValue (e i) (e j) = ⊥) :
    (⊤ : B) ≤ injects_into (check BaseSuccPSet) (bv_powerset bSet.omega) := by
  apply injects_into_of_named_cover preparedOrdinalEntry (fun i => realBitsName (e i))
  · exact checkedKappa_named_entries_cover
  · exact fun i => bv_powerset_spec.mp (realBitsName_subset_r103 (e i))
  · intro i j hij
    rw [realBitsName_eq_r128,h i j hij]

namespace Cohen

instance : Nonempty (TotalCondition wetzelCohenPoset) :=
  ⟨weakenToBase wetzelCohenPoset ⊤ top_ne_bot⟩

theorem wetzelCohen_reals_inject_into_kappa :
    (⊤ : WetzelCohenBA) ≤ injects_into (bv_powerset bSet.omega) (check BaseSuccPSet) := by
  obtain ⟨e,he⟩ := wetzelCohen_kappa_realCover
  exact named_reals_inject_into_checkedKappa e he

theorem wetzelCohen_kappa_injects_into_reals :
    (⊤ : WetzelCohenBA) ≤ injects_into (check BaseSuccPSet) (bv_powerset bSet.omega) := by
  apply checkedKappa_injects_into_named_reals (fun i => cohenRow PreparedBA (Sum.inl i : WetzelRow))
  intro i j hij
  exact cohen_rows_distinct (fun h => hij (Sum.inl_injective h))

end Cohen
end JSP000930.Positive

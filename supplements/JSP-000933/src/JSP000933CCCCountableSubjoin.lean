import JSP000933CliqueForcing
import Mathlib.Order.Zorn

namespace JSP000933
namespace OpenGraphForcing

variable {B : Type*} [CompleteBooleanAlgebra B]

theorem exists_countable_subjoin_r67 {I : Type*} (hCCC : BooleanCCC B) (a : I → B) :
    ∃ S : Set I, S.Countable ∧ (⨆ i : S, a i.1) = ⨆ i, a i := by
  classical
  let Q : Set B := {b | b ≠ ⊥ ∧ ∃ i, b ≤ a i}
  let A : Set (Set B) := {S | S ⊆ Q ∧ ∀ b ∈ S, ∀ c ∈ S, b ≠ c → Disjoint b c}
  have hZ : ∀ C ⊆ A, IsChain (· ⊆ ·) C → ∃ U ∈ A, ∀ S ∈ C, S ⊆ U := by
    intro C hC hCh
    refine ⟨⋃₀ C,⟨?_,?_⟩,fun _ h => Set.subset_sUnion_of_mem h⟩
    · rintro x ⟨S,hS,hxS⟩
      exact (hC hS).1 hxS
    · rintro b ⟨S,hS,hbS⟩ c ⟨T,hT,hcT⟩ hne
      by_cases he : S = T
      · subst T
        exact (hC hS).2 b hbS c hcT hne
      · rcases hCh hS hT he with h | h
        · exact (hC hT).2 b (h hbS) c hcT hne
        · exact (hC hS).2 b hbS c (h hcT) hne
  obtain ⟨M,hM⟩ := zorn_subset A hZ
  have hCount : M.Countable := hCCC M (fun b hb => (hM.prop.1 hb).1) hM.prop.2
  have hCover (i : I) : a i ≤ sSup M := by
    by_contra h
    let b := a i ⊓ (sSup M)ᶜ
    have hb : b ≠ ⊥ := by
      intro he
      apply h
      have hd : Disjoint (a i) (sSup M)ᶜ := disjoint_iff_inf_le.mpr he.le
      simpa only [compl_compl] using le_compl_iff_disjoint_right.mpr hd
    have hD (m : B) (hm : m ∈ M) : Disjoint b m := by
      apply le_compl_iff_disjoint_right.mp
      exact inf_le_right.trans (compl_le_compl (le_sSup hm))
    have hbNot : b ∉ M := by
      intro hm
      exact hb (disjoint_self.mp (hD b hm))
    have hInsert : insert b M ∈ A := by
      refine ⟨?_,?_⟩
      · intro y hy
        rcases Set.mem_insert_iff.mp hy with rfl | hM'
        · exact ⟨hb,i,inf_le_left⟩
        · exact hM.prop.1 hM'
      · intro x hx y hy hne
        rcases Set.mem_insert_iff.mp hx with rfl | hx
        · rcases Set.mem_insert_iff.mp hy with rfl | hy
          · exact False.elim (hne rfl)
          · exact hD y hy
        · rcases Set.mem_insert_iff.mp hy with rfl | hy
          · exact (hD x hx).symm
          · exact hM.prop.2 x hx y hy hne
    have he : M = insert b M := hM.eq_of_subset hInsert (Set.subset_insert _ _)
    exact hbNot (he.symm ▸ Set.mem_insert b M)
  have hEach (b : ↥M) : ∃ i, b.1 ≤ a i := (hM.prop.1 b.2).2
  choose select hSelect using hEach
  let S := Set.range select
  letI : Countable (↥M) := hCount.to_subtype
  refine ⟨S,Set.countable_range select,?_⟩
  apply le_antisymm
  · exact iSup_le (fun i => le_iSup a i.1)
  · apply iSup_le
    intro i
    apply (hCover i).trans
    apply sSup_le
    intro b hb
    exact (hSelect ⟨b,hb⟩).trans
      (le_iSup (fun j : ↥S => a j.1) ⟨select ⟨b,hb⟩,Set.mem_range_self _⟩)

end OpenGraphForcing
end JSP000933

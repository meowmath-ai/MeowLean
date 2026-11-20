import JSP000933CCCCountableSubjoin

namespace JSP000933
namespace OpenGraphForcing

variable {I B : Type*} [CompleteBooleanAlgebra B]

abbrev EnumerationMatrix (I B : Type*) [CompleteBooleanAlgebra B] :=
  {e : ℕ → I → B // ∀ n i j, i ≠ j → Disjoint (e n i) (e n j)}

noncomputable def matrixCoverage (g : I → B) (e : EnumerationMatrix I B) : B :=
  ⨅ i, (g i)ᶜ ⊔ (⨆ n, e.1 n i)

noncomputable def countableCoverageValue (g : I → B) : B :=
  ⨆ e : EnumerationMatrix I B, matrixCoverage g e

theorem enumerationRow_support_countable_r68 (hCCC : BooleanCCC B)
    (e : EnumerationMatrix I B) (n : ℕ) :
    {i : I | e.1 n i ≠ ⊥}.Countable := by
  classical
  let f := e.1 n
  let S : Set I := {i | f i ≠ ⊥}
  let T := f '' S
  have hN (a : B) (ha : a ∈ T) : a ≠ ⊥ := by
    obtain ⟨i,hi,rfl⟩ := ha
    exact hi
  have hD (a : B) (ha : a ∈ T) (b : B) (hb : b ∈ T) (hne : a ≠ b) : Disjoint a b := by
    obtain ⟨i,hi,rfl⟩ := ha
    obtain ⟨j,hj,rfl⟩ := hb
    exact e.2 n i j (fun h => hne (congrArg f h))
  have hInj : Set.InjOn f S := by
    intro i hi j hj h
    by_contra hn
    have hd := e.2 n i j hn
    change Disjoint (f i) (f j) at hd
    rw [← h] at hd
    exact hi (disjoint_self.mp hd)
  exact Set.countable_of_injective_of_countable_image hInj (hCCC T hN hD)

theorem countableCoverageValue_ne_top_r68 (hCCC : BooleanCCC B)
    (hI : ¬ Countable I) (g : I → B) (hNon : ∀ i, g i ≠ ⊥) :
    countableCoverageValue g ≠ ⊤ := by
  classical
  obtain ⟨E,hE,hJoin⟩ := exists_countable_subjoin_r67 hCCC
    (fun e : EnumerationMatrix I B => matrixCoverage g e)
  letI : Countable (↥E) := hE.to_subtype
  let Bad : Set I := ⋃ en : ↥E × ℕ, {i : I | en.1.1.1 en.2 i ≠ ⊥}
  have hBad : Bad.Countable :=
    Set.countable_iUnion (fun en : ↥E × ℕ => enumerationRow_support_countable_r68 hCCC en.1.1 en.2)
  have hNot : ¬ (Set.univ : Set I) ⊆ Bad := fun h => hI (Set.countable_univ_iff.mp (hBad.mono h))
  obtain ⟨i,_,hi⟩ := Set.not_subset.mp hNot
  have hE0 (e : ↥E) (n : ℕ) : e.1.1 n i = ⊥ := by
    by_contra hn
    exact hi (Set.mem_iUnion.mpr ⟨(e,n),hn⟩)
  have hEach (e : ↥E) : matrixCoverage g e.1 ≤ (g i)ᶜ := by
    have hh := iInf_le (fun j => (g j)ᶜ ⊔ (⨆ n, e.1.1 n j)) i
    simpa only [matrixCoverage,hE0 e,iSup_const,sup_bot_eq] using hh
  have hh : countableCoverageValue g ≤ (g i)ᶜ := by
    rw [countableCoverageValue,← hJoin]
    exact iSup_le hEach
  intro hTop
  rw [hTop] at hh
  have hg : g i ≤ (g i)ᶜ := le_top.trans hh
  exact hNon i (disjoint_self.mp (le_compl_iff_disjoint_right.mp hg))

end OpenGraphForcing
end JSP000933

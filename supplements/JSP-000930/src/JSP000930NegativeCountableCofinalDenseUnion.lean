import JSP000930NegativeExactProjectedRelativeCCC

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
  JSP000933.OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem countable_union_of_bounded_rows_bounded
    (hB : BoundsCountableOmegaOneNames B) (V : ℕ → OmegaOneIndex → B)
    (hb : ∀ n,unboundedValue (V n) = ⊥) :
    unboundedValue (fun i => ⨆ n,V n i) = ⊥ := by
  let W (n : ℕ) (b : OmegaOneIndex) := (aboveValue (V n) b)ᶜ
  let C (c : OmegaOneIndex) := ⨅ n : ℕ,⨆ b : {j : OmegaOneIndex // j < c},W n b.val
  have hW (n : ℕ) : (⨆ b,W n b) = ⊤ := by
    have h := congrArg (fun r : B => rᶜ) (hb n)
    simpa only [unboundedValue,compl_iInf,compl_bot,W] using h
  have hC : (⨆ c,C c) = ⊤ :=
    top_unique ((le_iInf (fun n => (hW n).ge)).trans (hB W))
  have hLate (c i : OmegaOneIndex) (hi : c < i) (n : ℕ) :
      C c ≤ (V n i)ᶜ := by
    apply (iInf_le _ n).trans
    apply iSup_le
    intro b
    exact compl_le_compl (le_iSup (fun j : {j : OmegaOneIndex // b.val < j} => V n j.val)
      ⟨i,b.property.trans hi⟩)
  apply compl_eq_top.mp
  apply top_unique
  rw [← hC]
  apply iSup_le
  intro c
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  apply (inf_le_inf le_rfl (iInf_le _ c)).trans
  unfold aboveValue
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  rw [inf_iSup_eq]
  apply iSup_le
  intro n
  exact (disjoint_iff_inf_le.mp (le_compl_iff_disjoint_right.mp (hLate c i.val i.property n)))

variable {A D : Type} [CompleteBooleanAlgebra A] [CompleteBooleanAlgebra D]

noncomputable def prefixInterior (F : CompleteValueMap A D) (x : D) : A :=
  ⨆ a : {a : A // F.toFun a ≤ x},a.val

theorem prefixInterior_image_le (F : CompleteValueMap A D) (x : D) :
    F.toFun (prefixInterior F x) ≤ x := by
  unfold prefixInterior
  rw [F.map_iSup]
  exact iSup_le fun a => a.property

theorem prefixInterior_disjoint (F : CompleteValueMap A D) {x y : D} (h : Disjoint x y) :
    Disjoint (prefixInterior F x) (prefixInterior F y) := by
  apply disjoint_iff_inf_le.mpr
  apply F.reflect_le_r93
  rw [F.map_inf,F.map_bot]
  exact disjoint_iff_inf_le.mp (h.mono (prefixInterior_image_le F x) (prefixInterior_image_le F y))

theorem projectedCCC_of_countable_dense_union
    (hB : BoundsCountableOmegaOneNames B) {A : ℕ → Type}
    [∀ n,CompleteBooleanAlgebra (A n)]
    (F : ∀ n,CompleteValueMap (A n) D) (π : D → B) (π₀ : ∀ n,A n → B)
    (hπ : ∀ {I : Type} (f : I → D),π (⨆ i,f i) = ⨆ i,π (f i))
    (hCoherent : ∀ n a,π ((F n).toFun a) = π₀ n a)
    (hCCC : ∀ n,ProjectedAntichainCCC (π₀ n))
    (hDense : ∀ x : D,x ≠ ⊥ → ∃ (n : ℕ) (a : A n),
      (F n).toFun a ≠ ⊥ ∧ (F n).toFun a ≤ x) :
    ProjectedAntichainCCC π := by
  intro x hx
  let T (n : ℕ) (i : OmegaOneIndex) := prefixInterior (F n) (x i)
  have hRepr (i : OmegaOneIndex) : x i = ⨆ n,(F n).toFun (T n i) := by
    apply le_antisymm _ (iSup_le fun n => prefixInterior_image_le (F n) _)
    by_contra h
    let p := x i ⊓ (⨆ n,(F n).toFun (T n i))ᶜ
    have hp : p ≠ ⊥ := fun he =>
      h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨n,a,ha,hap⟩ := hDense p hp
    have ht : a ≤ T n i := le_iSup (fun t : {t : A n // (F n).toFun t ≤ x i} => t.val)
      ⟨a,hap.trans inf_le_left⟩
    have hj : (F n).toFun a ≤ ⨆ n,(F n).toFun (T n i) :=
      ((F n).monotone ht).trans (le_iSup (fun n => (F n).toFun (T n i)) n)
    exact ha (disjoint_compl_right.out _ hj (hap.trans inf_le_right))
  have hRows (i : OmegaOneIndex) : π (x i) = ⨆ n,π₀ n (T n i) := by
    rw [hRepr i,hπ]
    exact iSup_congr fun n => hCoherent n (T n i)
  simp only [hRows]
  exact countable_union_of_bounded_rows_bounded hB (fun n i => π₀ n (T n i))
    (fun n => hCCC n (T n) (fun i j h => prefixInterior_disjoint (F n) (hx i j h)))

end JSP000930.Negative

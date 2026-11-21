import JSP000930PositiveCohenBitCylinders
import JSP000933BooleanRealEquality
import Mathlib.Data.Set.Finite.Basic

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B]

noncomputable def cohenRow (B : Type) [CompleteBooleanAlgebra B] (i : I) :
    ℕ → CohenBA B (I × ℕ) :=
  fun n => bitSlice B (i,n) true

theorem fresh_column (p : Trace (I × ℕ)) :
    ∃ n : ℕ, ∀ i : I, (i,n) ∉ p.1.dom := by
  obtain ⟨n,hn⟩ := (p.1.dom.image Prod.snd).exists_notMem
  exact ⟨n,fun i hi => hn (Finset.mem_image.mpr ⟨(i,n),hi,rfl⟩)⟩

theorem extends_with_disagreeing_fresh_rows (p : Trace (I × ℕ))
    {i j : I} (hij : i ≠ j) :
    ∃ q : Trace (I × ℕ), q ≤ p ∧ ∃ n : ℕ,
      Prescribes q (i,n) true ∧ Prescribes q (j,n) false := by
  classical
  obtain ⟨n,hn⟩ := fresh_column p
  let t := prescribe p.1 (i,n) true
  let u := prescribe t (j,n) false
  have hj : (j,n) ∉ t.dom := by
    intro he
    change (j,n) ∈ insert (i,n) p.1.dom at he
    rcases Finset.mem_insert.mp he with h | h
    · exact hij (congrArg Prod.fst h).symm
    · exact hn j h
  have htp : Extends t p.1 := prescribe_extends p.1 (i,n) true (hn i)
  have hut : Extends u t := prescribe_extends t (j,n) false hj
  have ht := prescribe_sets p.1 (i,n) true
  have hu := prescribe_sets t (j,n) false
  let q := normalize u
  have hqu : Extends q.1 u := normalized_extends u
  have hqt : Extends q.1 t := extends_trans hqu hut
  exact ⟨q,extends_trans hqt htp,n,
    ⟨hqt.1 ht.1,(hqt.2 _ ht.1).trans ht.2⟩,
    ⟨hqu.1 hu.1,(hqu.2 _ hu.1).trans hu.2⟩⟩

theorem cohen_rows_distinct {i j : I} (hij : i ≠ j) :
    realEqValue (cohenRow B i) (cohenRow B j) = ⊥ := by
  apply value_eq_bot_of_dense_avoidance
  intro p hp
  obtain ⟨q,hq⟩ := imageCondition_dense_r50 p hp
  obtain ⟨t,ht,n,hx,hy⟩ := extends_with_disagreeing_fresh_rows q.trace hij
  let r : TotalCondition (valuedCohen B (I × ℕ)) := ⟨q.mask,t,q.nonzero,le_top⟩
  have hr : r ≤ q := (cohen_total_le_iff _ _).mpr ⟨le_rfl,ht⟩
  refine ⟨imageCondition r,imageCondition_ne_bot_r50 r,
    (imageCondition_mono_r50 hr).trans hq,?_⟩
  let a := imageCondition r ⊓ realEqValue (cohenRow B i) (cohenRow B j)
  have ha₁ : a ≤ cohenRow B i n :=
    inf_le_left.trans (image_le_bitSlice r (i,n) true hx)
  have ha₂ : a ≤ (cohenRow B j n)ᶜ := by
    change a ≤ (bitSlice B (j,n) true)ᶜ
    rw [← bitSlice_false_eq_compl_true]
    exact inf_le_left.trans (image_le_bitSlice r (j,n) false hy)
  have he := (le_realEqValue_iff_r126 a (cohenRow B i) (cohenRow B j)).mp
    inf_le_right n
  have ha₃ : a ≤ cohenRow B j n := by
    rw [inf_eq_left.mpr ha₁] at he
    exact he.le.trans inf_le_right
  exact le_bot_iff.mp ((le_inf ha₃ ha₂).trans
    (disjoint_iff_inf_le.mp (disjoint_compl_right :
      Disjoint (cohenRow B j n) (cohenRow B j n)ᶜ)))

end JSP000930.Positive.Cohen

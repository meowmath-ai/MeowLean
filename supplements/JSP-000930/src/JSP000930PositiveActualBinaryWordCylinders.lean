import JSP000930PositiveOneReserveUnboundedFamily
import JSP000930PositiveRationalDyadicCylinders
import Mathlib.Data.Finset.Lattice.Fold

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B I : Type} [CompleteBooleanAlgebra B]

def WordMatches (p : Trace (I × ℕ)) (i : I) (w : List Bool) : Prop :=
  ∀ n : Fin w.length, Prescribes p (i,n.val) (w.get n)

def rowNatEmbedding (i : I) : ℕ ↪ I × ℕ :=
  ⟨fun n => (i,n),fun _ _ h => congrArg Prod.snd h⟩

def wordConstraint (i : I) (w : List Bool) : Condition (I × ℕ) :=
  ⟨(Finset.range w.length).map (rowNatEmbedding i),
    fun a => (w[a.2]?).getD false⟩

theorem mem_wordConstraint (i : I) (w : List Bool) (a : I × ℕ) :
    a ∈ (wordConstraint i w).dom ↔ a.1 = i ∧ a.2 < w.length := by
  change a ∈ (Finset.range w.length).map (rowNatEmbedding i) ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨n,hn,h⟩
    exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h) ▸ Finset.mem_range.mp hn⟩
  · rintro ⟨hi,hn⟩
    exact ⟨a.2,Finset.mem_range.mpr hn,Prod.ext hi.symm rfl⟩

theorem wordConstraint_bit (i : I) (w : List Bool) (n : Fin w.length) :
    (wordConstraint i w).bit (i,n.val) = w.get n := by
  change (w[n.val]?).getD false = w[n.val]'n.isLt
  simp [n.isLt]

theorem extends_word_of_agrees (p : Trace (I × ℕ)) (i : I) (w : List Bool)
    (h : ∀ n : Fin w.length, (i,n.val) ∈ p.1.dom → p.1.bit (i,n.val) = w.get n) :
    ∃ q : Trace (I × ℕ), q ≤ p ∧ WordMatches q i w := by
  classical
  let a := wordConstraint i w
  obtain ⟨q,hp,ha⟩ := (common_extension_iff p.1 a).mpr (by
    rintro ⟨j,n⟩ hp hq
    obtain ⟨he,hn⟩ := (mem_wordConstraint i w (j,n)).mp hq
    change j = i at he
    subst j
    exact (h ⟨n,hn⟩ hp).trans (wordConstraint_bit i w ⟨n,hn⟩).symm)
  let t := normalize q
  have ht : Extends t.1 a := extends_trans (normalized_extends q) ha
  refine ⟨t,extends_trans (normalized_extends q) hp, fun n => ?_⟩
  have hn : (i,n.val) ∈ a.dom := (mem_wordConstraint i w _).mpr ⟨rfl,n.isLt⟩
  exact ⟨ht.1 hn,(ht.2 _ hn).trans (wordConstraint_bit i w n)⟩

theorem exists_initialWord_for_append (p : Trace (I × ℕ)) (i : I) :
    ∃ u : List Bool, ∀ v : List Bool,
      ∃ q : Trace (I × ℕ), q ≤ p ∧ WordMatches q i (u ++ v) := by
  let N := ((p.1.dom.image Prod.snd).sup id) + 1
  let u := List.ofFn (fun k : Fin N => p.1.bit (i,k.val))
  refine ⟨u,fun v => extends_word_of_agrees p i (u ++ v) ?_⟩
  intro n hn
  have he : n.val ≤ (p.1.dom.image Prod.snd).sup id :=
    Finset.le_sup (f := id) (show n.val ∈ p.1.dom.image Prod.snd from
      Finset.mem_image.mpr ⟨(i,n.val),hn,rfl⟩)
  have hN : n.val < N := Nat.lt_succ_of_le he
  have hu : n.val < u.length := by simpa only [u,List.length_ofFn] using hN
  change p.1.bit (i,n.val) = (u ++ v)[n.val]'n.isLt
  rw [List.getElem_append_left hu]
  simp only [u,List.getElem_ofFn]

noncomputable def wordValue (B : Type) [CompleteBooleanAlgebra B]
    (i : I) (w : List Bool) : CohenBA B (I × ℕ) :=
  ⨅ n : Fin w.length, bitSlice B (i,n.val) (w.get n)

theorem image_le_wordValue (p : TotalCondition (valuedCohen B (I × ℕ)))
    (i : I) (w : List Bool) (h : WordMatches p.trace i w) :
    imageCondition p ≤ wordValue B i w :=
  le_iInf fun n => image_le_bitSlice p (i,n.val) (w.get n) (h n)

theorem meets_dense_word_family (i : I) (D : List Bool → Prop)
    (hD : ∀ u,∃ v,D (u ++ v)) :
    (⨆ w : {w : List Bool // D w},wordValue B i w.val) = ⊤ := by
  apply compl_eq_bot.mp
  apply value_eq_bot_of_dense_avoidance
  intro p hp
  obtain ⟨t,ht⟩ := imageCondition_dense_r50 p hp
  obtain ⟨u,hu⟩ := exists_initialWord_for_append t.trace i
  obtain ⟨v,hv⟩ := hD u
  obtain ⟨q,hqt,hq⟩ := hu v
  let r : TotalCondition (valuedCohen B (I × ℕ)) := ⟨t.mask,q,t.nonzero,le_top⟩
  have hr : r ≤ t := (cohen_total_le_iff _ _).mpr ⟨le_rfl,hqt⟩
  have hs : imageCondition r ≤ ⨆ w : {w : List Bool // D w},wordValue B i w.val :=
    (image_le_wordValue r i (u ++ v) hq).trans (le_iSup (fun w : {w : List Bool // D w} => wordValue B i w.val) ⟨u ++ v,hv⟩)
  exact ⟨imageCondition r,imageCondition_ne_bot_r50 r,
    (imageCondition_mono_r50 hr).trans ht,(disjoint_compl_right.mono_left hs).eq_bot⟩

end JSP000930.Positive.Cohen

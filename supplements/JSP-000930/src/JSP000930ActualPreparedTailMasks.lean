import JSP000930ActualMaskedSurvivorTower
import JSP000930PreparedPaletteCheckedTailCover

namespace JSP000930.Negative

open JSP000930.MixedPalettes
open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.RelativeOCA JSP000933.OpenGraphForcing
open scoped Cardinal

noncomputable def orderedWetzelPairs (s : Finset GroundContinuumSuccIndex) :
    Finset (GroundContinuumSuccIndex × GroundContinuumSuccIndex) :=
  (s.product s).filter (fun p => p.2<p.1)

theorem labelAgreement_comm930 {B : Type} [CompleteBooleanAlgebra B] (L R : Label B) :
    labelAgreement L R = labelAgreement R L := by
  unfold labelAgreement
  exact iSup_congr (fun _ => inf_comm _ _)

open scoped Classical

noncomputable def preparedJointTailMark (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (d : Set.Iio a) : PreparedBA :=
  ⨅ p : orderedWetzelPairs s,⨅ j : Set.Iio a,
    if j<d then ⊤ else
      (labelAgreement (preparedWetzelRows p.val.1 j.val) (preparedWetzelRows p.val.2 j.val))ᶜ

theorem preparedJointTailMark_covers (a : GroundContinuumSuccIndex) (s : Finset GroundContinuumSuccIndex)
    (hL : CheckedGroundLimit a) (hJ : ∀ g : ℕ → Set.Iio a,∃ d : Set.Iio a,∀ n,g n<d) :
    (⨆ d : Set.Iio a,preparedJointTailMark a s d) = ⊤ := by
  obtain ⟨j,hj⟩ := hL.1
  letI : Nonempty (↥(Set.Iio a)) := ⟨⟨j,hj⟩⟩
  apply top_unique
  exact prepared_palette_checkedTail_cover (Set.Iio a) hJ (orderedWetzelPairs s)
    (fun p hp => (Finset.mem_filter.mp hp).2)

private theorem orderedWetzelPairs_mem {s : Finset GroundContinuumSuccIndex} (i j : s)
    (h : j.val < i.val) : (i.val,j.val) ∈ orderedWetzelPairs s := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨i.property,j.property⟩,h⟩

theorem preparedJointTailMark_separates (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (d : Set.Iio a) {j : GroundContinuumSuccIndex}
    (hd : d.val≤j) (hj : j<a) (i k : s) (hik : i≠k) :
    preparedJointTailMark a s d ≤
      (labelAgreement (preparedWetzelRows i.val j) (preparedWetzelRows k.val j))ᶜ := by
  have hn : i.val≠k.val := fun he => hik (Subtype.ext he)
  have hOr (x y : s) (hlt : y.val<x.val) :
      preparedJointTailMark a s d ≤
        (labelAgreement (preparedWetzelRows x.val j) (preparedWetzelRows y.val j))ᶜ := by
    let p : orderedWetzelPairs s := ⟨(x.val,y.val),orderedWetzelPairs_mem x y hlt⟩
    let r : Set.Iio a := ⟨j,hj⟩
    have h := (iInf_le (fun p : orderedWetzelPairs s => ⨅ r : Set.Iio a, if r<d then ⊤ else
      (labelAgreement (preparedWetzelRows p.val.1 r.val) (preparedWetzelRows p.val.2 r.val))ᶜ) p).trans
      (iInf_le _ r)
    exact (h.trans_eq (ite_eq_right (not_lt_of_ge hd)))
  rcases lt_or_gt_of_ne hn with h|h
  · rw [labelAgreement_comm930]
    exact hOr k i h
  · exact hOr i k h

theorem openWetzelTail_card_le_continuum {d a : GroundContinuumSuccIndex} :
    Cardinal.mk (OpenWetzelTail d a) ≤ 𝔠 := by
  let f (i : OpenWetzelTail d a) : Set.Iio a := ⟨i.val,i.property.2⟩
  have hf : Function.Injective f := fun i j h => Subtype.ext (congrArg (fun x : Set.Iio a => x.val) h)
  exact (Cardinal.mk_le_of_injective hf).trans
    (Order.lt_succ_iff.mp (continuumSuccInitial_card_lt_r406 a))

end JSP000930.Negative

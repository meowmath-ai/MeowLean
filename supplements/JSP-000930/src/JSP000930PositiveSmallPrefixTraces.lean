import JSP000930PositiveActualCohenCoordinates

namespace JSP000930.Positive.Cohen

open Cardinal JSP000933.PreparedModel JSP000933.OpenGraphForcing JSP000933.RelativeOCA

variable {X : Type} {S : Set X}

theorem traceGraph_inside_block (p : BlockTrace S) (y : X × Bool)
    (hy : y ∈ traceGraph p.1) : y.1 ∈ S :=
  p.2 y.1 ((mem_traceGraph p.1 y.1 y.2).mp hy).1

noncomputable def blockGraph (p : BlockTrace S) : Finset (↥S × Bool) := by
  classical
  exact (traceGraph p.1).attach.image
    (fun y => (⟨y.val.1,traceGraph_inside_block p y.val y.property⟩,y.val.2))

theorem erase_blockGraph (p : BlockTrace S) :
    (blockGraph p).image (fun y : ↥S × Bool => (y.1.val,y.2)) = traceGraph p.1 := by
  classical
  ext y
  simp only [blockGraph,Finset.mem_image,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨z, ⟨w, hw⟩, hz⟩
    have he : w.val = y := by
      simpa only [← hz] using congrArg
        (fun pair : ↥S × Bool => (pair.1.val,pair.2)) hw
    exact he ▸ w.property
  · intro hy
    let w : ↥(traceGraph p.1) := ⟨y,hy⟩
    exact ⟨(⟨y.1,traceGraph_inside_block p y hy⟩,y.2),⟨w,rfl⟩,rfl⟩

theorem blockGraph_injective : Function.Injective (blockGraph (S := S)) := by
  intro p q h
  apply Subtype.ext
  apply traceGraph_injective
  rw [← erase_blockGraph p,← erase_blockGraph q,h]

theorem blockTrace_card_le {c : Cardinal} (hc : ℵ₀ ≤ c)
    (hS : Cardinal.mk (↥S) ≤ c) : Cardinal.mk (BlockTrace S) ≤ c := by
  apply (Cardinal.mk_le_of_injective (blockGraph_injective (S := S))).trans
  apply finite_family_card_le _ hc
  simp only [Cardinal.mk_prod,Cardinal.lift_id]
  exact Cardinal.mul_le_of_le hc hS (Cardinal.mk_le_aleph0.trans hc)

def bulkPrefixCoordinateCode (a : GroundContinuumSuccIndex)
    (x : ↥(bulkPrefix a)) : (↥(Set.Iio a) ⊕ OmegaOneIndex) × ℕ := by
  obtain ⟨⟨i,n⟩,hx⟩ := x
  cases i with
  | inl j => exact (Sum.inl ⟨j,hx⟩,n)
  | inr j => exact (Sum.inr j,n)

theorem bulkPrefixCoordinateCode_injective (a : GroundContinuumSuccIndex) :
    Function.Injective (bulkPrefixCoordinateCode a) := by
  let F : (↥(Set.Iio a) ⊕ OmegaOneIndex) × ℕ → WetzelCoordinate :=
    fun y => (Sum.elim (fun j => Sum.inl j.val) Sum.inr y.1,y.2)
  have hF : ∀ x : ↥(bulkPrefix a), F (bulkPrefixCoordinateCode a x) = x.val := by
    rintro ⟨⟨j,n⟩,hj⟩
    cases j <;> rfl
  intro x y h
  exact Subtype.ext ((hF x).symm.trans ((congrArg F h).trans (hF y)))

theorem bulkPrefixCoordinate_card (a : GroundContinuumSuccIndex) :
    Cardinal.mk (↥(bulkPrefix a)) ≤ 𝔠 := by
  apply (Cardinal.mk_le_of_injective (bulkPrefixCoordinateCode_injective a)).trans
  simp only [Cardinal.mk_prod,Cardinal.mk_sum,Cardinal.lift_id,Cardinal.mk_nat,
    mk_OmegaOneIndex_r61]
  apply Cardinal.mul_le_of_le Cardinal.aleph0_le_continuum _ Cardinal.aleph0_le_continuum
  exact Cardinal.add_le_of_le Cardinal.aleph0_le_continuum
    (Order.lt_succ_iff.mp (continuumSuccInitial_card_lt_r406 a)) Cardinal.aleph_one_le_continuum

theorem bulkPrefixTrace_card (a : GroundContinuumSuccIndex) :
    Cardinal.mk (BlockTrace (bulkPrefix a)) ≤ 𝔠 :=
  blockTrace_card_le Cardinal.aleph0_le_continuum (bulkPrefixCoordinate_card a)

end JSP000930.Positive.Cohen

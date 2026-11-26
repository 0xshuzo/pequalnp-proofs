import PEqualNP.Outside.L_meta_9752

namespace PEqualNP.Outside.L_meta_9750.Optional
open PEqualNP.Outside.L_meta_9752.Engine

theorem twoBanks {u : Bool} {T z : Sig} {raw : List Sig} {L : Nat}
    (pr : proper T) (plain : plainWord T = true)
    (inputsOK : (z :: raw).all plainWord = true)
    (need : ∀ w ∈ raw, Essential T (z :: raw) w)
    (bare : Impossible u T L raw.toFinset)
    (marked : Impossible u T L (insert z raw.toFinset)) :
    Lower u (z :: raw) T (L+1) := by
  intro p bs init hit
  obtain ⟨k,S,hk,live,sub⟩ := reach_live pr plain inputsOK init hit
  have necessary : raw.toFinset ⊆ S := by
    intro w hw
    obtain ⟨r,s,hT,hrest⟩ := need w (List.mem_toFinset.mp hw)
    exact raw_required live (z::raw) w sub r s hT hrest
  by_contra! small
  by_cases hz : z ∈ S
  · have he : S = insert z raw.toFinset := by
      ext w
      constructor
      · intro hw
        rcases List.mem_cons.mp (sub w hw) with rfl | hu
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hu)
      · intro hw
        rcases Finset.mem_insert.mp hw with rfl | hu
        · exact hz
        · exact necessary hu
    exact marked k (by omega) (he ▸ live)
  · have he : S = raw.toFinset := by
      apply Finset.Subset.antisymm _ necessary
      intro w hw
      rcases List.mem_cons.mp (sub w hw) with rfl | h
      · exact False.elim (hz hw)
      · exact List.mem_toFinset.mpr h
    exact bare k (by omega) (he ▸ live)

def endpoint (r : Fin 4) : Nat := ([2,4,6,9] : List Nat).getD r.val 0
def signal (i : Fin 11) : Sig := inputs.getD i.val zero
def firstOr (r : Fin 4) : Sig := inputs.getD 0 zero ||| inputs.getD (endpoint r) zero
def loTable : Array Nat := #[36,256,129,64,32,1,8,4,2,1,1,528,256,128,64,65,1,8,4,2,1,1,96,256,128,64,32,1,9,4,2,1,1,512,256,128,64,32,1,8,4,2,1,1]
def lo (r : Fin 4) (i : Fin 11) : Row := Fin.ofNat 2048 ((loTable[11*r.val+i.val]?).getD 0)
def hi (r : Fin 4) (i : Fin 11) : Row :=
  Fin.ofNat 2048 ((lo r i).val ^^^ (1 <<< i.val))
set_option maxHeartbeats 0
set_option maxRecDepth 16000
theorem probes : ∀ r : Fin 4, ∀ i : Fin 11,
    bit (lo r i) graph ≠ bit (hi r i) graph ∧
    bit (lo r i) (firstOr r) = bit (hi r i) (firstOr r) ∧
    ∀ j : Fin 11, j ≠ i → bit (lo r i) (signal j) = bit (hi r i) (signal j) := by decide +kernel

theorem allRaw (r : Fin 4) (w : Sig) (hw : w ∈ inputs) : Essential graph (firstOr r :: inputs) w := by
  rw [←input_list] at hw
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  obtain ⟨hT,ho,hs⟩ := probes r i
  refine ⟨lo r i,hi r i,hT,?_⟩
  intro v mem diff
  rcases List.mem_cons.mp mem with rfl | hv
  · exact ho
  · rw [←input_list] at hv
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
    exact hs j (fun eq => diff (congrArg signal eq))

theorem optionalOr (r : Fin 4) {L : Nat}
    (bare : Impossible true graph L inputs.toFinset)
    (marked : Impossible true graph L (insert (firstOr r) inputs.toFinset)) :
    Lower true (firstOr r :: inputs) graph (L+1) := by
  apply twoBanks graph_proper (by decide +kernel) _ (allRaw r) bare marked
  exact (by decide +kernel : ∀ j : Fin 4, (firstOr j :: inputs).all plainWord = true) r

end PEqualNP.Outside.L_meta_9750.Optional

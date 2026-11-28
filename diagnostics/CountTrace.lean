import PEqualNP.Defs
namespace Research9815.Count
open Finset
abbrev Pair := Nat × Nat
def put (n : Nat) (L : List Nat) := if n∈L then L else n::L
def putPair (p : Pair) (L : List Nat) := put p.1 (put p.2 L)
def blocked (k : Nat) (opts : List (List Pair)) (used : List Nat) : Bool :=
  if used.length>k then true else match opts with
  | [] => false
  | L::Ls => L.all (fun p => blocked k Ls (putPair p used))
def fits (H : Finset Nat) (p : Pair) := p.1∈H ∧ p.2∈H
theorem put_nd (n : Nat) {L : List Nat} (nd : L.Nodup) : (put n L).Nodup := by
  by_cases h : n∈L <;> simp [put,h,nd]
theorem put_sub (n : Nat) (L : List Nat) (H : Finset Nat)
    (hn : n∈H) (hh : ∀j∈L,j∈H) : ∀j∈put n L,j∈H := by
  by_cases h : n∈L
  · simpa [put,h] using hh
  · intro j hj
    rcases (show j=n ∨ j∈L by simpa [put,h] using hj) with rfl|z
    · exact hn
    · exact hh _ z
theorem blocked_sound (k : Nat) (H : Finset Nat) (size : H.card≤k) (opts : List (List Pair))
    (allFit : ∀t∈opts,∃p∈t,fits H p) :
    ∀used : List Nat,used.Nodup → (∀j∈used,j∈H) → blocked k opts used=false := by
  induction opts with
  | nil =>
    intro used nd sub
    have inc : used.toFinset⊆H := fun _ h => sub _ (List.mem_toFinset.mp h)
    have sz : used.length≤k := by simpa [List.toFinset_card_of_nodup nd] using (Finset.card_le_card inc).trans size
    simp [blocked,show ¬used.length>k by omega]
  | cons L Ls ih =>
    intro used nd sub
    have inc : used.toFinset⊆H := fun _ h => sub _ (List.mem_toFinset.mp h)
    have sz : used.length≤k := by simpa [List.toFinset_card_of_nodup nd] using (Finset.card_le_card inc).trans size
    obtain ⟨p,hp,ha,hb⟩ := allFit L (by simp)
    have rem : ∀t∈Ls,∃q∈t,fits H q := fun t ht => allFit t (by simp [ht])
    have next := ih rem (putPair p used) (put_nd _ (put_nd _ nd)) (put_sub _ _ _ ha (put_sub _ _ _ hb sub))
    cases r : blocked k (L::Ls) used with
    | false => rfl
    | true =>
      have yes : L.all (fun q => blocked k Ls (putPair q used))=true := by
        simpa [blocked,show ¬used.length>k by omega] using r
      exact Bool.noConfusion ((List.all_eq_true.mp yes p hp).symm.trans next)
def bits (k a b : Nat) := match k with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def Trace (raw : Finset Nat) : List Nat → Prop
  | [] => True
  | t::s => Trace raw s ∧ ∃k<4,∃a∈raw∪s.toFinset,∃b∈raw∪s.toFinset,bits k a b=t
theorem first_parent (raw : Finset Nat) (t : Nat) (absent : t∉raw) (s : List Nat) (ok : Trace raw s) (mem : t∈s) :
    ∃k<4,∃a∈raw∪s.toFinset,∃b∈raw∪s.toFinset,t≠a ∧ t≠b ∧ bits k a b=t := by
  induction s with
  | nil => simp at mem
  | cons w s ih =>
    obtain ⟨pre,last⟩ := ok
    have ext (x : Nat) (h : x∈raw∪s.toFinset) : x∈raw∪(w::s).toFinset := by
      rcases Finset.mem_union.mp h with h|h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (by simp_all)
    by_cases earlier : t∈s
    · obtain ⟨k,hk,a,ha,b,hb,na,nb,eq⟩ := ih pre earlier
      exact ⟨k,hk,a,ext _ ha,b,ext _ hb,na,nb,eq⟩
    · have eq : t=w := (List.mem_cons.mp mem).resolve_right earlier
      obtain ⟨k,hk,a,ha,b,hb,gate⟩ := last
      have fresh : t∉raw∪s.toFinset := by simp [absent,earlier]
      exact ⟨k,hk,a,ext _ ha,b,ext _ hb,(fun z => fresh (by rw [z]; exact ha)),(fun z => fresh (by rw [z]; exact hb)),gate.trans eq.symm⟩

theorem minimum (s : List Nat) (target : Finset Nat) (k : Nat) (opts : List (List Pair))
    (targets : target⊆s.toFinset) (pass : blocked k opts []=true)
    (explain : ∀L∈opts,∃p∈L,fits (s.toFinset \ target) p) : target.card+k<s.length := by
  by_contra small
  have cnt := Finset.card_sdiff_add_card_eq_card targets
  have len := s.toFinset_card_le
  have sz : (s.toFinset \ target).card≤k := by omega
  have no := blocked_sound k _ sz opts explain [] (by simp) (by simp)
  exact Bool.noConfusion (pass.symm.trans no)
end Research9815.Count

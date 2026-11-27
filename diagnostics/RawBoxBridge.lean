import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9471.Boxes
open PEqualNP.ProofComplexity PEqualNP.Search
abbrev P := Fin 6
abbrev H := Fin 5
abbrev V := P × H
abbrev L := Literal V
abbrev C := Clause V
abbrev Box := H → P → Prop

def atVal (p : P) (l : L) : Prop := decide (p=l.1.1)=l.2

theorem opposite (p : P) (l : L) : atVal p (negLit l) ↔ ¬atVal p l := by
  rcases l with ⟨⟨a,h⟩,b⟩
  cases b <;> by_cases e : p=a <;> simp [atVal,negLit,e]

def encode (c : C) : Box := fun h p => ∃ l∈c,l.1.2=h ∧ atVal p l

def live (D : Box) := ∀ h, ∃ p, D h p
def openCell (D b : Box) (h : H) := ∃p,D h p ∧ b h p
def stable (D b : Box) :=
  (∃h,∀p,D h p → b h p) ∨ ∃h k,h≠k ∧ openCell D b h ∧ openCell D b k
def forces (D : Box) (l : L) := ∀ p,D l.1.2 p → atVal p l

theorem openAt {D : Box} {c : C} {h : H} (o : openCell D (encode c) h) :
    ∃ l∈c, l.1.2=h ∧ ∃p,D l.1.2 p ∧ atVal p l := by
  obtain ⟨p,pd,l,lc,eq,val⟩ := o
  exact ⟨l,lc,eq,p,eq.symm ▸ pd,val⟩

theorem propagate {D : Box} (inh : live D) {G : Set C}
    (ok : ∀ c∈G,stable D (encode c)) {A : Set L}
    (assumeVal : ∀ l∈A,forces D l) {l : L} (f : UPForces G A l) : forces D l := by
  induction f with
  | hyp a => exact assumeVal _ a
  | @unit c l hc hl rest ih =>
    have unique {k : L} (hk : k∈c) {q : P} (qd : D k.1.2 q) (yes : atVal q k) : k=l := by
      by_contra ne
      exact (opposite q k).mp (ih k hk ne q qd) yes
    intro p pd
    rcases ok c hc with ⟨h,all⟩ | ⟨h,k,ne,oh,ok⟩
    · by_cases eq : h=l.1.2
      · obtain ⟨a,ac,ae,yes⟩ := all p (eq.symm ▸ pd)
        have al := unique ac (by simpa only [ae,eq] using pd) yes
        exact al ▸ yes
      · obtain ⟨q,qd⟩ := inh h
        obtain ⟨a,ac,ae,yes⟩ := all q qd
        have al := unique ac (ae.symm ▸ qd) yes
        exact (eq (ae.symm.trans (congrArg (fun t : L => t.1.2) al))).elim
    · obtain ⟨u,uc,uh,q,qd,uy⟩ := openAt oh
      obtain ⟨v,vc,vk,r,rd,vy⟩ := openAt ok
      have uv := (unique uc qd uy).trans (unique vc rd vy).symm
      exact (ne ((uh.symm.trans (congrArg (fun t : L => t.1.2) uv)).trans vk)).elim

def Step (B : Set Box) (b : Box) :=
  ∀ D, live D → (∀ a∈B,stable D a) → ∃h,openCell D b h

theorem projectStep {G : Set C} {c : C} (s : IsRUP G c) : Step (encode '' G) (encode c) := by
  classical
  intro D inhabited ok
  by_contra! dead
  have base (d : C) (hd : d∈G) := ok (encode d) ⟨d,hd,rfl⟩
  have assumptions (k : L) (hk : k∈negLit '' (↑c : Set L)) : forces D k := by
    obtain ⟨a,ha,rfl⟩ := hk
    intro p pd
    apply (opposite p a).mpr
    intro yes
    exact dead a.1.2 ⟨p,pd,a,ha,rfl,yes⟩
  obtain ⟨d,hd,unsat⟩ := s
  have invalid (o : ∃ h,openCell D (encode d) h) : False := by
    obtain ⟨h,oh⟩ := o
    obtain ⟨a,ha,_,p,pd,yes⟩ := openAt oh
    exact (opposite p a).mp (propagate inhabited base assumptions (unsat a ha) p pd) yes
  apply invalid
  rcases base d hd with ⟨h,all⟩|⟨h,k,_,oh,_⟩
  · obtain ⟨q,qd⟩ := inhabited h
    exact ⟨h,q,qd,all q qd⟩
  · exact ⟨h,oh⟩

inductive Run (G : Set Box) : List Box → Prop
  | nil : Run G []
  | add {ds b} : Run G ds → Step (G ∪ {a | a∈ds}) b → Run G (b::ds)

theorem project {G : Set C} {cs : List C} (r : IsRUPRun G cs) : Run (encode '' G) (cs.map encode) := by
  induction r with
  | nil => exact .nil
  | @learn ds c hist step ih =>
    apply Run.add ih
    have e : encode '' (G ∪ {a | a∈ds}) = encode '' G ∪ {a | a∈ds.map encode} := by
      ext b
      constructor
      · rintro ⟨a,ha,rfl⟩
        rcases ha with h | h
        · exact Or.inl ⟨a,h,rfl⟩
        · exact Or.inr (List.mem_map.mpr ⟨a,h,rfl⟩)
      · rintro (⟨a,h,rfl⟩|h)
        · exact ⟨a,Or.inl h,rfl⟩
        · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
          exact ⟨a,Or.inr ha,rfl⟩
    rw [←e]
    exact projectStep step

theorem originalBound (h : ∃ cs : List C, IsRUPRun (PHP 6 5) cs ∧ ∅∈cs ∧ cs.length≤20) :
    ∃ bs : List Box, Run (encode '' PHP 6 5) bs ∧ encode ∅∈bs ∧ bs.length≤20 := by
  obtain ⟨cs,h,ending,len⟩ := h
  exact ⟨cs.map encode,project h,List.mem_map.mpr ⟨∅,ending,rfl⟩,by simpa using len⟩

namespace RawBridge
def row (p : P) : C := Finset.univ.image (fun h : H => ((p,h),true))
def rawCode (p : P) : Nat := 17043521 * 2 ^ p.val
def bits (n : Nat) : Box := fun h p => n.testBit (6*h.val+p.val)=true
def rawCodes : List Nat := [17043521,34087042,68174084,136348168,272696336,545392672]
def finiteRaw : Set Box := {b | ∃a∈rawCodes,b=bits a}

theorem codes : ∀ p : P,rawCode p∈rawCodes := by decide +kernel
theorem fields : ∀ (p : P) (h : H) (q : P), (rawCode p).testBit (6*h.val+q.val)=decide (q=p) := by decide +kernel

theorem rowEq (p : P) : encode (row p)=bits (rawCode p) := by
  funext h q
  apply propext
  rw [show bits (rawCode p) h q ↔ q=p by simp [bits,fields]]
  constructor
  · rintro ⟨l,hl,_,yes⟩
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    simpa [atVal] using yes
  · intro eq
    refine ⟨((p,h),true),Finset.mem_image.mpr ⟨h,Finset.mem_univ _,rfl⟩,rfl,?_⟩
    simp [atVal,eq]

theorem finiteRawSubset : finiteRaw ⊆ encode '' PHP 6 5 := by
  rintro b ⟨n,hn,rfl⟩
  have listed : ∀ n∈rawCodes,∃p : P,rawCode p=n := by
    intro n mem
    simp only [rawCodes,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  obtain ⟨p,rfl⟩ := listed n hn
  exact ⟨row p,Or.inl ⟨p,rfl⟩,rowEq p⟩

theorem rawStable (D : Box) (ok : ∀b∈finiteRaw,stable D b) :
    ∀b∈encode '' PHP 6 5,stable D b := by
  rintro _ ⟨c,hc,rfl⟩
  rcases hc with ⟨i,rfl⟩|⟨p,q,j,ne,rfl⟩
  · apply ok
    exact ⟨rawCode i,codes i,rowEq i⟩
  · left
    refine ⟨j,?_⟩
    intro v _
    by_cases vp : v=p
    · have vq : v≠q := fun eq=>ne (vp.symm.trans eq)
      exact ⟨((q,j),false),by simp,rfl,by simp [atVal,vq]⟩
    · exact ⟨((p,j),false),by simp,rfl,by simp [atVal,vp]⟩

theorem changeBase {G K : Set Box}
    (imp : ∀D,live D → (∀a∈K,stable D a) → ∀a∈G,stable D a)
    {xs : List Box} (r : Run G xs) : Run K xs := by
  induction r with
  | nil => exact .nil
  | @add ds b prev step ih =>
    apply Run.add ih
    intro D inh st
    apply step D inh
    intro c hc
    rcases hc with g|old
    · exact imp D inh (fun a ha=>st a (Or.inl ha)) c g
    · exact st c (Or.inr old)

theorem bases {xs : List Box} : Run (encode '' PHP 6 5) xs ↔ Run finiteRaw xs :=
  ⟨changeBase (fun D _ => rawStable D),changeBase (fun _ _ st a ha => st a (finiteRawSubset ha))⟩

theorem physicalToFinite {cs : List C} (r : IsRUPRun (PHP 6 5) cs) :
    Run finiteRaw (cs.map encode) := bases.mp (project r)

end RawBridge
end PEqualNP.Outside.L_meta_9471.Boxes

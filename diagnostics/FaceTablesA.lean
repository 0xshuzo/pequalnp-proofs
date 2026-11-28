import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_178.Restrict
open PEqualNP.ProofComplexity Finset

structure Frame (V U : Type) where
  form : Finset V → Finset U
  flip : Finset V → Bool

variable {V U : Type} [DecidableEq V] [DecidableEq U]
def imageEq (T : Frame V U) (q : LinEq V) : LinEq U :=
  (T.form q.1, if T.flip q.1 then !q.2 else q.2)
def top (T : Frame V U) (C : LinClause V) : Prop :=
  (∅, false) ∈ C.image (imageEq T)
def body (T : Frame V U) (C : LinClause V) : LinClause U :=
  (C.image (imageEq T)).erase (∅,true)


end PEqualNP.Outside.L_pcx_178.Restrict
namespace PEqualNP.Outside.L_pcx_178.Restrict
open PEqualNP.ProofComplexity Finset
variable {V U : Type} [DecidableEq V] [DecidableEq U]

instance topDec (T : Frame V U) (C : LinClause V) : Decidable (top T C) :=
  inferInstanceAs (Decidable ((∅,false) ∈ C.image (imageEq T)))

end PEqualNP.Outside.L_pcx_178.Restrict
namespace PEqualNP.Outside.L_pcx_178.Restrict
open PEqualNP.ProofComplexity Finset
abbrev Big := Fin 5 × Fin 4
abbrev Little := Fin 4 × Fin 3
def emb (p : Fin 5) (h : Fin 4) (z : Little) : Big := (p.succAbove z.1,h.succAbove z.2)
theorem injT : ∀ p h (u v : Little), emb p h u=emb p h v → u=v := by decide +kernel
theorem awayT : ∀ p h (u : Little), emb p h u≠(p,h) := by decide +kernel
def face (p : Fin 5) (h : Fin 4) : Frame Big Little :=
  ⟨fun f => univ.filter fun z => emb p h z∈f, fun f => decide ((p,h)∈f)⟩
def extend (p : Fin 5) (h : Fin 4) (x : Little→Bool) (z : Big) :=
  decide (z=(p,h) ∨ ∃ u, emb p h u=z ∧ x u=true)

theorem faceEval (p : Fin 5) (h : Fin 4) (x : Little→Bool) (q : LinEq Big) :
    LinEqSat (extend p h x) q ↔ LinEqSat x (imageEq (face p h) q) := by
  classical
  rcases q with ⟨f,b⟩
  let K := ((face p h).form f).filter fun z => x z=true
  let I := K.image (emb p h)
  have ik : I.card=K.card := card_image_of_injective _ (injT p h)
  have memI (z : Big) : z∈I ↔ ∃ u, emb p h u=z ∧ emb p h u∈f ∧ x u=true := by
    change z∈K.image (emb p h) ↔ _
    simp only [mem_image, K, mem_filter, face, mem_univ,true_and]
    constructor
    · rintro ⟨u,hu,e⟩
      exact ⟨u,e,hu⟩
    · rintro ⟨u,e,hu⟩
      exact ⟨u,hu,e⟩
  have off : (p,h)∉I := fun hh => by obtain ⟨u,e,_⟩ := (memI _).1 hh; exact awayT p h u e
  let D := f.filter fun z => extend p h x z=true
  have memD (z : Big) : z∈D ↔ z∈f ∧ (z=(p,h) ∨ ∃ u, emb p h u=z ∧ x u=true) := by
    simp [D,extend]
  by_cases pin : (p,h)∈f
  · have eq : D=insert (p,h) I := by
      ext z
      rw [memD,mem_insert,memI]
      constructor
      · rintro ⟨hz,e|⟨u,e,on⟩⟩
        · exact Or.inl e
        · exact Or.inr ⟨u,e,by simpa only [e] using hz,on⟩
      · rintro (e|⟨u,e,hu,on⟩)
        · exact ⟨by simpa only [e] using pin,Or.inl e⟩
        · exact ⟨by simpa only [e] using hu,Or.inr ⟨u,e,on⟩⟩
    have cards : D.card=K.card+1 := by rw [eq,card_insert_of_notMem off,ik]
    change (Odd D.card ↔ b=true) ↔ (Odd K.card ↔ (if decide ((p,h)∈f) then !b else b)=true)
    rw [cards]
    cases b <;> simp [pin,Nat.odd_iff] <;> omega
  · have eq : D=I := by
      ext z
      rw [memD,memI]
      constructor
      · rintro ⟨hz,e|⟨u,e,on⟩⟩
        · exact False.elim (pin (by simpa only [e] using hz))
        · exact ⟨u,e,by simpa only [e] using hz,on⟩
      · rintro ⟨u,e,hu,on⟩
        exact ⟨by simpa only [e] using hu,Or.inr ⟨u,e,on⟩⟩
    change (Odd D.card ↔ b=true) ↔ (Odd K.card ↔ (if decide ((p,h)∈f) then !b else b)=true)
    simp [eq,ik,pin]

def pigeon (m n : Nat) (i : Fin m) : Clause (Fin m × Fin n) := univ.image (fun j => ((i,j),true))
def collision (m n : Nat) (i k : Fin m) (j : Fin n) : Clause (Fin m × Fin n) := {((i,j),false),((k,j),false)}
def raw (m n : Nat) : Finset (LinClause (Fin m × Fin n)) :=
  (univ.image (fun i => linOfClause (pigeon m n i))) ∪
    ((univ.filter (fun v : Fin m × Fin m × Fin n => v.1≠v.2.1)).image
       (fun v => linOfClause (collision m n v.1 v.2.1 v.2.2)))
theorem raw_spec {m n : Nat} {C : LinClause (Fin m×Fin n)} :
    C∈raw m n ↔ C∈linOfClause '' PHP m n := by
  simp only [raw,mem_union,mem_image,mem_univ,mem_filter,true_and]
  constructor
  · rintro (⟨i,rfl⟩|⟨⟨i,k,j⟩,ne,rfl⟩)
    · exact ⟨_,Or.inl ⟨i,rfl⟩,rfl⟩
    · exact ⟨_,Or.inr ⟨i,k,j,ne,rfl⟩,rfl⟩
  · rintro ⟨A,(⟨i,rfl⟩|⟨i,k,j,ne,rfl⟩),rfl⟩
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr ⟨⟨i,k,j⟩,ne,rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem axTable : ∀ p h, ((raw 5 4).toList.all fun C =>
  decide (top (face p h) C ∨ body (face p h) C∈raw 4 3))=true := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem removed : ∀ p h, ((raw 5 4).filter (top (face p h))).card=23 := by decide +kernel
end PEqualNP.Outside.L_pcx_178.Restrict

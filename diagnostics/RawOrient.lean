import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_121_raw
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]

def flip (x : V→Bool) (v : V) (i : V) := if i=v then !(x i) else x i

theorem opposite {x : V→Bool} {f : Finset V} {v : V} (hv : v∈f) (b : Bool) :
    LinEqSat (flip x v) (f,b) ↔ ¬LinEqSat x (f,b) := by
  let S := (f.erase v).filter (fun i=>x i=true)
  have nv : v∉S := by simp [S]
  have h0 : f.filter (fun i=>x i=true) = (if x v then insert v S else S) := by
    ext i
    by_cases he : i=v
    · subst i
      cases hx : x v <;> simp [hx,hv,S]
    · cases hx : x v <;> simp [hx,S,he]
  have h1 : f.filter (fun i=>flip x v i=true) = (if x v then S else insert v S) := by
    ext i
    by_cases he : i=v
    · subst i
      cases hx : x v <;> simp [hx,hv,S,flip]
    · cases hx : x v <;> simp [hx,S,he,flip]
  unfold LinEqSat
  change (Odd (f.filter (fun i=>flip x v i=true)).card ↔ b=true) ↔
    ¬(Odd (f.filter (fun i=>x i=true)).card ↔ b=true)
  rw [h0,h1]
  cases xx : x v <;> cases b <;> simp [xx,Finset.card_insert_of_notMem nv,Nat.odd_iff] <;> omega

def both (u v : V) (t : V) : Bool := decide (t=u ∨ t=v)

theorem collisionSign {u v : V} (ne : u≠v) {f : Finset V}
    (h : ∀ x : V→Bool, x u=true → x v=true → ¬LinEqSat x (f,false)) :
    f={u} ∨ f={v} := by
  classical
  have hu : both u v u=true := by simp [both]
  have hv : both u v v=true := by simp [both]
  have avoids := h (both u v) hu hv
  have support : ∀ t ∈ f, t=u ∨ t=v := by
    intro t ht
    by_contra! wrong
    have e := (opposite ht false (x:=both u v)).2 avoids
    have eq1 : flip (both u v) t u=true := by simp [flip,Ne.symm wrong.1,hu]
    have eq2 : flip (both u v) t v=true := by simp [flip,Ne.symm wrong.2,hv]
    exact h _ eq1 eq2 e
  have filt : f.filter (fun t => both u v t = true) = f := by
    ext t
    simp only [Finset.mem_filter,and_iff_left_iff_imp]
    intro ht
    exact decide_eq_true (support t ht)
  have odd : Odd f.card := by
    simpa [LinEqSat,filt] using avoids
  by_cases a : u∈f
  · by_cases b : v∈f
    · have eq : f={u,v} := by ext t; simp only [Finset.mem_insert,Finset.mem_singleton]; exact ⟨support t,fun h=>h.elim (fun e=>e.symm ▸ a) (fun e=>e.symm ▸ b)⟩
      rw [eq] at odd
      simp [ne,Nat.odd_iff] at odd
    · left
      ext t
      simp only [Finset.mem_singleton]
      exact ⟨fun ht=>(support t ht).resolve_right (fun e=>b (e ▸ ht)),fun e=>e.symm ▸ a⟩
  · by_cases b : v∈f
    · right
      ext t
      simp only [Finset.mem_singleton]
      exact ⟨fun ht=>(support t ht).resolve_left (fun e=>a (e ▸ ht)),fun e=>e.symm ▸ b⟩
    · have eq : f=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro t ht
        rcases support t ht with rfl|rfl
        · exact a ht
        · exact b ht
      simp [eq] at odd

abbrev W := Fin 4 × Fin 3

theorem rawNegative {C : Clause W} (hc : C∈PHP 4 3) {D : LinClause W}
    (back : ∀ x, LinClauseSat x D → ClauseSat x C) {f : Finset W} (hf : (f,false)∈D) :
    ∃t,f={t} := by
  rcases hc with ⟨i,rfl⟩ | ⟨i,j,k,d,rfl⟩
  · have eq : LinEqSat (fun _ : W=>false) (f,false) := by simp [LinEqSat]
    obtain ⟨l,hl,win⟩ := back _ ⟨_,hf,eq⟩
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    contradiction
  · have ne : (i,k) ≠ (j,k) := fun e => d (congrArg Prod.fst e)
    have fact : ∀x : W→Bool,x (i,k)=true → x (j,k)=true → ¬LinEqSat x (f,false) := by
      intro x xi xj sat
      obtain ⟨l,hl,win⟩ := back x ⟨_,hf,sat⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at hl
      rcases hl with rfl|rfl
      · simpa [xi] using win
      · simpa [xj] using win
    rcases collisionSign ne fact with z|z
    · exact ⟨_,z⟩
    · exact ⟨_,z⟩

end PEqualNP.Outside.L_pcx_121_raw

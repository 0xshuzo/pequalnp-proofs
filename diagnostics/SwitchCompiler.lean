import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166.Switch
open PEqualNP.ProofComplexity Finset
abbrev Big := Fin 5 × Fin 4
abbrev Small := Fin 4 × Fin 3
def pigeon (m n : Nat) (i : Fin m) : Clause (Fin m × Fin n) := univ.image (fun j => ((i,j),true))
def collision (m n : Nat) (i k : Fin m) (j : Fin n) : Clause (Fin m × Fin n) :=
  {((i,j),false),((k,j),false)}
def raw (m n : Nat) : Finset (Clause (Fin m × Fin n)) :=
  (univ.image (pigeon m n)) ∪
    ((univ.filter (fun v : Fin m × Fin m × Fin n => v.1≠v.2.1)).image
       (fun v => collision m n v.1 v.2.1 v.2.2))
theorem raw_spec {m n : Nat} {C : Clause (Fin m×Fin n)} : C∈raw m n ↔ C∈PHP m n := by
  simp only [raw,mem_union,mem_image,mem_univ,mem_filter,true_and]
  constructor
  · rintro (⟨i,rfl⟩|⟨⟨i,k,j⟩,ne,rfl⟩)
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr ⟨i,k,j,ne,rfl⟩
  · rintro (⟨i,rfl⟩|⟨i,k,j,ne,rfl⟩)
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr ⟨⟨i,k,j⟩,ne,rfl⟩

def emb (p : Fin 5) (h : Fin 4) (u : Small) : Big := (p.succAbove u.1,h.succAbove u.2)
def lower (p : Fin 5) (h : Fin 4) (z : Big) : Small :=
  (⟨(z.1.val - (if p<z.1 then 1 else 0))%4, Nat.mod_lt _ (by decide)⟩,
   ⟨(z.2.val - (if h<z.2 then 1 else 0))%3, Nat.mod_lt _ (by decide)⟩)
def switch (p : Fin 5) (h : Fin 4) (u : Small) (z : Big) : Option (Small × Bool) :=
  if z=(p,h) then some (u,false)
  else if z=(p,(emb p h u).2) ∨ z=((emb p h u).1,h) then some (u,true)
  else if z=emb p h u ∨ z.1=p ∨ z.2=h then none
  else some (lower p h z,true)

def translate {A B : Type} [DecidableEq B] (f : A→Option (B×Bool)) (z : A×Bool) :
    Finset (B×Bool) :=
  match f z.1 with
  | none => ∅
  | some (w,s) => {(w,if z.2 then s else !s)}
def body {A B : Type} [DecidableEq B] (f : A→Option (B×Bool)) (c : Clause A) :=
  c.biUnion (translate f)
def paid {A B : Type} [DecidableEq A] [DecidableEq B] (f : A→Option (B×Bool)) (c : Clause A) : Bool :=
  decide (∀ z∈c, f z.1=none → z.2=true) &&
    decide (∀ z∈body f c, (z.1,!z.2)∉body f c)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem oneSwitch : let f := switch 4 3 (0,0)
    (((raw 5 4).filter (fun c=> paid f c)).image (body f))=raw 4 3 ∧
    ((raw 5 4).filter (fun c=> paid f c)).card=22 := by decide +kernel

end PEqualNP.Outside.L_pcx_166.Switch
namespace PEqualNP.Outside.L_pcx_166.Switch
open PEqualNP.ProofComplexity Finset
variable {A B : Type} [DecidableEq A] [DecidableEq B]
def flip (y : B×Bool) : B×Bool := (y.1,!y.2)
theorem twice (y : B×Bool) : flip (flip y)=y := by rcases y with ⟨a,b⟩; cases b <;> rfl
def Good (f : A→Option (B×Bool)) (c : Clause A) : Prop :=
  (∀ z∈c, f z.1=none → z.2=true) ∧ (∀ z∈body f c, flip z∉body f c)
def Join {T : Type} [DecidableEq T] (p n : Clause T) (w : T) :=
  p.erase (w,true) ∪ n.erase (w,false)
theorem monoBody (f : A→Option (B×Bool)) {a b : Clause A} (inc : a⊆b) :
    body f a⊆body f b := by
  intro z h
  obtain ⟨v,hv,mem⟩:=mem_biUnion.mp h
  exact mem_biUnion.mpr ⟨v,inc hv,mem⟩
theorem peeled {f : A→Option (B×Bool)} {c r : Clause A} {w : A×Bool}
    (inc : c.erase w⊆r) (z : B×Bool) (hz : z∈body f c) : z∈body f r ∨ z∈translate f w := by
  obtain ⟨v,hv,mem⟩:=mem_biUnion.mp hz
  by_cases eq : v=w
  · exact Or.inr (eq ▸ mem)
  · exact Or.inl (mem_biUnion.mpr ⟨v,inc (mem_erase.mpr ⟨eq,hv⟩),mem⟩)
theorem fixedClean {f : A→Option (B×Bool)} {c r : Clause A} {w : A×Bool}
    (inc : c.erase w⊆r) (hr : Good f r) (pin : f w.1=none → w.2=true) :
    ∀ z∈c, f z.1=none → z.2=true := by
  intro z mem off
  by_cases eq : z=w
  · subst z; exact pin off
  · exact hr.1 z (inc (mem_erase.mpr ⟨eq,mem⟩)) off
theorem boundedClean {f : A→Option (B×Bool)} {c r : Clause A}
    (ok : ∀ z∈c, f z.1=none → z.2=true) (hr : Good f r) (inc : body f c⊆body f r) :
    Good f c := ⟨ok,fun z hz opp=> hr.2 z (inc hz) (inc opp)⟩
theorem extraClean {f : A→Option (B×Bool)} {c r : Clause A} {v : B×Bool}
    (ok : ∀ z∈c, f z.1=none → z.2=true) (hr : Good f r)
    (inc : ∀ z∈body f c, z∈body f r ∨ z=v) (opp : flip v∉body f r) : Good f c := by
  refine ⟨ok,?_⟩
  intro z hz hy
  rcases inc z hz with h|e
  · rcases inc (flip z) hy with hh|eq
    · exact hr.2 _ h hh
    · have zz : flip v=z := by rw [←eq,twice]
      exact opp (zz.symm ▸ h)
  · subst z
    rcases inc (flip v) hy with hh|eq
    · exact opp hh
    · rcases v with ⟨i,b⟩; cases b <;> simp [flip] at eq

theorem localstep {f : A→Option (B×Bool)} {p n : Clause A} {w : A}
    (hr : Good f (Join p n w)) :
    (Good f p ∧ body f p⊆body f (Join p n w)) ∨
    (Good f n ∧ body f n⊆body f (Join p n w)) ∨
    (∃v : B×Bool, f w=some v ∧ Good f p ∧ Good f n ∧
      (∀z∈body f p, z∈body f (Join p n w) ∨ z=v) ∧
      (∀z∈body f n, z∈body f (Join p n w) ∨ z=flip v)) := by
  have lp : p.erase (w,true)⊆Join p n w := fun _ h=>mem_union_left _ h
  have ln : n.erase (w,false)⊆Join p n w := fun _ h=>mem_union_right _ h
  cases hw : f w with
  | none =>
    have inc : body f p⊆body f (Join p n w) := by
      intro z hz
      rcases peeled lp z hz with h|h
      · exact h
      · simp [translate,hw] at h
    exact Or.inl ⟨boundedClean (fixedClean lp hr (fun _=>rfl)) hr inc,inc⟩
  | some v =>
    have op := fixedClean lp hr (fun _=>rfl)
    have on := fixedClean ln hr (by intro off; change f w=none at off; rw [hw] at off; contradiction)
    have bp : ∀z∈body f p, z∈body f (Join p n w) ∨ z=v := by
      intro z hz
      rcases peeled lp z hz with a|b
      · exact Or.inl a
      · right; rcases v with ⟨i,bv⟩; simpa [translate,hw] using b
    have bn : ∀z∈body f n, z∈body f (Join p n w) ∨ z=flip v := by
      intro z hz
      rcases peeled ln z hz with a|b
      · exact Or.inl a
      · right; rcases v with ⟨i,bv⟩; simpa [translate,hw,flip] using b
    by_cases a : v∈body f (Join p n w)
    · have inc : body f p⊆body f (Join p n w) := by
        intro z hz; rcases bp z hz with ok|rfl; exact ok; exact a
      exact Or.inl ⟨boundedClean op hr inc,inc⟩
    by_cases b : flip v∈body f (Join p n w)
    · have inc : body f n⊆body f (Join p n w) := by
        intro z hz; rcases bn z hz with ok|rfl; exact ok; exact b
      exact Or.inr (Or.inl ⟨boundedClean on hr inc,inc⟩)
    exact Or.inr (Or.inr ⟨v,rfl,extraClean op hr bp b,extraClean on hr bn (by simpa [twice] using a),bp,bn⟩)
end PEqualNP.Outside.L_pcx_166.Switch
namespace PEqualNP.Outside.L_pcx_166.Switch
open PEqualNP.ProofComplexity Finset
variable {A B : Type} [DecidableEq A] [DecidableEq B]
abbrev Mark (T : Type) := T × Clause T
inductive History (F : Set (Clause A)) : List (Clause A) → List (Mark A) → Prop
  | nil : History F [] []
  | ax {t tags c} : History F t tags → c∈F → History F (c::t) tags
  | res {t tags p n w} : History F t tags → p∈t → n∈t → (w,true)∈p → (w,false)∈n →
    History F (Join p n w::t) ((w,Join p n w)::tags)

theorem mark {F : Set (Clause A)} {t : List (Clause A)} (h : IsDerivation F t) :
    ∃tags, History F t tags := by
  induction h with
  | nil => exact ⟨_,History.nil⟩
  | ax prev ax ih => obtain ⟨tags,h⟩:=ih; exact ⟨_,History.ax h ax⟩
  | res prev mp mn step ih =>
    obtain ⟨tags,h⟩:=ih
    obtain ⟨w,pp,nn,rfl⟩:=step
    exact ⟨_,History.res h mp mn pp nn⟩

noncomputable def fee (f : A→Option (B×Bool)) (m : Mark A) : Nat := by
  classical
  exact if (f m.1).isSome=true ∧ Good f m.2 then 1 else 0

def Covers (f : A→Option (B×Bool)) (s : List (Clause B)) (c : Clause A) :=
  Good f c → ∃d∈s, d⊆body f c
theorem push {s : List (Clause B)} {F : Set (Clause B)} (hs : IsDerivation F s)
    {a b : Clause B} (ma : a∈s) (mb : b∈s) {y : B×Bool} (pa : y∈a) (nb : flip y∈b) :
    IsDerivation F ((a.erase y ∪ b.erase (flip y))::s) := by
  rcases y with ⟨w,k⟩
  cases k with
  | false =>
    apply IsDerivation.res hs mb ma
    exact ⟨w,nb,pa,Finset.union_comm _ _⟩
  | true =>
    apply IsDerivation.res hs ma mb
    exact ⟨w,pa,nb,rfl⟩

theorem compiler {F : Set (Clause A)} {G : Set (Clause B)} (f : A→Option (B×Bool))
    (seeds : List (Clause B)) (start : IsDerivation G seeds)
    (imageAx : ∀c∈F, Covers f seeds c) {t marks} (hist : History F t marks) :
    ∃s, IsDerivation G s ∧ s.length≤seeds.length+(marks.map (fee f)).sum ∧
      (∀ c∈seeds, c∈s) ∧ (∀c∈t, Covers f s c) := by
  classical
  induction hist with
  | nil => exact ⟨seeds,start,by simp,fun _ h=>h,by simp⟩
  | @ax t marks c hist ax ih =>
    obtain ⟨s,hs,size,inc,rep⟩:=ih
    refine ⟨s,hs,size,inc,?_⟩
    intro d mem hd
    rcases List.mem_cons.mp mem with rfl|old
    · obtain ⟨r,m,le⟩:=imageAx _ ax hd
      exact ⟨r,inc _ m,le⟩
    · exact rep _ old hd
  | @res t marks p n w hist mp mn pp nn ih =>
    obtain ⟨s,hs,size,inc,rep⟩:=ih
    let R := Join p n w
    have oldSize : s.length≤seeds.length+(((w,R)::marks).map (fee f)).sum := by
      simp only [List.map_cons,List.sum_cons]; omega
    have keep (head : Covers f s R) :
        ∃s', IsDerivation G s' ∧ s'.length≤seeds.length+(((w,R)::marks).map (fee f)).sum ∧
          (∀c∈seeds,c∈s') ∧ ∀c∈R::t,Covers f s' c :=
      ⟨s,hs,oldSize,inc,fun c m=>by rcases List.mem_cons.mp m with rfl|old; exact head; exact rep c old⟩
    by_cases ok : Good f R
    · rcases localstep ok with ⟨gp,sub⟩|⟨gn,sub⟩|⟨v,eq,gp,gn,ip,in'⟩
      · obtain ⟨d,m,dd⟩:=rep _ mp gp
        exact keep (fun _=>⟨d,m,fun _ h=>sub (dd h)⟩)
      · obtain ⟨d,m,dd⟩:=rep _ mn gn
        exact keep (fun _=>⟨d,m,fun _ h=>sub (dd h)⟩)
      · obtain ⟨a,ma,aa⟩:=rep _ mp gp
        obtain ⟨b,mb,bb⟩:=rep _ mn gn
        by_cases ap : a⊆body f R
        · exact keep (fun _=>⟨a,ma,ap⟩)
        by_cases bp : b⊆body f R
        · exact keep (fun _=>⟨b,mb,bp⟩)
        have pa : v∈a := by
          by_contra nn
          exact ap (fun z hz=>by rcases ip z (aa hz) with h|h; exact h; exact (nn (h ▸ hz)).elim)
        have nb : flip v∈b := by
          by_contra nn
          exact bp (fun z hz=>by rcases in' z (bb hz) with h|h; exact h; exact (nn (h ▸ hz)).elim)
        let d := a.erase v ∪ b.erase (flip v)
        have sub : d⊆body f R := by
          intro z hz
          rcases mem_union.mp hz with h|h
          · obtain ⟨ne,mem⟩:=mem_erase.mp h
            exact (ip z (aa mem)).resolve_right ne
          · obtain ⟨ne,mem⟩:=mem_erase.mp h
            exact (in' z (bb mem)).resolve_right ne
        have paidOne : fee f (w,R)=1 := by simp [fee,eq,ok]
        refine ⟨d::s,push hs ma mb pa nb,?_,fun c m=>List.mem_cons_of_mem _ (inc c m),?_⟩
        · simp only [List.length_cons,List.map_cons,List.sum_cons,paidOne]; omega
        · intro c mem hc
          rcases List.mem_cons.mp mem with rfl|old
          · exact ⟨d,List.mem_cons_self,sub⟩
          · obtain ⟨e,ee,le⟩:=rep _ old hc
            exact ⟨e,List.mem_cons_of_mem _ ee,le⟩
    · exact keep (fun h=>(ok h).elim)
end PEqualNP.Outside.L_pcx_166.Switch

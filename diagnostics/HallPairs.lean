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


namespace Reject
open Finset
def bits (n : Nat) : Box := fun h p => n.testBit (6*h.val+p.val)=true
def raws : List Nat := [17043521,34087042,68174084,136348168,272696336,545392672]
def G : Set Box := {b | ∃ a∈raws,b=bits a}

def goodDomain (d b : Nat) : Prop := stable (bits d) (bits b)
instance (d b : Nat) : Decidable (goodDomain d b) := by unfold goodDomain stable openCell bits;infer_instance
def rejects (free : List Nat) (g : Nat × Nat) := live (bits g.2) ∧
    (∀h : H,∀p : P,bits g.2 h p → ¬bits g.1 h p) ∧
    (free++raws).all (fun a => decide (goodDomain g.2 a)) = true
instance (free : List Nat) (g : Nat × Nat) : Decidable (rejects free g) := by
  unfold rejects live bits
  infer_instance

structure Cut where
  omit : List Nat
  blocked : List (Nat × Nat)
  deriving DecidableEq
def nested : List Nat := [798915,50344131,51118275,51130371,51130560,29127,1835463,1863687,1864128,117440967,117469191,117469632,119275527,119275968,119304192,975,61455,62400,3932175,3933120,3993600,251658255,251659200,251719680,255590400,31,1984,126976,8126464,520093696]
def free (e : Cut) : List Nat := nested.filter (fun x=> decide (x∉e.omit ∧ x∉e.blocked.map Prod.fst))
def ok (e : Cut) : Bool := decide (0∈e.blocked.map Prod.fst) &&
  e.blocked.all (fun g => decide (rejects (free e) g))
theorem kept {e : Cut} (valid : ok e=true) {xs : List Nat} (r : Run G (xs.map bits))
    (domain : ∀ a∈xs,a=0 ∨ a∈nested) (skip : ∀ a∈xs,a∉e.omit) : ∀ a∈xs,a∈free e := by
  classical
  simp only [ok,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at valid
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases r with
    | add before step =>
      have prev := ih before (fun b hb=>domain b (List.mem_cons_of_mem _ hb)) (fun b hb=>skip b (List.mem_cons_of_mem _ hb))
      have fresh : a∉e.blocked.map Prod.fst := by
        intro bad
        obtain ⟨g,hg,ag⟩ := List.mem_map.mp bad
        have tst : rejects (free e) g := valid.2 g hg
        have st : ∀ b∈G ∪ {b | b∈xs.map bits},stable (bits g.2) b := by
          intro b hb
          obtain ⟨n,hn,rfl⟩ : ∃ n∈free e++raws,b=bits n := by
            rcases hb with ⟨n,nh,rfl⟩|hb
            · exact ⟨n,List.mem_append.mpr (Or.inr nh),rfl⟩
            · obtain ⟨n,nh,rfl⟩ := List.mem_map.mp hb
              exact ⟨n,List.mem_append.mpr (Or.inl (prev _ nh)),rfl⟩
          exact of_decide_eq_true ((List.all_eq_true.mp tst.2.2) n hn)
        obtain ⟨h,p,pd,pa⟩ := step (bits g.2) tst.1 st
        exact tst.2.1 h p pd (ag.symm ▸ pa)
      have nz : a≠0 := fun eq=>fresh (eq.symm ▸ valid.1)
      have an := (domain a (by simp)).resolve_left nz
      have inFree : a∈free e := List.mem_filter.mpr ⟨an,decide_eq_true ((And.intro (skip a (by simp)) fresh))⟩
      intro b hb
      exact (List.mem_cons.mp hb).elim (fun eq => eq.symm ▸ inFree) (prev b)

theorem mandatory {e : Cut} (valid : ok e=true) {xs : List Nat} (r : Run G (xs.map bits))
    (domain : ∀ a∈xs,a=0 ∨ a∈nested) (ending : 0∈xs) : ∃ a∈xs,a∈e.omit := by
  classical
  by_contra! skip
  have bad := kept valid r domain skip 0 ending
  have both : 0∉e.omit ∧ 0∉e.blocked.map Prod.fst := of_decide_eq_true (List.mem_filter.mp bad).2
  simp only [ok,Bool.and_eq_true,decide_eq_true_eq] at valid
  exact both.2 valid.1
def c0 : Cut := ⟨[798915, 50344131],[(29127,119508536), (975,119311408), (61455,119472688), (62400,119475208), (31,255852512), (1984,255850559), (126976,255725567), (0,528482303)]⟩
def c1 : Cut := ⟨[798915, 51118275],[(1835463,132152888), (975,119569456), (3932175,130052656), (3933120,130055176), (31,268238816), (1984,268236863), (8126464,260112383), (0,536739839)]⟩
def c2 : Cut := ⟨[798915, 51130371],[(1863687,132350456), (61455,119734768), (3932175,130056688), (3993600,130220488), (31,268432352), (126976,268305407), (8126464,260305919), (0,536868863)]⟩
def c3 : Cut := ⟨[798915, 51130560],[(1864128,132353543), (62400,119737351), (3933120,130059271), (3993600,130220551), (1984,268433423), (126976,268308431), (8126464,260308943), (0,536870879)]⟩
def c4 : Cut := ⟨[50344131, 51118275],[(117440967,941391416), (975,136084528), (251658255,807170608), (251659200,807173128), (31,1060962272), (1984,1060960319), (520093696,540868607), (0,1065222143)]⟩
def c5 : Cut := ⟨[50344131, 51130371],[(117469191,941588984), (61455,136249840), (251658255,807174640), (251719680,807338440), (31,1061155808), (126976,1061028863), (520093696,541062143), (0,1065351167)]⟩
def c6 : Cut := ⟨[50344131, 51130560],[(117469632,941592071), (62400,136252423), (251659200,807177223), (251719680,807338503), (1984,1061156879), (126976,1061031887), (520093696,541065167), (0,1065353183)]⟩
def c7 : Cut := ⟨[51118275, 51130371],[(119275527,954233336), (3932175,146829808), (251658255,807432688), (255590400,817918408), (31,1073542112), (8126464,1065415679), (520093696,553448447), (0,1073608703)]⟩
def c8 : Cut := ⟨[51118275, 51130560],[(119275968,954236423), (3933120,146832391), (251659200,807435271), (255590400,817918471), (1984,1073543183), (8126464,1065418703), (520093696,553451471), (0,1073610719)]⟩
def c9 : Cut := ⟨[51130371, 51130560],[(119304192,954433991), (3993600,146997703), (251719680,807600583), (255590400,817922503), (126976,1073611727), (8126464,1065612239), (520093696,553645007), (0,1073739743)]⟩
def c10 : Cut := ⟨[29127, 1835463],[(975,121437232), (31,121435168), (1984,121436176), (0,528351231)]⟩
def c11 : Cut := ⟨[29127, 1863687],[(61455,121570288), (31,121439200), (126976,121504720), (0,528480255)]⟩
def c12 : Cut := ⟨[29127, 1864128],[(62400,121572367), (1984,121440271), (126976,121504783), (0,528482271)]⟩
def c13 : Cut := ⟨[29127, 117440967],[(975,253557808), (31,253555744), (1984,253556752), (0,528351231)]⟩
def c14 : Cut := ⟨[29127, 117469191],[(61455,253690864), (31,253559776), (126976,253625296), (0,528480255)]⟩
def c15 : Cut := ⟨[29127, 117469632],[(62400,253692943), (1984,253560847), (126976,253625359), (0,528482271)]⟩
def c16 : Cut := ⟨[1835463, 1863687],[(3932175,130085872), (31,121697248), (8126464,125891536), (0,536737791)]⟩
def c17 : Cut := ⟨[1835463, 1864128],[(3933120,130087951), (1984,121698319), (8126464,125891599), (0,536739807)]⟩
def c18 : Cut := ⟨[1835463, 117440967],[(975,255622192), (31,255620128), (1984,255621136), (0,528351231)]⟩
def c19 : Cut := ⟨[1835463, 119275527],[(3932175,264270832), (31,255882208), (8126464,260076496), (0,536737791)]⟩
def c20 : Cut := ⟨[1835463, 119275968],[(3933120,264272911), (1984,255883279), (8126464,260076559), (0,536739807)]⟩
def c21 : Cut := ⟨[1863687, 1864128],[(3993600,130221007), (126976,121766863), (8126464,125895631), (0,536868831)]⟩
def c22 : Cut := ⟨[1863687, 117469191],[(61455,255787504), (31,255656416), (126976,255721936), (0,528480255)]⟩
def c23 : Cut := ⟨[1863687, 119275527],[(3932175,264303088), (31,255914464), (8126464,260108752), (0,536737791)]⟩
def c24 : Cut := ⟨[1863687, 119304192],[(3993600,264438223), (126976,255984079), (8126464,260112847), (0,536868831)]⟩
def c25 : Cut := ⟨[1864128, 117469632],[(62400,255790087), (1984,255657991), (126976,255722503), (0,528482271)]⟩
def c26 : Cut := ⟨[1864128, 119275968],[(3933120,264305671), (1984,255916039), (8126464,260109319), (0,536739807)]⟩
def c27 : Cut := ⟨[1864128, 119304192],[(3993600,264438727), (126976,255984583), (8126464,260113351), (0,536868831)]⟩
def c28 : Cut := ⟨[117440967, 117469191],[(251658255,807203824), (31,270332896), (520093696,538768336), (0,1065220095)]⟩
def c29 : Cut := ⟨[117440967, 117469632],[(251659200,807205903), (1984,270333967), (520093696,538768399), (0,1065222111)]⟩
def c30 : Cut := ⟨[117440967, 119275527],[(251658255,809268208), (31,272397280), (520093696,540832720), (0,1065220095)]⟩
def c31 : Cut := ⟨[117440967, 119275968],[(251659200,809270287), (1984,272398351), (520093696,540832783), (0,1065222111)]⟩
def c32 : Cut := ⟨[117469191, 117469632],[(251719680,807338959), (126976,270402511), (520093696,538772431), (0,1065351135)]⟩
def c33 : Cut := ⟨[117469191, 119275527],[(251658255,809300464), (31,272429536), (520093696,540864976), (0,1065220095)]⟩
def c34 : Cut := ⟨[117469191, 119304192],[(251719680,809435599), (126976,272499151), (520093696,540869071), (0,1065351135)]⟩
def c35 : Cut := ⟨[117469632, 119275968],[(251659200,809303047), (1984,272431111), (520093696,540865543), (0,1065222111)]⟩
def c36 : Cut := ⟨[117469632, 119304192],[(251719680,809436103), (126976,272499655), (520093696,540869575), (0,1065351135)]⟩
def c37 : Cut := ⟨[119275527, 119275968],[(255590400,817918927), (8126464,276853711), (520093696,541094863), (0,1073608671)]⟩
def c38 : Cut := ⟨[119275527, 119304192],[(255590400,817951183), (8126464,276885967), (520093696,541127119), (0,1073608671)]⟩
def c39 : Cut := ⟨[119275968, 119304192],[(255590400,817951687), (8126464,276886471), (520093696,541127623), (0,1073608671)]⟩
def c40 : Cut := ⟨[975, 61455],[(31,255719392), (0,255719392)]⟩
def c41 : Cut := ⟨[975, 62400],[(1984,255719455), (0,255719455)]⟩
def c42 : Cut := ⟨[975, 3932175],[(31,259848160), (0,259848160)]⟩
def c43 : Cut := ⟨[975, 3933120],[(1984,259848223), (0,259848223)]⟩
def c44 : Cut := ⟨[975, 251658255],[(31,524089312), (0,524089312)]⟩
def c45 : Cut := ⟨[975, 251659200],[(1984,524089375), (0,524089375)]⟩
def c46 : Cut := ⟨[61455, 62400],[(126976,255723487), (0,255723487)]⟩
def c47 : Cut := ⟨[61455, 3932175],[(31,259912672), (0,259912672)]⟩
def c48 : Cut := ⟨[61455, 3993600],[(126976,259916767), (0,259916767)]⟩
def c49 : Cut := ⟨[61455, 251658255],[(31,524153824), (0,524153824)]⟩
def c50 : Cut := ⟨[61455, 251719680],[(126976,524157919), (0,524157919)]⟩
def c51 : Cut := ⟨[62400, 3933120],[(1984,259913743), (0,259913743)]⟩
def c52 : Cut := ⟨[62400, 3993600],[(126976,259917775), (0,259917775)]⟩
def c53 : Cut := ⟨[62400, 251659200],[(1984,524154895), (0,524154895)]⟩
def c54 : Cut := ⟨[62400, 251719680],[(126976,524158927), (0,524158927)]⟩
def c55 : Cut := ⟨[3932175, 3933120],[(8126464,260110303), (0,260110303)]⟩
def c56 : Cut := ⟨[3932175, 3993600],[(8126464,260174815), (0,260174815)]⟩
def c57 : Cut := ⟨[3932175, 251658255],[(31,528282592), (0,528282592)]⟩
def c58 : Cut := ⟨[3932175, 255590400],[(8126464,528544735), (0,528544735)]⟩
def c59 : Cut := ⟨[3933120, 3993600],[(8126464,260175823), (0,260175823)]⟩
def c60 : Cut := ⟨[3933120, 251659200],[(1984,528283663), (0,528283663)]⟩
def c61 : Cut := ⟨[3933120, 255590400],[(8126464,528545743), (0,528545743)]⟩
def c62 : Cut := ⟨[3993600, 251719680],[(126976,528352207), (0,528352207)]⟩
def c63 : Cut := ⟨[3993600, 255590400],[(8126464,528610255), (0,528610255)]⟩
def c64 : Cut := ⟨[251658255, 251659200],[(520093696,540866527), (0,540866527)]⟩
def c65 : Cut := ⟨[251658255, 251719680],[(520093696,540931039), (0,540931039)]⟩
def c66 : Cut := ⟨[251658255, 255590400],[(520093696,545059807), (0,545059807)]⟩
def c67 : Cut := ⟨[251659200, 251719680],[(520093696,540932047), (0,540932047)]⟩
def c68 : Cut := ⟨[251659200, 255590400],[(520093696,545060815), (0,545060815)]⟩
def c69 : Cut := ⟨[251719680, 255590400],[(520093696,545125327), (0,545125327)]⟩
def c70 : Cut := ⟨[31, 1984],[(0,528351231)]⟩
def c71 : Cut := ⟨[31, 126976],[(0,528480255)]⟩
def c72 : Cut := ⟨[31, 8126464],[(0,536737791)]⟩
def c73 : Cut := ⟨[31, 520093696],[(0,1065220095)]⟩
def c74 : Cut := ⟨[1984, 126976],[(0,528482271)]⟩
def c75 : Cut := ⟨[1984, 8126464],[(0,536739807)]⟩
def c76 : Cut := ⟨[1984, 520093696],[(0,1065222111)]⟩
def c77 : Cut := ⟨[126976, 8126464],[(0,536868831)]⟩
def c78 : Cut := ⟨[126976, 520093696],[(0,1065351135)]⟩
def c79 : Cut := ⟨[8126464, 520093696],[(0,1073608671)]⟩
def cuts : List Cut := [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79]

set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked : cuts.all ok=true := by decide +kernel
theorem everySwapPair {xs : List Nat} (run : Run G (xs.map bits)) (domain : ∀ a∈xs,a=0 ∨ a∈nested)
    (ending : 0∈xs) (e : Cut) (he : e∈cuts) : ∃ a∈xs,a∈e.omit :=
  mandatory ((List.all_eq_true.mp checked) e he) run domain ending

end Reject
end PEqualNP.Outside.L_meta_9471.Boxes

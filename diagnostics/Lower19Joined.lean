import PEqualNP.Outside.L_meta_9169

namespace Mux9939Lower
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9169
def forbidden (v : Nat) := (0x20002aa024402442240224055ea00ea570057aa024402442240224055400040 : Nat).testBit (v%256)


theorem join {S : List Nat} (k : Nat)
    (base : (0 :: S).any forbidden=false)
    (branches : ∀ t∈next 255 S, reach 255 forbidden k (S++[t])=false) :
    reach 255 forbidden (k+1) S=false := by
  rw [reach_succ,base,Bool.false_or]
  cases h : (next 255 S).any (fun t => reach 255 forbidden k (S++[t])) with
  | false => rfl
  | true =>
    obtain ⟨t,mem,ht⟩ := List.any_eq_true.mp h
    exact False.elim (Bool.false_ne_true ((branches t mem).symm.trans ht))

private theorem bank_0_15 : reach 255 forbidden 2 [170,204,240,0,15]=false := by decide +kernel
private theorem bank_0_51 : reach 255 forbidden 2 [170,204,240,0,51]=false := by decide +kernel
private theorem bank_0_85 : reach 255 forbidden 2 [170,204,240,0,85]=false := by decide +kernel
private theorem bank_0_136 : reach 255 forbidden 2 [170,204,240,0,136]=false := by decide +kernel
private theorem bank_0_160 : reach 255 forbidden 2 [170,204,240,0,160]=false := by decide +kernel
private theorem bank_0_192 : reach 255 forbidden 2 [170,204,240,0,192]=false := by decide +kernel
private theorem bank_0_238 : reach 255 forbidden 2 [170,204,240,0,238]=false := by decide +kernel
private theorem bank_0_250 : reach 255 forbidden 2 [170,204,240,0,250]=false := by decide +kernel
private theorem bank_0_252 : reach 255 forbidden 2 [170,204,240,0,252]=false := by decide +kernel
private theorem bank_0_255 : reach 255 forbidden 2 [170,204,240,0,255]=false := by decide +kernel

theorem bank_0 : reach 255 forbidden 3 [170,204,240,0]=false := by
  apply join 2 (by decide)
  intro t ht
  have enum : (next 255 [170,204,240,0]).all (fun a => decide (a∈([15,51,85,136,160,192,238,250,252,255] : List Nat)))=true := by decide +kernel
  have ways := of_decide_eq_true ((List.all_eq_true.mp enum) t ht)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ways
  rcases ways with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_0_15
  · exact bank_0_51
  · exact bank_0_85
  · exact bank_0_136
  · exact bank_0_160
  · exact bank_0_192
  · exact bank_0_238
  · exact bank_0_250
  · exact bank_0_252
  · exact bank_0_255
private theorem bank_15_0 : reach 255 forbidden 2 [170,204,240,15,0]=false := by decide +kernel
private theorem bank_15_10 : reach 255 forbidden 2 [170,204,240,15,10]=false := by decide +kernel
private theorem bank_15_12 : reach 255 forbidden 2 [170,204,240,15,12]=false := by decide +kernel
private theorem bank_15_51 : reach 255 forbidden 2 [170,204,240,15,51]=false := by decide +kernel
private theorem bank_15_85 : reach 255 forbidden 2 [170,204,240,15,85]=false := by decide +kernel
private theorem bank_15_136 : reach 255 forbidden 2 [170,204,240,15,136]=false := by decide +kernel
private theorem bank_15_160 : reach 255 forbidden 2 [170,204,240,15,160]=false := by decide +kernel
private theorem bank_15_175 : reach 255 forbidden 2 [170,204,240,15,175]=false := by decide +kernel
private theorem bank_15_192 : reach 255 forbidden 2 [170,204,240,15,192]=false := by decide +kernel
private theorem bank_15_207 : reach 255 forbidden 2 [170,204,240,15,207]=false := by decide +kernel
private theorem bank_15_238 : reach 255 forbidden 2 [170,204,240,15,238]=false := by decide +kernel
private theorem bank_15_250 : reach 255 forbidden 2 [170,204,240,15,250]=false := by decide +kernel
private theorem bank_15_252 : reach 255 forbidden 2 [170,204,240,15,252]=false := by decide +kernel
private theorem bank_15_255 : reach 255 forbidden 2 [170,204,240,15,255]=false := by decide +kernel

theorem bank_15 : reach 255 forbidden 3 [170,204,240,15]=false := by
  apply join 2 (by decide)
  intro t ht
  have enum : (next 255 [170,204,240,15]).all (fun a => decide (a∈([0,10,12,51,85,136,160,175,192,207,238,250,252,255] : List Nat)))=true := by decide +kernel
  have ways := of_decide_eq_true ((List.all_eq_true.mp enum) t ht)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ways
  rcases ways with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_15_0
  · exact bank_15_10
  · exact bank_15_12
  · exact bank_15_51
  · exact bank_15_85
  · exact bank_15_136
  · exact bank_15_160
  · exact bank_15_175
  · exact bank_15_192
  · exact bank_15_207
  · exact bank_15_238
  · exact bank_15_250
  · exact bank_15_252
  · exact bank_15_255
private theorem bank_51_0 : reach 255 forbidden 2 [170,204,240,51,0]=false := by decide +kernel
private theorem bank_51_15 : reach 255 forbidden 2 [170,204,240,51,15]=false := by decide +kernel
private theorem bank_51_34 : reach 255 forbidden 2 [170,204,240,51,34]=false := by decide +kernel
private theorem bank_51_48 : reach 255 forbidden 2 [170,204,240,51,48]=false := by decide +kernel
private theorem bank_51_85 : reach 255 forbidden 2 [170,204,240,51,85]=false := by decide +kernel
private theorem bank_51_136 : reach 255 forbidden 2 [170,204,240,51,136]=false := by decide +kernel
private theorem bank_51_160 : reach 255 forbidden 2 [170,204,240,51,160]=false := by decide +kernel
private theorem bank_51_187 : reach 255 forbidden 2 [170,204,240,51,187]=false := by decide +kernel
private theorem bank_51_192 : reach 255 forbidden 2 [170,204,240,51,192]=false := by decide +kernel
private theorem bank_51_238 : reach 255 forbidden 2 [170,204,240,51,238]=false := by decide +kernel
private theorem bank_51_243 : reach 255 forbidden 2 [170,204,240,51,243]=false := by decide +kernel
private theorem bank_51_250 : reach 255 forbidden 2 [170,204,240,51,250]=false := by decide +kernel
private theorem bank_51_252 : reach 255 forbidden 2 [170,204,240,51,252]=false := by decide +kernel
private theorem bank_51_255 : reach 255 forbidden 2 [170,204,240,51,255]=false := by decide +kernel

theorem bank_51 : reach 255 forbidden 3 [170,204,240,51]=false := by
  apply join 2 (by decide)
  intro t ht
  have enum : (next 255 [170,204,240,51]).all (fun a => decide (a∈([0,15,34,48,85,136,160,187,192,238,243,250,252,255] : List Nat)))=true := by decide +kernel
  have ways := of_decide_eq_true ((List.all_eq_true.mp enum) t ht)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ways
  rcases ways with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_51_0
  · exact bank_51_15
  · exact bank_51_34
  · exact bank_51_48
  · exact bank_51_85
  · exact bank_51_136
  · exact bank_51_160
  · exact bank_51_187
  · exact bank_51_192
  · exact bank_51_238
  · exact bank_51_243
  · exact bank_51_250
  · exact bank_51_252
  · exact bank_51_255
private theorem bank_85_0 : reach 255 forbidden 2 [170,204,240,85,0]=false := by decide +kernel
private theorem bank_85_15 : reach 255 forbidden 2 [170,204,240,85,15]=false := by decide +kernel
private theorem bank_85_51 : reach 255 forbidden 2 [170,204,240,85,51]=false := by decide +kernel
private theorem bank_85_68 : reach 255 forbidden 2 [170,204,240,85,68]=false := by decide +kernel
private theorem bank_85_80 : reach 255 forbidden 2 [170,204,240,85,80]=false := by decide +kernel
private theorem bank_85_136 : reach 255 forbidden 2 [170,204,240,85,136]=false := by decide +kernel
private theorem bank_85_160 : reach 255 forbidden 2 [170,204,240,85,160]=false := by decide +kernel
private theorem bank_85_192 : reach 255 forbidden 2 [170,204,240,85,192]=false := by decide +kernel
private theorem bank_85_221 : reach 255 forbidden 2 [170,204,240,85,221]=false := by decide +kernel
private theorem bank_85_238 : reach 255 forbidden 2 [170,204,240,85,238]=false := by decide +kernel
private theorem bank_85_245 : reach 255 forbidden 2 [170,204,240,85,245]=false := by decide +kernel
private theorem bank_85_250 : reach 255 forbidden 2 [170,204,240,85,250]=false := by decide +kernel
private theorem bank_85_252 : reach 255 forbidden 2 [170,204,240,85,252]=false := by decide +kernel
private theorem bank_85_255 : reach 255 forbidden 2 [170,204,240,85,255]=false := by decide +kernel

theorem bank_85 : reach 255 forbidden 3 [170,204,240,85]=false := by
  apply join 2 (by decide)
  intro t ht
  have enum : (next 255 [170,204,240,85]).all (fun a => decide (a∈([0,15,51,68,80,136,160,192,221,238,245,250,252,255] : List Nat)))=true := by decide +kernel
  have ways := of_decide_eq_true ((List.all_eq_true.mp enum) t ht)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ways
  rcases ways with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_85_0
  · exact bank_85_15
  · exact bank_85_51
  · exact bank_85_68
  · exact bank_85_80
  · exact bank_85_136
  · exact bank_85_160
  · exact bank_85_192
  · exact bank_85_221
  · exact bank_85_238
  · exact bank_85_245
  · exact bank_85_250
  · exact bank_85_252
  · exact bank_85_255
private theorem bank_136_0 : reach 255 forbidden 2 [170,204,240,136,0]=false := by decide +kernel
private theorem bank_136_15 : reach 255 forbidden 2 [170,204,240,136,15]=false := by decide +kernel
private theorem bank_136_51 : reach 255 forbidden 2 [170,204,240,136,51]=false := by decide +kernel
private theorem bank_136_85 : reach 255 forbidden 2 [170,204,240,136,85]=false := by decide +kernel
private theorem bank_136_119 : reach 255 forbidden 2 [170,204,240,136,119]=false := by decide +kernel
private theorem bank_136_128 : reach 255 forbidden 2 [170,204,240,136,128]=false := by decide +kernel
private theorem bank_136_160 : reach 255 forbidden 2 [170,204,240,136,160]=false := by decide +kernel
private theorem bank_136_192 : reach 255 forbidden 2 [170,204,240,136,192]=false := by decide +kernel
private theorem bank_136_238 : reach 255 forbidden 2 [170,204,240,136,238]=false := by decide +kernel
private theorem bank_136_248 : reach 255 forbidden 2 [170,204,240,136,248]=false := by decide +kernel
private theorem bank_136_250 : reach 255 forbidden 2 [170,204,240,136,250]=false := by decide +kernel
private theorem bank_136_252 : reach 255 forbidden 2 [170,204,240,136,252]=false := by decide +kernel
private theorem bank_136_255 : reach 255 forbidden 2 [170,204,240,136,255]=false := by decide +kernel

theorem bank_136 : reach 255 forbidden 3 [170,204,240,136]=false := by
  apply join 2 (by decide)
  intro t ht
  have enum : (next 255 [170,204,240,136]).all (fun a => decide (a∈([0,15,51,85,119,128,160,192,238,248,250,252,255] : List Nat)))=true := by decide +kernel
  have ways := of_decide_eq_true ((List.all_eq_true.mp enum) t ht)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ways
  rcases ways with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_136_0
  · exact bank_136_15
  · exact bank_136_51
  · exact bank_136_85
  · exact bank_136_119
  · exact bank_136_128
  · exact bank_136_160
  · exact bank_136_192
  · exact bank_136_238
  · exact bank_136_248
  · exact bank_136_250
  · exact bank_136_252
  · exact bank_136_255
private theorem bank_160_0 : reach 255 forbidden 2 [170,204,240,160,0]=false := by decide +kernel
private theorem bank_160_15 : reach 255 forbidden 2 [170,204,240,160,15]=false := by decide +kernel
private theorem bank_160_51 : reach 255 forbidden 2 [170,204,240,160,51]=false := by decide +kernel
private theorem bank_160_85 : reach 255 forbidden 2 [170,204,240,160,85]=false := by decide +kernel
private theorem bank_160_95 : reach 255 forbidden 2 [170,204,240,160,95]=false := by decide +kernel
private theorem bank_160_128 : reach 255 forbidden 2 [170,204,240,160,128]=false := by decide +kernel
private theorem bank_160_136 : reach 255 forbidden 2 [170,204,240,160,136]=false := by decide +kernel
private theorem bank_160_192 : reach 255 forbidden 2 [170,204,240,160,192]=false := by decide +kernel
private theorem bank_160_236 : reach 255 forbidden 2 [170,204,240,160,236]=false := by decide +kernel
private theorem bank_160_238 : reach 255 forbidden 2 [170,204,240,160,238]=false := by decide +kernel
private theorem bank_160_250 : reach 255 forbidden 2 [170,204,240,160,250]=false := by decide +kernel
private theorem bank_160_252 : reach 255 forbidden 2 [170,204,240,160,252]=false := by decide +kernel
private theorem bank_160_255 : reach 255 forbidden 2 [170,204,240,160,255]=false := by decide +kernel

theorem bank_160 : reach 255 forbidden 3 [170,204,240,160]=false := by
  apply join 2 (by decide)
  intro t ht
  have enum : (next 255 [170,204,240,160]).all (fun a => decide (a∈([0,15,51,85,95,128,136,192,236,238,250,252,255] : List Nat)))=true := by decide +kernel
  have ways := of_decide_eq_true ((List.all_eq_true.mp enum) t ht)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ways
  rcases ways with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_160_0
  · exact bank_160_15
  · exact bank_160_51
  · exact bank_160_85
  · exact bank_160_95
  · exact bank_160_128
  · exact bank_160_136
  · exact bank_160_192
  · exact bank_160_236
  · exact bank_160_238
  · exact bank_160_250
  · exact bank_160_252
  · exact bank_160_255
private theorem bank_192_0 : reach 255 forbidden 2 [170,204,240,192,0]=false := by decide +kernel
private theorem bank_192_15 : reach 255 forbidden 2 [170,204,240,192,15]=false := by decide +kernel
private theorem bank_192_51 : reach 255 forbidden 2 [170,204,240,192,51]=false := by decide +kernel
private theorem bank_192_63 : reach 255 forbidden 2 [170,204,240,192,63]=false := by decide +kernel
private theorem bank_192_85 : reach 255 forbidden 2 [170,204,240,192,85]=false := by decide +kernel
private theorem bank_192_128 : reach 255 forbidden 2 [170,204,240,192,128]=false := by decide +kernel
private theorem bank_192_136 : reach 255 forbidden 2 [170,204,240,192,136]=false := by decide +kernel
private theorem bank_192_160 : reach 255 forbidden 2 [170,204,240,192,160]=false := by decide +kernel
private theorem bank_192_234 : reach 255 forbidden 2 [170,204,240,192,234]=false := by decide +kernel
private theorem bank_192_238 : reach 255 forbidden 2 [170,204,240,192,238]=false := by decide +kernel
private theorem bank_192_250 : reach 255 forbidden 2 [170,204,240,192,250]=false := by decide +kernel
private theorem bank_192_252 : reach 255 forbidden 2 [170,204,240,192,252]=false := by decide +kernel
private theorem bank_192_255 : reach 255 forbidden 2 [170,204,240,192,255]=false := by decide +kernel

theorem bank_192 : reach 255 forbidden 3 [170,204,240,192]=false := by
  apply join 2 (by decide)
  intro t ht
  have enum : (next 255 [170,204,240,192]).all (fun a => decide (a∈([0,15,51,63,85,128,136,160,234,238,250,252,255] : List Nat)))=true := by decide +kernel
  have ways := of_decide_eq_true ((List.all_eq_true.mp enum) t ht)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ways
  rcases ways with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_192_0
  · exact bank_192_15
  · exact bank_192_51
  · exact bank_192_63
  · exact bank_192_85
  · exact bank_192_128
  · exact bank_192_136
  · exact bank_192_160
  · exact bank_192_234
  · exact bank_192_238
  · exact bank_192_250
  · exact bank_192_252
  · exact bank_192_255
private theorem bank_238_0 : reach 255 forbidden 2 [170,204,240,238,0]=false := by decide +kernel
private theorem bank_238_15 : reach 255 forbidden 2 [170,204,240,238,15]=false := by decide +kernel
private theorem bank_238_17 : reach 255 forbidden 2 [170,204,240,238,17]=false := by decide +kernel
private theorem bank_238_51 : reach 255 forbidden 2 [170,204,240,238,51]=false := by decide +kernel
private theorem bank_238_85 : reach 255 forbidden 2 [170,204,240,238,85]=false := by decide +kernel
private theorem bank_238_136 : reach 255 forbidden 2 [170,204,240,238,136]=false := by decide +kernel
private theorem bank_238_160 : reach 255 forbidden 2 [170,204,240,238,160]=false := by decide +kernel
private theorem bank_238_192 : reach 255 forbidden 2 [170,204,240,238,192]=false := by decide +kernel
private theorem bank_238_224 : reach 255 forbidden 2 [170,204,240,238,224]=false := by decide +kernel
private theorem bank_238_250 : reach 255 forbidden 2 [170,204,240,238,250]=false := by decide +kernel
private theorem bank_238_252 : reach 255 forbidden 2 [170,204,240,238,252]=false := by decide +kernel
private theorem bank_238_254 : reach 255 forbidden 2 [170,204,240,238,254]=false := by decide +kernel
private theorem bank_238_255 : reach 255 forbidden 2 [170,204,240,238,255]=false := by decide +kernel

theorem bank_238 : reach 255 forbidden 3 [170,204,240,238]=false := by
  apply join 2 (by decide)
  intro t ht
  have enum : (next 255 [170,204,240,238]).all (fun a => decide (a∈([0,15,17,51,85,136,160,192,224,250,252,254,255] : List Nat)))=true := by decide +kernel
  have ways := of_decide_eq_true ((List.all_eq_true.mp enum) t ht)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ways
  rcases ways with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_238_0
  · exact bank_238_15
  · exact bank_238_17
  · exact bank_238_51
  · exact bank_238_85
  · exact bank_238_136
  · exact bank_238_160
  · exact bank_238_192
  · exact bank_238_224
  · exact bank_238_250
  · exact bank_238_252
  · exact bank_238_254
  · exact bank_238_255
private theorem bank_250_0 : reach 255 forbidden 2 [170,204,240,250,0]=false := by decide +kernel
private theorem bank_250_5 : reach 255 forbidden 2 [170,204,240,250,5]=false := by decide +kernel
private theorem bank_250_15 : reach 255 forbidden 2 [170,204,240,250,15]=false := by decide +kernel
private theorem bank_250_51 : reach 255 forbidden 2 [170,204,240,250,51]=false := by decide +kernel
private theorem bank_250_85 : reach 255 forbidden 2 [170,204,240,250,85]=false := by decide +kernel
private theorem bank_250_136 : reach 255 forbidden 2 [170,204,240,250,136]=false := by decide +kernel
private theorem bank_250_160 : reach 255 forbidden 2 [170,204,240,250,160]=false := by decide +kernel
private theorem bank_250_192 : reach 255 forbidden 2 [170,204,240,250,192]=false := by decide +kernel
private theorem bank_250_200 : reach 255 forbidden 2 [170,204,240,250,200]=false := by decide +kernel
private theorem bank_250_238 : reach 255 forbidden 2 [170,204,240,250,238]=false := by decide +kernel
private theorem bank_250_252 : reach 255 forbidden 2 [170,204,240,250,252]=false := by decide +kernel
private theorem bank_250_254 : reach 255 forbidden 2 [170,204,240,250,254]=false := by decide +kernel
private theorem bank_250_255 : reach 255 forbidden 2 [170,204,240,250,255]=false := by decide +kernel

theorem bank_250 : reach 255 forbidden 3 [170,204,240,250]=false := by
  apply join 2 (by decide)
  intro t ht
  have enum : (next 255 [170,204,240,250]).all (fun a => decide (a∈([0,5,15,51,85,136,160,192,200,238,252,254,255] : List Nat)))=true := by decide +kernel
  have ways := of_decide_eq_true ((List.all_eq_true.mp enum) t ht)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ways
  rcases ways with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_250_0
  · exact bank_250_5
  · exact bank_250_15
  · exact bank_250_51
  · exact bank_250_85
  · exact bank_250_136
  · exact bank_250_160
  · exact bank_250_192
  · exact bank_250_200
  · exact bank_250_238
  · exact bank_250_252
  · exact bank_250_254
  · exact bank_250_255
private theorem bank_252_0 : reach 255 forbidden 2 [170,204,240,252,0]=false := by decide +kernel
private theorem bank_252_3 : reach 255 forbidden 2 [170,204,240,252,3]=false := by decide +kernel
private theorem bank_252_15 : reach 255 forbidden 2 [170,204,240,252,15]=false := by decide +kernel
private theorem bank_252_51 : reach 255 forbidden 2 [170,204,240,252,51]=false := by decide +kernel
private theorem bank_252_85 : reach 255 forbidden 2 [170,204,240,252,85]=false := by decide +kernel
private theorem bank_252_136 : reach 255 forbidden 2 [170,204,240,252,136]=false := by decide +kernel
private theorem bank_252_160 : reach 255 forbidden 2 [170,204,240,252,160]=false := by decide +kernel
private theorem bank_252_168 : reach 255 forbidden 2 [170,204,240,252,168]=false := by decide +kernel
private theorem bank_252_192 : reach 255 forbidden 2 [170,204,240,252,192]=false := by decide +kernel
private theorem bank_252_238 : reach 255 forbidden 2 [170,204,240,252,238]=false := by decide +kernel
private theorem bank_252_250 : reach 255 forbidden 2 [170,204,240,252,250]=false := by decide +kernel
private theorem bank_252_254 : reach 255 forbidden 2 [170,204,240,252,254]=false := by decide +kernel
private theorem bank_252_255 : reach 255 forbidden 2 [170,204,240,252,255]=false := by decide +kernel

theorem bank_252 : reach 255 forbidden 3 [170,204,240,252]=false := by
  apply join 2 (by decide)
  intro t ht
  have enum : (next 255 [170,204,240,252]).all (fun a => decide (a∈([0,3,15,51,85,136,160,168,192,238,250,254,255] : List Nat)))=true := by decide +kernel
  have ways := of_decide_eq_true ((List.all_eq_true.mp enum) t ht)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ways
  rcases ways with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_252_0
  · exact bank_252_3
  · exact bank_252_15
  · exact bank_252_51
  · exact bank_252_85
  · exact bank_252_136
  · exact bank_252_160
  · exact bank_252_168
  · exact bank_252_192
  · exact bank_252_238
  · exact bank_252_250
  · exact bank_252_254
  · exact bank_252_255
private theorem bank_255_0 : reach 255 forbidden 2 [170,204,240,255,0]=false := by decide +kernel
private theorem bank_255_15 : reach 255 forbidden 2 [170,204,240,255,15]=false := by decide +kernel
private theorem bank_255_51 : reach 255 forbidden 2 [170,204,240,255,51]=false := by decide +kernel
private theorem bank_255_85 : reach 255 forbidden 2 [170,204,240,255,85]=false := by decide +kernel
private theorem bank_255_136 : reach 255 forbidden 2 [170,204,240,255,136]=false := by decide +kernel
private theorem bank_255_160 : reach 255 forbidden 2 [170,204,240,255,160]=false := by decide +kernel
private theorem bank_255_192 : reach 255 forbidden 2 [170,204,240,255,192]=false := by decide +kernel
private theorem bank_255_238 : reach 255 forbidden 2 [170,204,240,255,238]=false := by decide +kernel
private theorem bank_255_250 : reach 255 forbidden 2 [170,204,240,255,250]=false := by decide +kernel
private theorem bank_255_252 : reach 255 forbidden 2 [170,204,240,255,252]=false := by decide +kernel

theorem bank_255 : reach 255 forbidden 3 [170,204,240,255]=false := by
  apply join 2 (by decide)
  intro t ht
  have enum : (next 255 [170,204,240,255]).all (fun a => decide (a∈([0,15,51,85,136,160,192,238,250,252] : List Nat)))=true := by decide +kernel
  have ways := of_decide_eq_true ((List.all_eq_true.mp enum) t ht)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ways
  rcases ways with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_255_0
  · exact bank_255_15
  · exact bank_255_51
  · exact bank_255_85
  · exact bank_255_136
  · exact bank_255_160
  · exact bank_255_192
  · exact bank_255_238
  · exact bank_255_250
  · exact bank_255_252

theorem bank_root : reach 255 forbidden 4 [170,204,240]=false := by
  apply join 3 (by decide)
  intro t ht
  have enum : (next 255 [170,204,240]).all (fun a => decide (a∈([0,15,51,85,136,160,192,238,250,252,255] : List Nat)))=true := by decide +kernel
  have ways := of_decide_eq_true ((List.all_eq_true.mp enum) t ht)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ways
  rcases ways with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bank_0
  · exact bank_15
  · exact bank_51
  · exact bank_85
  · exact bank_136
  · exact bank_160
  · exact bank_192
  · exact bank_238
  · exact bank_250
  · exact bank_252
  · exact bank_255

end Mux9939Lower

namespace Mux9939Lower
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9169
def addr (x : Fin 11 → Bool) : Fin 8 := Fin.ofNat 8 ((x 0).toNat + 2*(x 1).toNat + 4*(x 2).toNat)
def slot (a : Fin 8) : Fin 11 := ⟨3+a.val,by omega⟩
def field (u y : Nat) (a : Fin 8) (v : Bool) : Bool := if u.testBit a.val then v else y.testBit a.val
def f (u y : Nat) (x : Fin 11 → Bool) : Bool := field u y (addr x) (x (slot (addr x)))
def mask (w : Nat) (i : Fin 11) : Bool := w.testBit i.val
def LB (u y k : Nat) := ∀ s, HasCircuitSize 11 (f u y) s → k ≤ s
def Update (u y : Nat) (i : Fin 8) (b : Bool) (U Y : Nat) :=
  ∀ a : Fin 8,∀ v : Bool,field u y a (if a=i then b else v) = field U Y a v
instance instUpdate (u y : Nat) (i : Fin 8) (b : Bool) (U Y : Nat) : Decidable (Update u y i b U Y) := by unfold Update;infer_instance

theorem notAddr : ∀ i : Fin 8, (0:Fin 11)≠slot i ∧ (1:Fin 11)≠slot i ∧ (2:Fin 11)≠slot i := by decide
theorem slot_inj : Function.Injective slot := by intro a b h; apply Fin.ext; have v := congrArg Fin.val h; change 3+a.val=3+b.val at v; omega

theorem update_eq {u y i b U Y} (h : Update u y i b U Y) :
    (fun x => f u y (Function.update x (slot i) b)) = f U Y := by
  funext x
  have a : addr (Function.update x (slot i) b) = addr x := by
    simp [addr,Function.update_of_ne (notAddr i).1,Function.update_of_ne (notAddr i).2.1,
      Function.update_of_ne (notAddr i).2.2]
  simp only [f,a]
  have v : Function.update x (slot i) b (slot (addr x)) = (if addr x=i then b else x (slot (addr x))) := by
    by_cases eq : addr x=i
    · simp [eq]
    · rw [Function.update_of_ne (fun e => eq (slot_inj e)),if_neg eq]
  rw [v]
  exact h _ _

def Uses (u y : Nat) (i : Fin 8) := ∃ x, f u y (Function.update x (slot i) (!x (slot i))) ≠ f u y x
def Varies (u y : Nat) := ∃ x z, f u y x ≠ f u y z

theorem one {u y k U Y} (i : Fin 8) (b : Bool) (dep : Uses u y i) (nc : Varies U Y)
    (st : Update u y i b U Y) (child : LB U Y k) : LB u y (k+1) := by
  intro s hs
  have upd := update_eq st
  obtain ⟨x,z,hz⟩ := nc
  obtain ⟨t,ht,v⟩ := q70 10 (f u y) (slot i) b s dep
    ⟨x,z,by simpa only [← upd] using hz⟩ hs
  rw [upd] at v
  have low := child t v
  omega

theorem two {u y k U Y V Z} (i : Fin 8) (dep : Uses u y i) (nc0 : Varies U Y) (nc1 : Varies V Z)
    (st0 : Update u y i false U Y) (st1 : Update u y i true V Z) (lo : LB U Y k) (hi : LB V Z k) :
    LB u y (k+2) := by
  intro s hs
  have e0 := update_eq st0
  have e1 := update_eq st1
  have varies (b : Bool) : ∃ x z, f u y (Function.update x (slot i) b) ≠ f u y (Function.update z (slot i) b) := by
    cases b
    · obtain ⟨x,z,h⟩ := nc0
      exact ⟨x,z,by simpa only [←e0] using h⟩
    · obtain ⟨x,z,h⟩ := nc1
      exact ⟨x,z,by simpa only [←e1] using h⟩
  obtain ⟨b,t,ht,v⟩ := q141 10 (f u y) (slot i) s dep varies hs
  cases b
  · rw [e0] at v
    have low := lo t v
    omega
  · rw [e1] at v
    have low := hi t v
    omega

theorem reach_goal {M : Nat} {g h : Nat → Bool} (inc : ∀ x,g x=true → h x=true) (k : Nat) (S : List Nat) :
    reach M g k S=true → reach M h k S=true := by
  induction k generalizing S with
  | zero =>
    simp only [reach,List.any_eq_true]
    exact fun ⟨v,m,vok⟩ => ⟨v,m,inc _ vok⟩
  | succ k ih =>
    simp only [reach,Bool.or_eq_true,List.any_eq_true]
    rintro (⟨v,m,vok⟩|⟨v,m,vok⟩)
    · exact Or.inl ⟨v,m,inc _ vok⟩
    · exact Or.inr ⟨v,m,ih _ vok⟩

def addr3 (x : Fin 3 → Bool) : Fin 8 := Fin.ofNat 8 ((x 0).toNat+2*(x 1).toNat+4*(x 2).toNat)
theorem leaf (endcheck : (reach 255 forbidden 4 [170,204,240]=false)) (y : Nat) (small : y<256) (hard : forbidden y=true) : LB 0 y 5 := by
  have tab : ∀ p : Fin 8, List.ofFn (fun i : Fin 3 => p.val.testBit i.val) =
      [170,204,240].map (fun t : Nat => t.testBit p.val) ∧
      addr3 (fun i : Fin 3 => p.val.testBit i.val) = p := by decide
  have deny := lower_of_search 3 8 (fun x => y.testBit (addr3 x).val) [170,204,240] y 4 small (by
    intro p hp
    obtain ⟨a,b⟩ := tab ⟨p,hp⟩
    exact ⟨fun i => p.testBit i.val,a,congrArg (fun j : Fin 8 => y.testBit j.val) b⟩) (by
    cases e : reach (2^8-1) (fun t => t % 2^8 == y) 4 [170,204,240] with
    | false => rfl
    | true =>
      exfalso
      apply Bool.false_ne_true (endcheck.symm.trans ?_)
      apply reach_goal (g:=fun t => t % 2^8 == y) (fun t ht => ?_) 4 _ e
      have q : t%256 = y := beq_iff_eq.mp ht
      simpa only [forbidden,q,Nat.mod_eq_of_lt small] using (show (0x20002aa024402442240224055ea00ea570057aa024402442240224055400040 : Nat).testBit y=true from by simpa [forbidden,Nat.mod_eq_of_lt small] using hard))
  intro s hs
  by_contra lt
  let pi : Fin 11 → Fin 3 := fun i => Fin.ofNat 3 i.val
  have rel := yn pi (f 0 y) s hs
  have ne : (fun x : Fin 3 → Bool => f 0 y (x ∘ pi)) = fun x => y.testBit (addr3 x).val := by
    funext x
    simp only [f,field,Nat.zero_testBit,Bool.false_eq_true,ite_false]
    rfl
  rw [ne] at rel
  obtain ⟨C,hm,hsize,co⟩ := rel
  exact deny ⟨C,hm,hsize.trans (by omega),co⟩

private theorem node_0_6_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 6 5 := leaf excluded 6 (by decide) (by decide)
private theorem node_0_22_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 22 5 := leaf excluded 22 (by decide) (by decide)
private theorem node_0_24_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 24 5 := leaf excluded 24 (by decide) (by decide)
private theorem node_0_26_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 26 5 := leaf excluded 26 (by decide) (by decide)
private theorem node_0_28_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 28 5 := leaf excluded 28 (by decide) (by decide)
private theorem node_0_30_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 30 5 := leaf excluded 30 (by decide) (by decide)
private theorem node_0_38_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 38 5 := leaf excluded 38 (by decide) (by decide)
private theorem node_0_41_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 41 5 := leaf excluded 41 (by decide) (by decide)
private theorem node_0_45_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 45 5 := leaf excluded 45 (by decide) (by decide)
private theorem node_0_54_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 54 5 := leaf excluded 54 (by decide) (by decide)
private theorem node_0_57_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 57 5 := leaf excluded 57 (by decide) (by decide)
private theorem node_0_61_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 61 5 := leaf excluded 61 (by decide) (by decide)
private theorem node_0_66_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 66 5 := leaf excluded 66 (by decide) (by decide)
private theorem node_0_70_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 70 5 := leaf excluded 70 (by decide) (by decide)
private theorem node_0_73_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 73 5 := leaf excluded 73 (by decide) (by decide)
private theorem node_0_82_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 82 5 := leaf excluded 82 (by decide) (by decide)
private theorem node_0_86_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 86 5 := leaf excluded 86 (by decide) (by decide)
private theorem node_0_89_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 89 5 := leaf excluded 89 (by decide) (by decide)
private theorem node_0_97_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 97 5 := leaf excluded 97 (by decide) (by decide)
private theorem node_0_99_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 99 5 := leaf excluded 99 (by decide) (by decide)
private theorem node_0_101_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 101 5 := leaf excluded 101 (by decide) (by decide)
private theorem node_0_103_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 103 5 := leaf excluded 103 (by decide) (by decide)
private theorem node_0_104_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 104 5 := leaf excluded 104 (by decide) (by decide)
private theorem node_0_105_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 105 5 := leaf excluded 105 (by decide) (by decide)
private theorem node_0_106_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 106 5 := leaf excluded 106 (by decide) (by decide)
private theorem node_0_108_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 108 5 := leaf excluded 108 (by decide) (by decide)
private theorem node_0_110_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 110 5 := leaf excluded 110 (by decide) (by decide)
private theorem node_0_120_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 120 5 := leaf excluded 120 (by decide) (by decide)
private theorem node_0_121_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 121 5 := leaf excluded 121 (by decide) (by decide)
private theorem node_0_122_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 122 5 := leaf excluded 122 (by decide) (by decide)
private theorem node_0_124_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 124 5 := leaf excluded 124 (by decide) (by decide)
private theorem node_0_126_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 126 5 := leaf excluded 126 (by decide) (by decide)
private theorem node_0_129_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 129 5 := leaf excluded 129 (by decide) (by decide)
private theorem node_0_131_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 131 5 := leaf excluded 131 (by decide) (by decide)
private theorem node_0_133_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 133 5 := leaf excluded 133 (by decide) (by decide)
private theorem node_0_134_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 134 5 := leaf excluded 134 (by decide) (by decide)
private theorem node_0_135_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 135 5 := leaf excluded 135 (by decide) (by decide)
private theorem node_0_145_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 145 5 := leaf excluded 145 (by decide) (by decide)
private theorem node_0_147_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 147 5 := leaf excluded 147 (by decide) (by decide)
private theorem node_0_149_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 149 5 := leaf excluded 149 (by decide) (by decide)
private theorem node_0_150_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 150 5 := leaf excluded 150 (by decide) (by decide)
private theorem node_0_151_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 151 5 := leaf excluded 151 (by decide) (by decide)
private theorem node_0_152_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 152 5 := leaf excluded 152 (by decide) (by decide)
private theorem node_0_154_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 154 5 := leaf excluded 154 (by decide) (by decide)
private theorem node_0_156_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 156 5 := leaf excluded 156 (by decide) (by decide)
private theorem node_0_158_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 158 5 := leaf excluded 158 (by decide) (by decide)
private theorem node_0_166_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 166 5 := leaf excluded 166 (by decide) (by decide)
private theorem node_0_169_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 169 5 := leaf excluded 169 (by decide) (by decide)
private theorem node_0_173_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 173 5 := leaf excluded 173 (by decide) (by decide)
private theorem node_0_182_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 182 5 := leaf excluded 182 (by decide) (by decide)
private theorem node_0_185_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 185 5 := leaf excluded 185 (by decide) (by decide)
private theorem node_0_189_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 189 5 := leaf excluded 189 (by decide) (by decide)
private theorem node_0_194_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 194 5 := leaf excluded 194 (by decide) (by decide)
private theorem node_0_198_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 198 5 := leaf excluded 198 (by decide) (by decide)
private theorem node_0_201_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 201 5 := leaf excluded 201 (by decide) (by decide)
private theorem node_0_210_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 210 5 := leaf excluded 210 (by decide) (by decide)
private theorem node_0_214_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 214 5 := leaf excluded 214 (by decide) (by decide)
private theorem node_0_217_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 217 5 := leaf excluded 217 (by decide) (by decide)
private theorem node_0_225_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 225 5 := leaf excluded 225 (by decide) (by decide)
private theorem node_0_227_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 227 5 := leaf excluded 227 (by decide) (by decide)
private theorem node_0_229_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 229 5 := leaf excluded 229 (by decide) (by decide)
private theorem node_0_231_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 231 5 := leaf excluded 231 (by decide) (by decide)
private theorem node_0_233_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 233 5 := leaf excluded 233 (by decide) (by decide)
private theorem node_0_249_5 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 0 249 5 := leaf excluded 249 (by decide) (by decide)
private theorem node_16_104_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 16 104 7 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 0,mask 3,by decide⟩ ⟨mask 0,mask 3,by decide⟩ (by decide) (by decide) (node_0_104_5 excluded) (node_0_120_5 excluded)
private theorem node_16_106_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 16 106 7 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_0_106_5 excluded) (node_0_122_5 excluded)
private theorem node_16_108_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 16 108 7 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 0,mask 2,by decide⟩ ⟨mask 0,mask 2,by decide⟩ (by decide) (by decide) (node_0_108_5 excluded) (node_0_124_5 excluded)
private theorem node_16_110_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 16 110 7 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_0_110_5 excluded) (node_0_126_5 excluded)
private theorem node_16_129_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 16 129 7 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_0_129_5 excluded) (node_0_145_5 excluded)
private theorem node_16_131_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 16 131 7 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 2,mask 0,by decide⟩ ⟨mask 2,mask 0,by decide⟩ (by decide) (by decide) (node_0_131_5 excluded) (node_0_147_5 excluded)
private theorem node_16_133_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 16 133 7 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_0_133_5 excluded) (node_0_149_5 excluded)
private theorem node_16_135_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 16 135 7 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 3,mask 0,by decide⟩ ⟨mask 3,mask 0,by decide⟩ (by decide) (by decide) (node_0_135_5 excluded) (node_0_151_5 excluded)
private theorem node_128_6_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 6 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_0_6_5 excluded) (node_0_134_5 excluded)
private theorem node_128_22_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 22 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_0_22_5 excluded) (node_0_150_5 excluded)
private theorem node_128_24_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 24 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 0,mask 3,by decide⟩ ⟨mask 0,mask 3,by decide⟩ (by decide) (by decide) (node_0_24_5 excluded) (node_0_152_5 excluded)
private theorem node_128_26_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 26 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_0_26_5 excluded) (node_0_154_5 excluded)
private theorem node_128_28_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 28 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 0,mask 2,by decide⟩ ⟨mask 0,mask 2,by decide⟩ (by decide) (by decide) (node_0_28_5 excluded) (node_0_156_5 excluded)
private theorem node_128_30_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 30 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_0_30_5 excluded) (node_0_158_5 excluded)
private theorem node_128_38_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 38 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_0_38_5 excluded) (node_0_166_5 excluded)
private theorem node_128_41_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 41 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_0_41_5 excluded) (node_0_169_5 excluded)
private theorem node_128_45_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 45 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_0_45_5 excluded) (node_0_173_5 excluded)
private theorem node_128_54_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 54 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_0_54_5 excluded) (node_0_182_5 excluded)
private theorem node_128_57_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 57 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_0_57_5 excluded) (node_0_185_5 excluded)
private theorem node_128_61_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 61 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_0_61_5 excluded) (node_0_189_5 excluded)
private theorem node_128_66_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 66 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_0_66_5 excluded) (node_0_194_5 excluded)
private theorem node_128_70_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 70 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_0_70_5 excluded) (node_0_198_5 excluded)
private theorem node_128_73_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 73 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_0_73_5 excluded) (node_0_201_5 excluded)
private theorem node_128_82_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 82 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_0_82_5 excluded) (node_0_210_5 excluded)
private theorem node_128_86_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 86 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_0_86_5 excluded) (node_0_214_5 excluded)
private theorem node_128_89_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 89 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_0_89_5 excluded) (node_0_217_5 excluded)
private theorem node_128_97_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 97 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_0_97_5 excluded) (node_0_225_5 excluded)
private theorem node_128_99_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 99 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 2,mask 0,by decide⟩ ⟨mask 2,mask 0,by decide⟩ (by decide) (by decide) (node_0_99_5 excluded) (node_0_227_5 excluded)
private theorem node_128_101_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 101 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_0_101_5 excluded) (node_0_229_5 excluded)
private theorem node_128_103_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 103 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 3,mask 0,by decide⟩ ⟨mask 3,mask 0,by decide⟩ (by decide) (by decide) (node_0_103_5 excluded) (node_0_231_5 excluded)
private theorem node_128_105_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 105 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_0_105_5 excluded) (node_0_233_5 excluded)
private theorem node_128_121_7 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 128 121 7 := two (7 : Fin 8) ⟨mask 7,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_0_121_5 excluded) (node_0_249_5 excluded)
private theorem node_20_104_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 20 104 9 := two (2 : Fin 8) ⟨mask 2,by decide⟩ ⟨mask 0,mask 3,by decide⟩ ⟨mask 0,mask 2,by decide⟩ (by decide) (by decide) (node_16_104_7 excluded) (node_16_108_7 excluded)
private theorem node_20_106_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 20 106 9 := two (2 : Fin 8) ⟨mask 2,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_16_106_7 excluded) (node_16_110_7 excluded)
private theorem node_20_129_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 20 129 9 := two (2 : Fin 8) ⟨mask 2,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_16_129_7 excluded) (node_16_133_7 excluded)
private theorem node_20_131_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 20 131 9 := two (2 : Fin 8) ⟨mask 2,by decide⟩ ⟨mask 2,mask 0,by decide⟩ ⟨mask 3,mask 0,by decide⟩ (by decide) (by decide) (node_16_131_7 excluded) (node_16_135_7 excluded)
private theorem node_132_24_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 132 24 9 := two (2 : Fin 8) ⟨mask 2,by decide⟩ ⟨mask 0,mask 3,by decide⟩ ⟨mask 0,mask 2,by decide⟩ (by decide) (by decide) (node_128_24_7 excluded) (node_128_28_7 excluded)
private theorem node_132_26_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 132 26 9 := two (2 : Fin 8) ⟨mask 2,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_128_26_7 excluded) (node_128_30_7 excluded)
private theorem node_132_97_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 132 97 9 := two (2 : Fin 8) ⟨mask 2,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_128_97_7 excluded) (node_128_101_7 excluded)
private theorem node_132_99_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 132 99 9 := two (2 : Fin 8) ⟨mask 2,by decide⟩ ⟨mask 2,mask 0,by decide⟩ ⟨mask 3,mask 0,by decide⟩ (by decide) (by decide) (node_128_99_7 excluded) (node_128_103_7 excluded)
private theorem node_144_41_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 144 41 9 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_128_41_7 excluded) (node_128_57_7 excluded)
private theorem node_144_45_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 144 45 9 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_128_45_7 excluded) (node_128_61_7 excluded)
private theorem node_144_66_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 144 66 9 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_128_66_7 excluded) (node_128_82_7 excluded)
private theorem node_144_70_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 144 70 9 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_128_70_7 excluded) (node_128_86_7 excluded)
private theorem node_160_6_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 160 6 9 := two (5 : Fin 8) ⟨mask 5,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_128_6_7 excluded) (node_128_38_7 excluded)
private theorem node_160_22_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 160 22 9 := two (5 : Fin 8) ⟨mask 5,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_128_22_7 excluded) (node_128_54_7 excluded)
private theorem node_160_73_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 160 73 9 := two (5 : Fin 8) ⟨mask 5,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_128_73_7 excluded) (node_128_105_7 excluded)
private theorem node_160_89_9 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 160 89 9 := two (5 : Fin 8) ⟨mask 5,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_128_89_7 excluded) (node_128_121_7 excluded)
private theorem node_22_104_11 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 22 104 11 := two (1 : Fin 8) ⟨mask 1,by decide⟩ ⟨mask 0,mask 3,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_20_104_9 excluded) (node_20_106_9 excluded)
private theorem node_22_129_11 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 22 129 11 := two (1 : Fin 8) ⟨mask 1,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 2,mask 0,by decide⟩ (by decide) (by decide) (node_20_129_9 excluded) (node_20_131_9 excluded)
private theorem node_134_24_11 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 134 24 11 := two (1 : Fin 8) ⟨mask 1,by decide⟩ ⟨mask 0,mask 3,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_132_24_9 excluded) (node_132_26_9 excluded)
private theorem node_134_97_11 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 134 97 11 := two (1 : Fin 8) ⟨mask 1,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 2,mask 0,by decide⟩ (by decide) (by decide) (node_132_97_9 excluded) (node_132_99_9 excluded)
private theorem node_148_41_11 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 148 41 11 := two (2 : Fin 8) ⟨mask 2,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_144_41_9 excluded) (node_144_45_9 excluded)
private theorem node_148_66_11 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 148 66 11 := two (2 : Fin 8) ⟨mask 2,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_144_66_9 excluded) (node_144_70_9 excluded)
private theorem node_176_6_11 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 176 6 11 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_160_6_9 excluded) (node_160_22_9 excluded)
private theorem node_176_73_11 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 176 73 11 := two (4 : Fin 8) ⟨mask 4,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_160_73_9 excluded) (node_160_89_9 excluded)
private theorem node_150_1_12 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 150 1 12 := one (7 : Fin 8) true ⟨mask 7,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (node_22_129_11 excluded)
private theorem node_150_104_12 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 150 104 12 := one (7 : Fin 8) false ⟨mask 7,by decide⟩ ⟨mask 0,mask 3,by decide⟩ (by decide) (node_22_104_11 excluded)
private theorem node_180_2_12 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 180 2 12 := one (2 : Fin 8) true ⟨mask 2,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (node_176_6_11 excluded)
private theorem node_180_9_12 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 180 9 12 := one (5 : Fin 8) true ⟨mask 5,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (node_148_41_11 excluded)
private theorem node_180_66_12 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 180 66 12 := one (5 : Fin 8) false ⟨mask 5,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (node_148_66_11 excluded)
private theorem node_180_73_12 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 180 73 12 := one (2 : Fin 8) false ⟨mask 2,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (node_176_73_11 excluded)
private theorem node_198_24_12 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 198 24 12 := one (6 : Fin 8) false ⟨mask 6,by decide⟩ ⟨mask 0,mask 3,by decide⟩ (by decide) (node_134_24_11 excluded)
private theorem node_198_33_12 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 198 33 12 := one (6 : Fin 8) true ⟨mask 6,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (node_134_97_11 excluded)
private theorem node_214_1_13 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 214 1 13 := one (6 : Fin 8) false ⟨mask 6,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (node_150_1_12 excluded)
private theorem node_214_8_13 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 214 8 13 := one (4 : Fin 8) true ⟨mask 4,by decide⟩ ⟨mask 0,mask 3,by decide⟩ (by decide) (node_198_24_12 excluded)
private theorem node_214_33_13 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 214 33 13 := one (4 : Fin 8) false ⟨mask 4,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (node_198_33_12 excluded)
private theorem node_214_40_13 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 214 40 13 := one (6 : Fin 8) true ⟨mask 6,by decide⟩ ⟨mask 0,mask 3,by decide⟩ (by decide) (node_150_104_12 excluded)
private theorem node_244_2_14 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 244 2 14 := two (6 : Fin 8) ⟨mask 6,by decide⟩ ⟨mask 0,mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (by decide) (node_180_2_12 excluded) (node_180_66_12 excluded)
private theorem node_244_9_14 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 244 9 14 := two (6 : Fin 8) ⟨mask 6,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_180_9_12 excluded) (node_180_73_12 excluded)
private theorem node_246_0_15 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 246 0 15 := one (1 : Fin 8) true ⟨mask 1,by decide⟩ ⟨mask 0,mask 1,by decide⟩ (by decide) (node_244_2_14 excluded)
private theorem node_246_1_15 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 246 1 15 := two (5 : Fin 8) ⟨mask 5,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_214_1_13 excluded) (node_214_33_13 excluded)
private theorem node_246_8_15 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 246 8 15 := two (5 : Fin 8) ⟨mask 5,by decide⟩ ⟨mask 0,mask 3,by decide⟩ ⟨mask 0,mask 3,by decide⟩ (by decide) (by decide) (node_214_8_13 excluded) (node_214_40_13 excluded)
private theorem node_246_9_15 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 246 9 15 := one (1 : Fin 8) false ⟨mask 1,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (node_244_9_14 excluded)
private theorem node_254_0_17 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 254 0 17 := two (3 : Fin 8) ⟨mask 3,by decide⟩ ⟨mask 0,mask 17,by decide⟩ ⟨mask 0,mask 3,by decide⟩ (by decide) (by decide) (node_246_0_15 excluded) (node_246_8_15 excluded)
private theorem node_254_1_17 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 254 1 17 := two (3 : Fin 8) ⟨mask 3,by decide⟩ ⟨mask 1,mask 0,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_246_1_15 excluded) (node_246_9_15 excluded)
private theorem node_255_0_19 (excluded : (reach 255 forbidden 4 [170,204,240]=false)) : LB 255 0 19 := two (0 : Fin 8) ⟨mask 0,by decide⟩ ⟨mask 0,mask 17,by decide⟩ ⟨mask 1,mask 0,by decide⟩ (by decide) (by decide) (node_254_0_17 excluded) (node_254_1_17 excluded)

def posted (x : Fin 11 → Bool) := (List.ofFn x).getD (3+(1*(x 0).toNat+2*(x 1).toNat+4*(x 2).toNat)) false
theorem root_eq : f 255 0 = posted := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [f,addr,field,slot,posted,h0,h1,h2,List.getD_eq_getElem?_getD] <;> intro _ <;> decide
theorem lower (excluded : (reach 255 forbidden 4 [170,204,240]=false)) (s : Nat) (c : HasCircuitSize 11 posted s) : 19 ≤ s := by
  rw [←root_eq] at c
  exact node_255_0_19 excluded s c

theorem kernel_lower (s : Nat) (c : HasCircuitSize 11 posted s) : 19≤s := lower bank_root s c

end Mux9939Lower

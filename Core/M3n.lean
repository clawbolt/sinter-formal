import Core.M3

/-!
# M3（二）：n 个参数的调用，以及求值顺序

把 M3（一）的两参数调用推广到任意多个参数：

* **静态检查**：所有参数都必须拥有值；任意两个参数如果是同一个变量，必须都是 `read`
  （`exclB`，两两检查）。调用之后，`sink` 的参数不再拥有值。
* **动态语义**：调用开始时取出所有参数的指针（`capture`），依次处理每个参数（`effAll`，
  和 M3（一）的 `eff` 相同），最后再检查一遍所有 `read` 参数（`recheckAll`）。

**主定理** `safety_and_no_leak`：检查器接受的程序，执行和作用域结束时的释放都不会出错，
结束时没有泄漏。

**求值顺序**：`v.push(v.len())` 写成“先调用 `len(read v)`，结果放进临时变量，
再调用 `push(inout v, sink tmp)`”。只读借用在第一次调用结束时就结束了，
所以检查器直接接受，不需要 Rust 的“两阶段借用”特例。见文件末尾的例子。

证明里最关键的不变式（`effAll_sound`）：处理到某个参数时，后面所有还没处理的参数
仍然拥有值、指针没变、位置还活着。成立的原因有两条：
不是 `read` 的参数，变量和其他所有参数都不同（排他性）；
不同变量的指针也不同（拥有者唯一）。
-/

namespace Core.M3n
open Core.M1 (Stmt)
open Core.M2b
open Core.M3 (Mode Arg afterArg afterArg_apply eff eff_spec recheck recheck_ok)

/-! ## 静态检查 -/

/-- 两两检查排他性：同一个变量出现两次，两次都必须是 `read`。 -/
def exclB : List Arg → Bool
  | []      => true
  | a :: as =>
    as.all (fun b => decide (a.x ≠ b.x) || (decide (a.m = .read) && decide (b.m = .read)))
      && exclB as

def afterAll : List Arg → SEnv → SEnv
  | [],      σ => σ
  | a :: as, σ => afterAll as (afterArg a σ)

def checkCallN (σ : SEnv) (args : List Arg) : Option SEnv :=
  if args.all (fun a => decide (σ a.x = .yes)) = true ∧ exclB args = true then
    some (afterAll args σ)
  else none

/-! ## 动态语义 -/

def capture (s : St) : List Arg → Option (List (Arg × Loc))
  | []      => some []
  | a :: as =>
    match s.env a.x, capture s as with
    | some l, some cs => some ((a, l) :: cs)
    | _, _            => none

def effAll : List (Arg × Loc) → St → Option St
  | [],           s => some s
  | (a, l) :: cs, s =>
    match eff a.m a.x l s with
    | some s' => effAll cs s'
    | none    => none

def recheckAll : List (Arg × Loc) → St → Option St
  | [],           s => some s
  | (a, l) :: cs, s =>
    match recheck a.m l s with
    | some s' => recheckAll cs s'
    | none    => none

def execCallN (s : St) (args : List Arg) : Option St :=
  match capture s args with
  | some cs =>
    match effAll cs s with
    | some s' => recheckAll cs s'
    | none    => none
  | none => none

/-! ## 辅助定义与引理 -/

def PreAll (s : St) (cs : List (Arg × Loc)) : Prop :=
  ∀ p ∈ cs, s.flag p.1.x = true ∧ s.env p.1.x = some p.2 ∧ s.live p.2 = true

def ExclP : List (Arg × Loc) → Prop
  | []      => True
  | p :: ps => (∀ q ∈ ps, p.1.x ≠ q.1.x ∨ (p.1.m = .read ∧ q.1.m = .read)) ∧ ExclP ps

theorem exclP_of (cs : List (Arg × Loc)) (h : exclB (cs.map Prod.fst) = true) : ExclP cs := by
  induction cs with
  | nil => simp [ExclP]
  | cons p ps ih =>
    simp only [List.map, exclB, Bool.and_eq_true, List.all_eq_true] at h
    simp only [ExclP]
    refine ⟨?_, ih h.2⟩
    intro q hq
    have := h.1 q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
    simpa using this

/-- 两两排他性的直接形式：同一个变量的两个参数，要么都只读，要么就是同一个参数。 -/
theorem exclP_pair : ∀ {cs : List (Arg × Loc)} {p q : Arg × Loc}, ExclP cs → p ∈ cs → q ∈ cs →
    p.1.x = q.1.x → (p.1.m = .read ∧ q.1.m = .read) ∨ p = q := by
  intro cs
  induction cs with
  | nil => intro p q _ hp; cases hp
  | cons r rs ih =>
    intro p q hex hp hq hxx
    simp only [ExclP] at hex
    obtain ⟨hh, ht⟩ := hex
    rcases List.mem_cons.mp hp with rfl | hp'
    · rcases List.mem_cons.mp hq with rfl | hq'
      · right; rfl
      · rcases hh q hq' with h | h
        · exact absurd hxx h
        · left; exact h
    · rcases List.mem_cons.mp hq with rfl | hq'
      · rcases hh p hp' with h | h
        · exact absurd hxx.symm h
        · left; exact ⟨h.2, h.1⟩
      · exact ih ht hp' hq' hxx

theorem capture_ok {N : Nat} {s : St} (hd : DInv N s) (args : List Arg)
    (hf : ∀ a ∈ args, s.flag a.x = true) :
    ∃ cs, capture s args = some cs ∧ cs.map Prod.fst = args ∧ PreAll s cs := by
  induction args with
  | nil => exact ⟨[], rfl, rfl, by intro p hp; cases hp⟩
  | cons a as ih =>
    have hfa := hf a (by simp)
    obtain ⟨l, hl, hlive⟩ := hd.owned_live a.x hfa
    obtain ⟨cs, hc, hm, hp⟩ := ih (fun b hb => hf b (by simp [hb]))
    refine ⟨(a, l) :: cs, by simp only [capture, hl, hc], by simp [hm], ?_⟩
    intro p hp'
    rcases List.mem_cons.mp hp' with rfl | hp''
    · exact ⟨hfa, hl, hlive⟩
    · exact hp p hp''

theorem effAll_sound {N : Nat} (cs : List (Arg × Loc)) :
    ∀ (s : St), DInv N s → PreAll s cs → ExclP cs →
    ∃ s', effAll cs s = some s' ∧ DInv N s' ∧
      (∀ y, (∀ p ∈ cs, p.1.x ≠ y) → s'.flag y = s.flag y) ∧
      (∀ p ∈ cs, p.1.m = .sink → s'.flag p.1.x = false) ∧
      (∀ p ∈ cs, p.1.m ≠ .sink → s'.flag p.1.x = true) ∧
      (∀ k, (∀ p ∈ cs, p.1.m ≠ .read → p.2 ≠ k) → s.live k = true → s'.live k = true) := by
  induction cs with
  | nil =>
    intro s hd _ _
    refine ⟨s, rfl, hd, fun _ _ => rfl, ?_, ?_, fun _ _ h => h⟩
    · intro p hp; cases hp
    · intro p hp; cases hp
  | cons p ps ih =>
    intro s hd hpre hex
    obtain ⟨⟨m, x⟩, l⟩ := p
    simp only [ExclP] at hex
    obtain ⟨hexh, hext⟩ := hex
    obtain ⟨hf, he, hlive⟩ := hpre (⟨m, x⟩, l) (by simp)
    obtain ⟨s1, he1, hd1, fr1, lv1, sk1, nsk1, rd1⟩ := eff_spec m hd hf he hlive
    -- 处理完当前参数之后，后面的参数仍然完好
    have hpre1 : PreAll s1 ps := by
      intro q hq
      obtain ⟨hqf, hqe, hql⟩ := hpre q (by simp [hq])
      by_cases hqx : q.1.x = x
      · have hrd : m = .read ∧ q.1.m = .read := by
          rcases hexh q hq with h | h
          · exact absurd hqx.symm h
          · exact h
        rw [rd1 hrd.1]
        exact ⟨hqf, hqe, hql⟩
      · have hql' : q.2 ≠ l := by
          intro h
          rw [h] at hqe
          exact hqx (hd.unique q.1.x x l hqf hf hqe he)
        exact ⟨by rw [(fr1 q.1.x hqx).1]; exact hqf,
               by rw [(fr1 q.1.x hqx).2]; exact hqe,
               lv1 q.2 hql' hql⟩
    obtain ⟨s2, he2, hd2, fr2, sk2, nsk2, lv2⟩ := ih s1 hd1 hpre1 hext
    refine ⟨s2, ?_, hd2, ?_, ?_, ?_, ?_⟩
    · simp only [effAll, he1, he2]
    · intro y hy
      have hyx : x ≠ y := hy (⟨m, x⟩, l) (by simp)
      rw [fr2 y (fun q hq => hy q (by simp [hq])), (fr1 y (Ne.symm hyx)).1]
    · intro q hq hqs
      rcases List.mem_cons.mp hq with rfl | hq'
      · show s2.flag x = false
        -- 当前参数是 sink：排他性保证后面没有同一个变量
        have hnot : ∀ r ∈ ps, r.1.x ≠ x := by
          intro r hr
          rcases hexh r hr with h | h
          · exact Ne.symm h
          · have h1 : m = Mode.read := h.1
            have h2 : m = Mode.sink := hqs
            rw [h2] at h1
            cases h1
        rw [fr2 x hnot]
        exact sk1 hqs
      · exact sk2 q hq' hqs
    · intro q hq hqs
      rcases List.mem_cons.mp hq with rfl | hq'
      · show s2.flag x = true
        have h1 : s1.flag x = true := nsk1 hqs
        rcases Classical.em (∃ r ∈ ps, r.1.x = x) with ⟨r, hr, hrx⟩ | hno
        · -- 后面还有同一个变量：排他性要求它也只读，结论来自归纳假设
          have hrd : r.1.m ≠ .sink := by
            rcases hexh r hr with h | h
            · exact absurd hrx.symm h
            · rw [h.2]; decide
          have := nsk2 r hr hrd
          rw [hrx] at this
          exact this
        · have hnot : ∀ r ∈ ps, r.1.x ≠ x := fun r hr hrx => hno ⟨r, hr, hrx⟩
          rw [fr2 x hnot]
          exact h1
      · exact nsk2 q hq' hqs
    · intro k hk hsk
      have h1 : s1.live k = true := by
        by_cases hmr : m = .read
        · rw [rd1 hmr]; exact hsk
        · exact lv1 k (fun h => hk (⟨m, x⟩, l) (by simp) hmr h.symm) hsk
      exact lv2 k (fun q hq => hk q (by simp [hq])) h1

theorem recheckAll_ok (cs : List (Arg × Loc)) :
    ∀ (s : St), (∀ p ∈ cs, p.1.m = .read → s.live p.2 = true) → recheckAll cs s = some s := by
  induction cs with
  | nil => intro s _; rfl
  | cons p ps ih =>
    intro s h
    obtain ⟨a, l⟩ := p
    have h1 : recheck a.m l s = some s := recheck_ok (h (a, l) (by simp))
    simp only [recheckAll, h1]
    exact ih s (fun q hq => h q (by simp [hq]))

theorem afterAll_keep_no (as : List Arg) :
    ∀ (σ : SEnv) (z : Var), σ z = .no → afterAll as σ z = .no := by
  induction as with
  | nil => intro σ z h; exact h
  | cons a as ih =>
    intro σ z h
    apply ih
    rw [afterArg_apply]
    split <;> simp [h]

theorem afterAll_sink (as : List Arg) : ∀ (σ : SEnv) (z : Var),
    (∃ a ∈ as, a.m = .sink ∧ a.x = z) → afterAll as σ z = .no := by
  induction as with
  | nil => intro σ z h; obtain ⟨a, ha, _⟩ := h; cases ha
  | cons a as ih =>
    intro σ z h
    obtain ⟨b, hb, hbs, hbz⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb'
    · show afterAll as (afterArg b σ) z = .no
      apply afterAll_keep_no
      rw [afterArg_apply]
      simp [hbs, hbz]
    · exact ih _ z ⟨b, hb', hbs, hbz⟩

theorem afterAll_other (as : List Arg) : ∀ (σ : SEnv) (z : Var),
    (∀ a ∈ as, a.m = .sink → a.x ≠ z) → afterAll as σ z = σ z := by
  induction as with
  | nil => intro σ z _; rfl
  | cons a as ih =>
    intro σ z h
    show afterAll as (afterArg a σ) z = σ z
    rw [ih _ z (fun b hb => h b (by simp [hb])), afterArg_apply]
    have hn : ¬ (a.m = .sink ∧ z = a.x) := fun ⟨h1, h2⟩ => h a (by simp) h1 h2.symm
    split
    · rename_i hc; exact absurd hc hn
    · rfl

/-! ## 调用 -/

theorem callN_sound {N : Nat} {σ σ' : SEnv} {s : St} {args : List Arg}
    (hc : checkCallN σ args = some σ') (hc0 : Compat σ s.flag) (hd : DInv N s) :
    ∃ s', execCallN s args = some s' ∧ Compat σ' s'.flag ∧ DInv N s' := by
  simp only [checkCallN] at hc
  split at hc
  · rename_i hcond
    cases hc
    obtain ⟨hown, hex⟩ := hcond
    have hown' : ∀ a ∈ args, σ a.x = .yes := by
      intro a ha
      have := List.all_eq_true.mp hown a ha
      simpa using this
    have hf : ∀ a ∈ args, s.flag a.x = true := fun a ha => hc0.yes a.x (hown' a ha)
    obtain ⟨cs, hcap, hmap, hpre⟩ := capture_ok hd args hf
    subst hmap
    have hexP := exclP_of cs hex
    obtain ⟨s', he, hd', fr, sk, nsk, lv⟩ := effAll_sound cs s hd hpre hexP
    -- 只读参数的位置在处理完所有参数后仍然活着
    have hrc : recheckAll cs s' = some s' := by
      apply recheckAll_ok
      intro p hp hpr
      obtain ⟨hpf, hpe, hpl⟩ := hpre p hp
      refine lv p.2 ?_ hpl
      intro q hq hqr hqp
      obtain ⟨hqf, hqe, _⟩ := hpre q hq
      have hxx : q.1.x = p.1.x := by
        rw [hqp] at hqe
        exact hd.unique q.1.x p.1.x p.2 hqf hpf hqe hpe
      rcases exclP_pair hexP hq hp hxx with h | h
      · exact hqr h.1
      · rw [h] at hqr; exact hqr hpr
    refine ⟨s', ?_, ?_, hd'⟩
    · simp only [execCallN, hcap, he, hrc]
    · constructor
      · intro z hz
        rcases Classical.em (∃ a ∈ cs.map Prod.fst, a.m = .sink ∧ a.x = z) with hs | hns
        · rw [afterAll_sink _ σ z hs] at hz; cases hz
        · have hns' : ∀ a ∈ cs.map Prod.fst, a.m = .sink → a.x ≠ z :=
            fun a ha has hax => hns ⟨a, ha, has, hax⟩
          rw [afterAll_other _ σ z hns'] at hz
          rcases Classical.em (∃ p ∈ cs, p.1.x = z) with ⟨p, hp, hpz⟩ | hnz
          · have hps : p.1.m ≠ .sink := fun h =>
              hns' p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩) h hpz
            rw [← hpz]
            exact nsk p hp hps
          · rw [fr z (fun p hp hpz => hnz ⟨p, hp, hpz⟩)]
            exact hc0.yes z hz
      · intro z hz
        rcases Classical.em (∃ a ∈ cs.map Prod.fst, a.m = .sink ∧ a.x = z) with hs | hns
        · obtain ⟨a, ha, has, hax⟩ := hs
          obtain ⟨p, hp, hpa⟩ := List.mem_map.mp ha
          rw [← hax, ← hpa]
          exact sk p hp (by rw [hpa]; exact has)
        · have hns' : ∀ a ∈ cs.map Prod.fst, a.m = .sink → a.x ≠ z :=
            fun a ha has hax => hns ⟨a, ha, has, hax⟩
          rw [afterAll_other _ σ z hns'] at hz
          have hnz : ∀ p ∈ cs, p.1.x ≠ z := by
            intro p hp hpz
            have := hown' p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
            rw [hpz, hz] at this
            cases this
          rw [fr z hnz]
          exact hc0.no z hz
  · contradiction

/-! ## 语句列表 -/

inductive S3n
  | base (t : Stmt)
  | call (args : List Arg)

def checkSn (N : Nat) (σ : SEnv) : S3n → Option SEnv
  | .base t    => checkStmtV N σ t
  | .call args => checkCallN σ args

def checkListN (N : Nat) (σ : SEnv) : List S3n → Option SEnv
  | []      => some σ
  | t :: ts =>
    match checkSn N σ t with
    | some σ' => checkListN N σ' ts
    | none    => none

def execSn (s : St) : S3n → Option St
  | .base t    => execS s t
  | .call args => execCallN s args

def execListN (s : St) : List S3n → Option St
  | []      => some s
  | t :: ts =>
    match execSn s t with
    | some s' => execListN s' ts
    | none    => none

theorem stepSn {N : Nat} {σ σ' : SEnv} {s : St} {t : S3n}
    (hc : checkSn N σ t = some σ') (hc0 : Compat σ s.flag) (hd : DInv N s) :
    ∃ s', execSn s t = some s' ∧ Compat σ' s'.flag ∧ DInv N s' := by
  cases t with
  | base t =>
    simp only [checkSn, checkStmtV] at hc
    split at hc
    · rename_i hv
      exact stepS hv hc hc0 hd
    · contradiction
  | call args =>
    simp only [checkSn] at hc
    exact callN_sound hc hc0 hd

theorem listSoundN (N : Nat) (ts : List S3n) :
    ∀ {σ σ' : SEnv} {s : St}, checkListN N σ ts = some σ' → Compat σ s.flag → DInv N s →
      ∃ s', execListN s ts = some s' ∧ Compat σ' s'.flag ∧ DInv N s' := by
  induction ts with
  | nil =>
    intro σ σ' s hc hc0 hd
    simp [checkListN] at hc
    subst hc
    exact ⟨s, by simp [execListN], hc0, hd⟩
  | cons t ts ih =>
    intro σ σ' s hc hc0 hd
    simp only [checkListN] at hc
    split at hc
    · rename_i σ₁ h₁
      obtain ⟨s₁, he₁, hc₁, hd₁⟩ := stepSn h₁ hc0 hd
      obtain ⟨s₂, he₂, hc₂, hd₂⟩ := ih hc hc₁ hd₁
      exact ⟨s₂, by simp only [execListN, he₁, he₂], hc₂, hd₂⟩
    · contradiction

/-! ## 主定理 -/

/-- **M3（二）主定理。** 检查器接受的程序（普通语句 + 任意多参数的调用），
执行和作用域结束时按 drop flag 的释放都不会出错，并且结束时堆上没有活着的值。 -/
theorem safety_and_no_leak (N : Nat) (ts : List S3n) (σ' : SEnv)
    (h : checkListN N (fun _ => .no) ts = some σ') :
    ∃ s', (execListN St.empty ts).bind (fun s => dropAll s N) = some s' ∧
      ∀ l, s'.live l = false := by
  obtain ⟨s₁, he₁, _, hd₁⟩ := listSoundN N ts h compat_empty (dinv_empty N)
  obtain ⟨s₂, he₂, hd₂, hf₂⟩ := dropAll_sound hd₁ N
  refine ⟨s₂, by rw [he₁]; exact he₂, ?_⟩
  intro l
  cases hl : s₂.live l with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨x, hx, _⟩ := hd₂.live_owned l hl
    have hxN := hd₂.bound x hx
    rw [hf₂ x hxN] at hx
    contradiction

/-! ## 例子 -/

/-- `v.push(v.len())`：先 `len(read v)`，结果放进临时变量 1，再 `push(inout v, sink 1)`。
只读借用在第一次调用结束时就结束了，检查器直接接受。 -/
def pushLen : List S3n :=
  [.base (.alloc 0),
   .call [⟨.read, 0⟩],
   .base (.alloc 1),
   .call [⟨.inout, 0⟩, ⟨.sink, 1⟩]]

example : (checkListN 2 (fun _ => .no) pushLen).isSome = true := rfl
example : ((execListN St.empty pushLen).bind (fun s => dropAll s 2)).isSome = true := rfl

/-- 三个参数：0 被读两次，1 可变借用。合法。 -/
def threeOk : List S3n :=
  [.base (.alloc 0), .base (.alloc 1), .call [⟨.read, 0⟩, ⟨.inout, 1⟩, ⟨.read, 0⟩]]

example : (checkListN 2 (fun _ => .no) threeOk).isSome = true := rfl
example : ((execListN St.empty threeOk).bind (fun s => dropAll s 2)).isSome = true := rfl

/-- 三个参数：0 先被读，后面又以 `inout` 传入。检查器拒绝，不经检查执行真的会出错。 -/
def threeBad : List S3n :=
  [.base (.alloc 0), .base (.alloc 1), .call [⟨.read, 0⟩, ⟨.read, 1⟩, ⟨.inout, 0⟩]]

example : (checkListN 2 (fun _ => .no) threeBad).isNone = true := rfl
example : (execListN St.empty threeBad).isNone = true := rfl

end Core.M3n

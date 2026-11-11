import Core.Calls.NArgs
import Core.Projection.Lock

/-!
# 投影作为调用参数

在 `Projection.Lock` 的命令之外加入调用 `call args prs`：
- `args`：拥有者参数，和 `Calls.NArgs` 一样带 `read` / `inout` / `sink` 约定；
- `prs`：以只读方式传入的投影。

**静态检查**（在 `Calls.NArgs` 的 `checkCallN` 之外加两条）：
- 被锁定的源对象只能以 `read` 传入，不能 `inout`、不能 `sink`；
- 传入的投影必须还活着。

**动态语义**：调用开始和结束时，被调函数都可能通过传入的投影读取，
所以两个时刻都检查投影指向的位置是否活着，不活着就出错。
`inout` 在模型里是“释放旧值、分配新值”，所以如果允许把被锁定的源对象以 `inout` 传入，
投影就会悬空。文件末尾的例子演示了这一点。

**不能带出函数**：在这个模型里，投影只能作为只读参数传入，调用不返回任何指针，
被调函数没有办法把投影存下来或交给调用者。返回值里带借用的情况属于区域，在 `Regions.Model` 处理。

**主定理** `safety_and_no_leak`：检查器接受的程序执行不出错，作用域结束后没有泄漏。

证明的关键是调用的“框架引理” `execCallN_env`：只以 `read` 方式出现、或者根本没出现的变量，
调用前后指针不变。被锁定的源对象正属于这一类，所以投影和源对象仍然指向同一个位置。

**按 drop flag 析构** `dropIf x`（后来加入，对应编译器在“可能已移走”的变量上插入的
`if (flag) drop(x)`）：静态上 `x` 无论处于哪种状态都变成 `no`，要求 `x` 没有被锁定；
动态上就是 `Ownership.Branch` 作用域结束时用的 `dropOne`，flag 为真才释放。这样之后可以给 `x` 重新赋值。
-/

namespace Core.Projection.CallArg
open Core.Ownership.Branch (Own SEnv St allocOp freeOp dropAll dropAll_sound dropOne dropOne_sound)
open Core.Calls.Modes (Mode Arg eff recheck)
open Core.Calls.NArgs (checkCallN callN_sound afterAll afterAll_other capture effAll recheckAll
  execCallN)
open Core.Projection.Lock (Cmd Locks St4 check1 exec1 step1 Good good_empty locked active
  not_locked active_mem)

inductive Cmd2
  | c      (c : Cmd)
  | call   (args : List Arg) (prs : List Var)
  | dropIf (x : Var)

/-- 被锁定的源对象只能以 `read` 传入；传入的投影必须还活着。 -/
def callOk (ps : Locks) (args : List Arg) (prs : List Var) : Bool :=
  args.all (fun a => decide (a.m = .read) || !locked ps a.x) && prs.all (fun p => active ps p)

/-! ## 静态检查 -/

def check2 (N : Nat) (σ : SEnv) (ps : Locks) : Cmd2 → Option (SEnv × Locks)
  | .c c => check1 N σ ps c
  | .call args prs =>
    if callOk ps args prs = true then
      match checkCallN σ args with
      | some σ' => some (σ', ps)
      | none    => none
    else none
  | .dropIf x => if locked ps x = false then some (upd σ x .no, ps) else none

def checkL2 (N : Nat) (σ : SEnv) (ps : Locks) : List Cmd2 → Option (SEnv × Locks)
  | []      => some (σ, ps)
  | c :: cs =>
    match check2 N σ ps c with
    | some (σ', ps') => checkL2 N σ' ps' cs
    | none           => none

/-! ## 动态语义 -/

/-- 传入的投影指向的位置是否都还活着。 -/
def prsLive (s : St4) (prs : List Var) : Bool :=
  prs.all (fun p => match s.pr p with
    | some l => s.b.live l
    | none   => false)

def exec2 (s : St4) : Cmd2 → Option St4
  | .c c => exec1 s c
  | .call args prs =>
    if prsLive s prs = true then
      match execCallN s.b args with
      | some b' => if prsLive ⟨b', s.pr⟩ prs = true then some ⟨b', s.pr⟩ else none
      | none    => none
    else none
  | .dropIf x =>
    match dropOne x s.b with
    | some b' => some ⟨b', s.pr⟩
    | none    => none

def execL2 (s : St4) : List Cmd2 → Option St4
  | []      => some s
  | c :: cs =>
    match exec2 s c with
    | some s' => execL2 s' cs
    | none    => none

/-! ## 调用的框架引理：只读或未出现的变量，指针不变 -/

theorem eff_env {m : Mode} {x : Var} {l : Loc} {s s' : St} (he : eff m x l s = some s') :
    (m = .read → s' = s) ∧ ∀ y, y ≠ x → s'.env y = s.env y := by
  unfold eff at he
  split at he
  · cases m with
    | read =>
      simp at he
      subst he
      exact ⟨fun _ => rfl, fun _ _ => rfl⟩
    | inout =>
      simp at he
      subst he
      refine ⟨(fun h => by cases h), ?_⟩
      intro y hy
      simp [allocOp, freeOp, upd, hy]
    | sink =>
      simp at he
      subst he
      exact ⟨(fun h => by cases h), fun _ _ => rfl⟩
  · contradiction

theorem effAll_env (cs : List (Arg × Loc)) : ∀ (s s' : St) (z : Var),
    (∀ p ∈ cs, p.1.x = z → p.1.m = .read) → effAll cs s = some s' → s'.env z = s.env z := by
  induction cs with
  | nil =>
    intro s s' z _ he
    simp [effAll] at he
    subst he
    rfl
  | cons p ps ih =>
    intro s s' z hz he
    obtain ⟨a, l⟩ := p
    simp only [effAll] at he
    split at he
    · rename_i s₁ h₁
      rw [ih s₁ s' z (fun q hq => hz q (by simp [hq])) he]
      obtain ⟨hr, hf⟩ := eff_env h₁
      by_cases hza : a.x = z
      · rw [hr (hz (a, l) (by simp) hza)]
      · exact hf z (fun h => hza h.symm)
    · contradiction

theorem recheckAll_eq (cs : List (Arg × Loc)) :
    ∀ (s s' : St), recheckAll cs s = some s' → s' = s := by
  induction cs with
  | nil =>
    intro s s' h
    simp [recheckAll] at h
    exact h.symm
  | cons p ps ih =>
    intro s s' h
    obtain ⟨a, l⟩ := p
    simp only [recheckAll] at h
    split at h
    · rename_i s₁ h₁
      have e1 : s₁ = s := by
        unfold recheck at h₁
        split at h₁
        · split at h₁
          · simp at h₁; exact h₁.symm
          · contradiction
        · simp at h₁; exact h₁.symm
      rw [ih s₁ s' h, e1]
    · contradiction

theorem capture_mem {s : St} : ∀ {args : List Arg} {cs : List (Arg × Loc)},
    capture s args = some cs → ∀ p ∈ cs, p.1 ∈ args := by
  intro args
  induction args with
  | nil =>
    intro cs h p hp
    simp [capture] at h
    subst h
    cases hp
  | cons a as ih =>
    intro cs h p hp
    simp only [capture] at h
    split at h
    · rename_i l cs' hl hc
      cases h
      rcases List.mem_cons.mp hp with rfl | hp'
      · simp
      · simp [ih hc p hp']
    · contradiction

theorem execCallN_env {b b' : St} {args : List Arg} {z : Var}
    (he : execCallN b args = some b') (hz : ∀ a ∈ args, a.x = z → a.m = .read) :
    b'.env z = b.env z := by
  unfold execCallN at he
  split at he
  · rename_i cs hcap
    split at he
    · rename_i s₁ h₁
      rw [recheckAll_eq cs s₁ b' he]
      exact effAll_env cs b s₁ z (fun p hp hpz => hz p.1 (capture_mem hcap p hp) hpz) h₁
    · contradiction
  · contradiction

/-! ## 单步 -/

theorem callOk_spec {ps : Locks} {args : List Arg} {prs : List Var}
    (h : callOk ps args prs = true) :
    (∀ a ∈ args, a.m = .read ∨ locked ps a.x = false) ∧ (∀ p ∈ prs, active ps p = true) := by
  unfold callOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a ha => ?_, h2⟩
  have := h1 a ha
  simpa using this

theorem prsLive_ok {N : Nat} {σ : SEnv} {ps : Locks} {s : St4} {prs : List Var}
    (hg : Good N σ ps s) (ha : ∀ p ∈ prs, active ps p = true) : prsLive s prs = true := by
  unfold prsLive
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨z, hm⟩ := active_mem (ha p hp)
  obtain ⟨hz, hpz⟩ := hg.pinv p z hm
  obtain ⟨l, hl, hlive⟩ := hg.dinv.owned_live z (hg.compat.yes z hz)
  simp [hpz, hl, hlive]

/-- `dropOne` 不改指针（只改 `live` 和 drop flag）。 -/
theorem dropOne_env {x : Var} {s s' : St} (h : dropOne x s = some s') : s'.env = s.env := by
  unfold dropOne at h
  split at h
  · split at h
    · split at h
      · cases h; rfl
      · contradiction
    · contradiction
  · cases h; rfl

theorem step2 {N : Nat} {σ σ' : SEnv} {ps ps' : Locks} {s : St4} {c : Cmd2}
    (hc : check2 N σ ps c = some (σ', ps')) (hg : Good N σ ps s) :
    ∃ s', exec2 s c = some s' ∧ Good N σ' ps' s' := by
  cases c with
  | c c =>
    simp only [check2] at hc
    obtain ⟨s', he, hg'⟩ := step1 hc hg
    exact ⟨s', by simp only [exec2, he], hg'⟩
  | call args prs =>
    simp only [check2] at hc
    split at hc
    · rename_i hok
      split at hc
      · rename_i σ₁ hcc
        cases hc
        obtain ⟨hargs, hprs⟩ := callOk_spec hok
        have hσ₁ : σ' = afterAll args σ := by
          simp only [checkCallN] at hcc
          split at hcc
          · cases hcc; rfl
          · contradiction
        obtain ⟨b', he, hc', hd'⟩ := callN_sound hcc hg.compat hg.dinv
        -- 被锁定的源对象只以 `read` 出现
        have hrd : ∀ p z, (p, z) ∈ ps → ∀ a ∈ args, a.x = z → a.m = .read := by
          intro p z hm a ha haz
          rcases hargs a ha with h | h
          · exact h
          · exact absurd haz.symm (not_locked h hm)
        have hg' : Good N σ' ps ⟨b', s.pr⟩ := by
          refine ⟨hc', hd', ?_⟩
          intro p z hm
          obtain ⟨hz, hpz⟩ := hg.pinv p z hm
          refine ⟨?_, ?_⟩
          · have hns : ∀ a ∈ args, a.m = .sink → a.x ≠ z := by
              intro a ha has haz
              rw [hrd p z hm a ha haz] at has
              cases has
            rw [hσ₁, afterAll_other args σ z hns]
            exact hz
          · show s.pr p = b'.env z
            rw [execCallN_env he (hrd p z hm)]
            exact hpz
        refine ⟨⟨b', s.pr⟩, ?_, hg'⟩
        simp [exec2, prsLive_ok hg hprs, he, prsLive_ok hg' hprs]
      · contradiction
    · contradiction
  | dropIf x =>
    simp only [check2] at hc
    split at hc
    · rename_i hnl
      cases hc
      obtain ⟨b', he, hd', hfx, hrest⟩ := dropOne_sound x hg.dinv
      refine ⟨⟨b', s.pr⟩, by simp only [exec2, he], ⟨?_, hd', ?_⟩⟩
      · constructor
        · intro z hz
          by_cases hzx : z = x
          · rw [hzx] at hz
            simp [upd] at hz
          · rw [upd_other _ _ hzx] at hz
            rw [hrest z hzx]
            exact hg.compat.yes z hz
        · intro z hz
          by_cases hzx : z = x
          · rw [hzx]
            exact hfx
          · rw [upd_other _ _ hzx] at hz
            rw [hrest z hzx]
            exact hg.compat.no z hz
      · intro p z hm
        obtain ⟨hz, hpz⟩ := hg.pinv p z hm
        have hzx : z ≠ x := not_locked hnl hm
        refine ⟨by rw [upd_other _ _ hzx]; exact hz, ?_⟩
        show s.pr p = b'.env z
        rw [dropOne_env he]
        exact hpz
    · contradiction

theorem listSound2 (N : Nat) (cs : List Cmd2) :
    ∀ {σ σ' : SEnv} {ps ps' : Locks} {s : St4},
      checkL2 N σ ps cs = some (σ', ps') → Good N σ ps s →
      ∃ s', execL2 s cs = some s' ∧ Good N σ' ps' s' := by
  induction cs with
  | nil =>
    intro σ σ' ps ps' s hc hg
    simp only [checkL2] at hc
    cases hc
    exact ⟨s, rfl, hg⟩
  | cons c cs ih =>
    intro σ σ' ps ps' s hc hg
    simp only [checkL2] at hc
    split at hc
    · rename_i σ₁ ps₁ h₁
      obtain ⟨s₁, he₁, hg₁⟩ := step2 h₁ hg
      obtain ⟨s₂, he₂, hg₂⟩ := ih hc hg₁
      exact ⟨s₂, by simp only [execL2, he₁, he₂], hg₂⟩
    · contradiction

/-! ## 主定理 -/

/-- **`Projection.CallArg` 主定理。** 检查器接受的程序执行不出错：调用开始和结束时，
传入的投影都指向活着的位置；作用域结束时按 drop flag 释放，之后堆上没有活着的值。 -/
theorem safety_and_no_leak (N : Nat) (cs : List Cmd2) (σ' : SEnv) (ps' : Locks)
    (h : checkL2 N (fun _ => .no) [] cs = some (σ', ps')) :
    ∃ b, (execL2 St4.empty cs).bind (fun s => dropAll s.b N) = some b ∧
      ∀ l, b.live l = false := by
  obtain ⟨s₁, he₁, hg₁⟩ := listSound2 N cs h (good_empty N)
  obtain ⟨b₂, he₂, hd₂, hf₂⟩ := dropAll_sound hg₁.dinv N
  refine ⟨b₂, by rw [he₁]; exact he₂, ?_⟩
  intro l
  cases hl : b₂.live l with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨x, hx, _⟩ := hd₂.live_owned l hl
    have hxN := hd₂.bound x hx
    rw [hf₂ x hxN] at hx
    contradiction

/-! ## 例子（投影名用 5） -/

/-- `let p = proj v.0; f(read v, p); read p`：源对象和投影同时以只读方式传入，接受。 -/
def ok1 : List Cmd2 :=
  [.c (.base (.alloc 0)), .c (.proj 5 0), .call [⟨.read, 0⟩] [5],
   .c (.readp 5), .c (.endp 5), .c (.base (.free 0))]
example : (checkL2 2 (fun _ => .no) [] ok1).isSome = true := rfl

/-- 把投影和另一个变量的 `inout` 一起传入：接受。 -/
def ok2 : List Cmd2 :=
  [.c (.base (.alloc 0)), .c (.base (.alloc 1)), .c (.proj 5 0),
   .call [⟨.inout, 1⟩] [5], .c (.readp 5), .c (.endp 5)]
example : (checkL2 2 (fun _ => .no) [] ok2).isSome = true := rfl

/-- 投影还在时把源对象以 `inout` 传入：拒绝。 -/
def bad1 : List Cmd2 :=
  [.c (.base (.alloc 0)), .c (.proj 5 0), .call [⟨.inout, 0⟩] [5]]
example : (checkL2 2 (fun _ => .no) [] bad1).isNone = true := rfl

/-- 不经检查直接执行 `bad1`：被调函数换掉了源对象的值，投影悬空，执行出错。 -/
example : (execL2 St4.empty bad1).isNone = true := rfl

/-- 投影还在时把源对象 `sink` 进去：拒绝。 -/
def bad2 : List Cmd2 :=
  [.c (.base (.alloc 0)), .c (.proj 5 0), .call [⟨.sink, 0⟩] []]
example : (checkL2 2 (fun _ => .no) [] bad2).isNone = true := rfl

/-- 传入已经结束的投影：拒绝。 -/
def bad3 : List Cmd2 :=
  [.c (.base (.alloc 0)), .c (.proj 5 0), .c (.endp 5), .call [] [5]]
example : (checkL2 2 (fun _ => .no) [] bad3).isNone = true := rfl

/-- 只在一个分支里移走之后，按 flag 析构，再重新赋值：接受（静态状态 `maybe` 由 `dropIf` 变成 `no`）。 -/
def ok3 : List Cmd2 := [.dropIf 0, .c (.base (.alloc 0)), .dropIf 0, .c (.base (.alloc 0))]
example : (checkL2 2 (fun _ => .maybe) [] ok3).isSome = true := rfl

/-- 投影还在时按 flag 析构源对象：拒绝。 -/
def bad4 : List Cmd2 := [.c (.base (.alloc 0)), .c (.proj 5 0), .dropIf 0]
example : (checkL2 2 (fun _ => .no) [] bad4).isNone = true := rfl

end Core.Projection.CallArg

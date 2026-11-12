import Core.Projection.CallArg

/-!
# 返回借用的调用

`Projection.CallArg` 里投影只能传进函数，调用不返回指针。这里加入返回借用的调用，
对应签名 `fn get(v: Vec<T>, i: I64) -> &T in v`：返回值借用参数 `v`（以 `read` 传入的拥有者），
或者借用一个传入的投影（`fn trim(s: &str in a) -> &str in a`）。

- `callOwn p args prs z`：调用之后 `p` 指向 `z` 的值，`p` 锁住 `z`，和 `proj p z` 一样。
  要求 `z` 在 `args` 里、并且只以 `read` 出现（编译器只允许返回借用 let 参数的函数）。
- `callBor p args prs q`：调用之后 `p` 和传入的投影 `q` 指向同一个位置，`p` 锁住 `q` 的源对象。
  `q` 之后结束不影响 `p`：`p` 在锁表里有自己的一项。

被调函数这一边由签名保证：返回类型是 `&T in m` 时，返回的只能是 `m` 里面的位置。
所以调用者这一边的语义就是“调用，然后从 `z`（或 `q`）建一个投影”，借用从调用返回时开始，
调用期间 `z` 照常以 `read` 传入。

**主定理** `safety_and_no_leak`：检查器接受的程序执行不出错（包括通过返回的借用读取时，
指向的位置都还活着），作用域结束后没有泄漏。

证明沿用 `Projection.Lock` 的不变式 `Good`：`callOwn` 是 `step2`（调用）接着 `step1`（投影）；
`callBor` 的新的一项 `(p, z)` 由 `q` 的那一项 `(q, z)` 得到。
-/

namespace Core.Projection.Return
open Core.Ownership.Branch (SEnv dropAll dropAll_sound)
open Core.Calls.Modes (Arg)
open Core.Projection.Lock (Cmd Locks St4 check1 exec1 step1 Good good_empty active not_active)
open Core.Projection.CallArg (Cmd2 check2 exec2 step2)

inductive Cmd3
  | c       (c : Cmd2)
  | callOwn (p : Var) (args : List Arg) (prs : List Var) (z : Var)
  | callBor (p : Var) (args : List Arg) (prs : List Var) (q : Var)

/-- `z` 作为参数传入，并且只以 `read` 出现。 -/
def passedRead (args : List Arg) (z : Var) : Bool :=
  args.any (fun a => a.x == z) && args.all (fun a => a.x != z || decide (a.m = .read))

/-- 投影 `q` 锁住的源对象（锁表里 `q` 的第一项）。 -/
def srcOf : Locks → Var → Option Var
  | [], _ => none
  | (p, z) :: ps, q => if p = q then some z else srcOf ps q

theorem srcOf_mem : ∀ {ps : Locks} {q z : Var}, srcOf ps q = some z → (q, z) ∈ ps := by
  intro ps
  induction ps with
  | nil => intro q z h; simp [srcOf] at h
  | cons e ps ih =>
    intro q z h
    obtain ⟨p, w⟩ := e
    simp only [srcOf] at h
    split at h
    · rename_i hpq
      cases h
      subst hpq
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-! ## 静态检查 -/

def check3 (N : Nat) (σ : SEnv) (ps : Locks) : Cmd3 → Option (SEnv × Locks)
  | .c c => check2 N σ ps c
  | .callOwn p args prs z =>
    if passedRead args z = true then
      match check2 N σ ps (.call args prs) with
      | some (σ₁, ps₁) => check1 N σ₁ ps₁ (.proj p z)
      | none           => none
    else none
  | .callBor p args prs q =>
    match check2 N σ ps (.call args prs) with
    | some (σ₁, ps₁) =>
      if q ∈ prs ∧ active ps₁ p = false then
        match srcOf ps₁ q with
        | some z => some (σ₁, (p, z) :: ps₁)
        | none   => none
      else none
    | none => none

def checkL3 (N : Nat) (σ : SEnv) (ps : Locks) : List Cmd3 → Option (SEnv × Locks)
  | []      => some (σ, ps)
  | c :: cs =>
    match check3 N σ ps c with
    | some (σ', ps') => checkL3 N σ' ps' cs
    | none           => none

/-! ## 动态语义：返回的借用是裸指针，指向 `z` 的值或 `q` 指向的位置 -/

def exec3 (s : St4) : Cmd3 → Option St4
  | .c c => exec2 s c
  | .callOwn p args prs z =>
    match exec2 s (.call args prs) with
    | some s₁ => exec1 s₁ (.proj p z)
    | none    => none
  | .callBor p args prs q =>
    match exec2 s (.call args prs) with
    | some s₁ =>
      match s₁.pr q with
      | some l => if s₁.b.live l = true then some ⟨s₁.b, upd s₁.pr p (some l)⟩ else none
      | none   => none
    | none => none

def execL3 (s : St4) : List Cmd3 → Option St4
  | []      => some s
  | c :: cs =>
    match exec3 s c with
    | some s' => execL3 s' cs
    | none    => none

/-! ## 单步 -/

theorem step3 {N : Nat} {σ σ' : SEnv} {ps ps' : Locks} {s : St4} {c : Cmd3}
    (hc : check3 N σ ps c = some (σ', ps')) (hg : Good N σ ps s) :
    ∃ s', exec3 s c = some s' ∧ Good N σ' ps' s' := by
  cases c with
  | c c =>
    simp only [check3] at hc
    obtain ⟨s', he, hg'⟩ := step2 hc hg
    exact ⟨s', by simp only [exec3, he], hg'⟩
  | callOwn p args prs z =>
    simp only [check3] at hc
    split at hc
    · split at hc
      · rename_i σ₁ ps₁ h₁
        obtain ⟨s₁, he₁, hg₁⟩ := step2 h₁ hg
        obtain ⟨s₂, he₂, hg₂⟩ := step1 hc hg₁
        exact ⟨s₂, by simp only [exec3, he₁, he₂], hg₂⟩
      · contradiction
    · contradiction
  | callBor p args prs q =>
    simp only [check3] at hc
    split at hc
    · rename_i σ₁ ps₁ h₁
      split at hc
      · rename_i hcond
        obtain ⟨_, hpa⟩ := hcond
        split at hc
        · rename_i z hz
          cases hc
          obtain ⟨s₁, he₁, hg₁⟩ := step2 h₁ hg
          obtain ⟨hzy, hqz⟩ := hg₁.pinv q z (srcOf_mem hz)
          obtain ⟨l, hl, hlive⟩ := hg₁.dinv.owned_live z (hg₁.compat.yes z hzy)
          refine ⟨⟨s₁.b, upd s₁.pr p (some l)⟩, ?_, ⟨hg₁.compat, hg₁.dinv, ?_⟩⟩
          · simp [exec3, he₁, hqz, hl, hlive]
          · intro r w hm
            rcases List.mem_cons.mp hm with h | h
            · simp only [Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨hzy, by simp [hl]⟩
            · obtain ⟨hw, hrw⟩ := hg₁.pinv r w h
              have hrp : r ≠ p := not_active hpa h
              exact ⟨hw, by simp [upd, hrp, hrw]⟩
        · contradiction
      · contradiction
    · contradiction

theorem listSound3 (N : Nat) (cs : List Cmd3) :
    ∀ {σ σ' : SEnv} {ps ps' : Locks} {s : St4},
      checkL3 N σ ps cs = some (σ', ps') → Good N σ ps s →
      ∃ s', execL3 s cs = some s' ∧ Good N σ' ps' s' := by
  induction cs with
  | nil =>
    intro σ σ' ps ps' s hc hg
    simp only [checkL3] at hc
    cases hc
    exact ⟨s, rfl, hg⟩
  | cons c cs ih =>
    intro σ σ' ps ps' s hc hg
    simp only [checkL3] at hc
    split at hc
    · rename_i σ₁ ps₁ h₁
      obtain ⟨s₁, he₁, hg₁⟩ := step3 h₁ hg
      obtain ⟨s₂, he₂, hg₂⟩ := ih hc hg₁
      exact ⟨s₂, by simp only [execL3, he₁, he₂], hg₂⟩
    · contradiction

/-! ## 主定理 -/

/-- **`Projection.Return` 主定理。** 检查器接受的程序执行不出错：通过调用返回的借用读取时，
指向的位置都还活着；作用域结束时按 drop flag 释放，之后堆上没有活着的值。 -/
theorem safety_and_no_leak (N : Nat) (cs : List Cmd3) (σ' : SEnv) (ps' : Locks)
    (h : checkL3 N (fun _ => .no) [] cs = some (σ', ps')) :
    ∃ b, (execL3 St4.empty cs).bind (fun s => dropAll s.b N) = some b ∧
      ∀ l, b.live l = false := by
  obtain ⟨s₁, he₁, hg₁⟩ := listSound3 N cs h (good_empty N)
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

/-! ## 例子（投影和返回的借用用 5、6） -/

/-- `let p = v.get(0); read p; (p 结束); free v`：接受。 -/
def ok1 : List Cmd3 :=
  [.c (.c (.base (.alloc 0))), .callOwn 5 [⟨.read, 0⟩] [] 0, .c (.c (.readp 5)),
   .c (.c (.endp 5)), .c (.c (.base (.free 0)))]
example : (checkL3 2 (fun _ => .no) [] ok1).isSome = true := rfl

/-- 借用还在时只读使用源对象、再传给只读参数：接受。 -/
def ok2 : List Cmd3 :=
  [.c (.c (.base (.alloc 0))), .callOwn 5 [⟨.read, 0⟩] [] 0, .c (.c (.base (.use 0))),
   .c (.call [⟨.read, 0⟩] [5]), .c (.c (.readp 5)), .c (.c (.endp 5)), .c (.c (.base (.move 0 1)))]
example : (checkL3 2 (fun _ => .no) [] ok2).isSome = true := rfl

/-- 借用的借用：`let q = proj v; let p = q.trim(); (q 结束); read p`：接受，`p` 比 `q` 活得长。 -/
def ok3 : List Cmd3 :=
  [.c (.c (.base (.alloc 0))), .c (.c (.proj 5 0)), .callBor 6 [] [5] 5, .c (.c (.endp 5)),
   .c (.c (.readp 6)), .c (.c (.endp 6)), .c (.c (.base (.free 0)))]
example : (checkL3 2 (fun _ => .no) [] ok3).isSome = true := rfl

/-- 借用还在时释放源对象：拒绝。 -/
def bad1 : List Cmd3 :=
  [.c (.c (.base (.alloc 0))), .callOwn 5 [⟨.read, 0⟩] [] 0, .c (.c (.base (.free 0))),
   .c (.c (.readp 5))]
example : (checkL3 2 (fun _ => .no) [] bad1).isNone = true := rfl

/-- 不经检查直接执行 `bad1`：通过返回的借用读到了已释放的内存，执行出错。 -/
example : (execL3 St4.empty bad1).isNone = true := rfl

/-- 借用还在时把源对象 `inout` 传给别的函数：拒绝。 -/
def bad2 : List Cmd3 :=
  [.c (.c (.base (.alloc 0))), .callOwn 5 [⟨.read, 0⟩] [] 0, .c (.call [⟨.inout, 0⟩] [])]
example : (checkL3 2 (fun _ => .no) [] bad2).isNone = true := rfl

/-- 返回借用 `inout` 参数的函数：拒绝（只能借用以 `read` 传入的参数）。 -/
def bad3 : List Cmd3 := [.c (.c (.base (.alloc 0))), .callOwn 5 [⟨.inout, 0⟩] [] 0]
example : (checkL3 2 (fun _ => .no) [] bad3).isNone = true := rfl

/-- 借用的借用：`q` 结束之后源对象仍被 `p` 锁住，释放它：拒绝。 -/
def bad4 : List Cmd3 :=
  [.c (.c (.base (.alloc 0))), .c (.c (.proj 5 0)), .callBor 6 [] [5] 5, .c (.c (.endp 5)),
   .c (.c (.base (.free 0))), .c (.c (.readp 6))]
example : (checkL3 2 (fun _ => .no) [] bad4).isNone = true := rfl

/-- 返回借用的投影没有传进去：拒绝。 -/
def bad5 : List Cmd3 :=
  [.c (.c (.base (.alloc 0))), .c (.c (.proj 5 0)), .callBor 6 [] [] 5]
example : (checkL3 2 (fun _ => .no) [] bad5).isNone = true := rfl

end Core.Projection.Return

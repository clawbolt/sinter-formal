import Core.Ownership.Loop
import Core.Projection.Liveness

/-!
# 投影与分支、循环

把 `Projection.Lock` 的命令放进 `Ownership.Loop` 的结构化程序里：顺序、分支、循环。结束点 `endp` 在这一轮仍然显式写出。

**锁表在汇合点怎么合并**（`joinL`）：取两边的交集，并且只保留两边源对象都确定拥有值的项。
- 只在一边还活着的投影，汇合之后不再算活着：后面不能再读它，也不再锁它的源对象。
  这是健全的，因为锁只是为了保护“还能被读的投影”。
- 不取并集：如果取并集，走了另一边时运行时的投影指针可能早已不指向源对象。

**循环**沿用 `Ownership.Loop` 的两轮不动点。循环头的锁表 `πh := joinL σ σb ps pb`；
从循环头再检查一遍循环体得到 `p2`，要求 `πh ⊆ p2`（`subL`）。
也就是说，循环体跑完一轮后，循环头要求还活着的投影仍然活着。

**主定理** `safety_and_no_leak`：检查器接受的程序，无论燃料多少、分支怎么走、循环跑几轮，
执行都不会出现内存错误（包括通过投影读到已释放的内存）；正常结束时按 drop flag 释放不出错，
并且堆上没有活着的值。
-/

namespace Core.Projection.Branches
open Core.Ownership.Move (Stmt)
open Core.Ownership.Branch (Own SEnv join dropAll dropAll_sound)
open Core.Ownership.Loop (Bounded bounded_empty bounded_join bounded_checkS Le compat_le
  le_join_left le_join_right leN leN_sound join_of_le)
open Core.Projection.Lock (Cmd Locks St4 check1 exec1 step1 Good good_empty)

inductive P
  | skip
  | cmd    (c : Cmd)
  | seq    (p q : P)
  | branch (p q : P)
  | loop   (b : P)

/-- 汇合点的锁表：两边都有、并且两边源对象都确定拥有值的项。 -/
def joinL (σa σb : SEnv) (pa pb : Locks) : Locks :=
  pa.filter (fun e => decide (e ∈ pb) && decide (σa e.2 = .yes) && decide (σb e.2 = .yes))

def subL (qs ps : Locks) : Bool := qs.all (fun e => decide (e ∈ ps))

/-! ## 静态检查 -/

def check (N : Nat) : P → SEnv → Locks → Option (SEnv × Locks)
  | .skip,       σ, ps => some (σ, ps)
  | .cmd c,      σ, ps => check1 N σ ps c
  | .seq p q,    σ, ps =>
    match check N p σ ps with
    | some (σ₁, ps₁) => check N q σ₁ ps₁
    | none           => none
  | .branch p q, σ, ps =>
    match check N p σ ps, check N q σ ps with
    | some (σa, pa), some (σb, pb) => some (join σa σb, joinL σa σb pa pb)
    | _, _                         => none
  | .loop b,     σ, ps =>
    match check N b σ ps with
    | none          => none
    | some (σb, pb) =>
      match check N b (join σ σb) (joinL σ σb ps pb) with
      | none          => none
      | some (σ2, p2) =>
        if leN N σ2 (join σ σb) = true ∧ subL (joinL σ σb ps pb) p2 = true then
          some (join σ σb, joinL σ σb ps pb)
        else none

/-! ## 动态语义 -/

inductive Res
  | ok  (s : St4) (cs : List Bool)
  | err
  | oof

def exec : Nat → P → St4 → List Bool → Res
  | 0,     _,            _, _  => .oof
  | _ + 1, .skip,        s, cs => .ok s cs
  | _ + 1, .cmd c,       s, cs =>
    match exec1 s c with
    | some s' => .ok s' cs
    | none    => .err
  | n + 1, .seq p q,     s, cs =>
    match exec n p s cs with
    | .ok s₁ cs₁ => exec n q s₁ cs₁
    | .err       => .err
    | .oof       => .oof
  | n + 1, .branch p q,  s, cs =>
    if cs.headD false = true then exec n p s cs.tail else exec n q s cs.tail
  | n + 1, .loop b,      s, cs =>
    if cs.headD false = true then
      match exec n b s cs.tail with
      | .ok s₁ cs₁ => exec n (.loop b) s₁ cs₁
      | .err       => .err
      | .oof       => .oof
    else .ok s cs.tail

def GoodR (N : Nat) (σ : SEnv) (ps : Locks) : Res → Prop
  | .ok s _ => Good N σ ps s
  | .err    => False
  | .oof    => True

/-! ## 锁表合并的引理 -/

theorem filter_all {α : Type} (f : α → Bool) (l : List α)
    (h : ∀ a ∈ l, f a = true) : l.filter f = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : f a = true := h a (by simp)
    have hl : l.filter f = l := ih (fun b hb => h b (by simp [hb]))
    simp [ha, hl]

theorem joinL_mem {σa σb : SEnv} {pa pb : Locks} {e : Var × Var}
    (h : e ∈ joinL σa σb pa pb) :
    e ∈ pa ∧ e ∈ pb ∧ σa e.2 = .yes ∧ σb e.2 = .yes := by
  unfold joinL at h
  obtain ⟨hm, hc⟩ := List.mem_filter.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hb, hya⟩, hyb⟩ := hc
  exact ⟨hm, hb, hya, hyb⟩

theorem join_yes {σa σb : SEnv} {z : Var} (ha : σa z = .yes) (hb : σb z = .yes) :
    join σa σb z = .yes := by
  simp [join, ha, hb]

theorem joinL_self {σa σb : SEnv} {ps qs : Locks}
    (hsub : ∀ e ∈ ps, e ∈ qs) (ha : ∀ e ∈ ps, σa e.2 = .yes) (hb : ∀ e ∈ ps, σb e.2 = .yes) :
    joinL σa σb ps qs = ps := by
  unfold joinL
  exact filter_all _ ps (fun e he => by simp [hsub e he, ha e he, hb e he])

theorem subL_sound {qs ps : Locks} (h : subL qs ps = true) : ∀ e ∈ qs, e ∈ ps := by
  intro e he
  have := List.all_eq_true.mp h e he
  simpa using this

/-- 弱化：静态状态变弱、锁表变小，`Good` 仍然成立。 -/
theorem good_weak {N : Nat} {σ τ : SEnv} {ps qs : Locks} {s : St4}
    (hle : Le σ τ) (hsub : ∀ e ∈ qs, e ∈ ps) (hy : ∀ e ∈ qs, τ e.2 = .yes)
    (hg : Good N σ ps s) : Good N τ qs s :=
  ⟨compat_le hle hg.compat, hg.dinv,
    fun p z hm => ⟨hy _ hm, (hg.pinv p z (hsub _ hm)).2⟩⟩

theorem goodR_weak {N : Nat} {σ τ : SEnv} {ps qs : Locks} {r : Res}
    (hle : Le σ τ) (hsub : ∀ e ∈ qs, e ∈ ps) (hy : ∀ e ∈ qs, τ e.2 = .yes) :
    GoodR N σ ps r → GoodR N τ qs r := by
  cases r with
  | ok s cs =>
    intro g
    simp only [GoodR] at g ⊢
    exact good_weak hle hsub hy g
  | err => intro g; simp [GoodR] at g
  | oof => intro _; simp [GoodR]

/-! ## 静态不变式 `Bounded` -/

theorem bounded_check1 {N : Nat} {σ σ' : SEnv} {ps ps' : Locks} {c : Cmd}
    (hc : check1 N σ ps c = some (σ', ps')) (hb : Bounded N σ) : Bounded N σ' := by
  cases c with
  | base t =>
    simp only [check1] at hc
    split at hc
    · split at hc
      · rename_i σ₁ h₁
        cases hc
        simp only [Core.Ownership.Branch.checkStmtV] at h₁
        split at h₁
        · rename_i hv
          exact bounded_checkS hv h₁ hb
        · contradiction
      · contradiction
    · contradiction
  | proj p x =>
    simp only [check1] at hc
    split at hc
    · cases hc; exact hb
    · contradiction
  | readp p =>
    simp only [check1] at hc
    split at hc
    · cases hc; exact hb
    · contradiction
  | endp p =>
    simp only [check1] at hc
    split at hc
    · cases hc; exact hb
    · contradiction

theorem bounded_check (N : Nat) (p : P) :
    ∀ {σ σ' : SEnv} {ps ps' : Locks},
      check N p σ ps = some (σ', ps') → Bounded N σ → Bounded N σ' := by
  induction p with
  | skip =>
    intro σ σ' ps ps' hc hb
    simp only [check] at hc
    cases hc
    exact hb
  | cmd c =>
    intro σ σ' ps ps' hc hb
    exact bounded_check1 hc hb
  | seq p q ihp ihq =>
    intro σ σ' ps ps' hc hb
    simp only [check] at hc
    split at hc
    · rename_i σ₁ ps₁ h₁
      exact ihq hc (ihp h₁ hb)
    · contradiction
  | branch p q ihp ihq =>
    intro σ σ' ps ps' hc hb
    simp only [check] at hc
    split at hc
    · rename_i σa pa σb pb hpa hpb
      cases hc
      exact bounded_join (ihp hpa hb) (ihq hpb hb)
    · contradiction
  | loop b ih =>
    intro σ σ' ps ps' hc hb
    simp only [check] at hc
    split at hc
    · contradiction
    · rename_i σb pb hσb
      split at hc
      · contradiction
      · split at hc
        · cases hc
          exact bounded_join hb (ih hσb hb)
        · contradiction

/-! ## 主引理 -/

theorem sound (N : Nat) (n : Nat) :
    ∀ (p : P) {σ σ' : SEnv} {ps ps' : Locks} {s : St4} (cs : List Bool),
      check N p σ ps = some (σ', ps') → Bounded N σ → Good N σ ps s →
      GoodR N σ' ps' (exec n p s cs) := by
  induction n with
  | zero =>
    intro p σ σ' ps ps' s cs _ _ _
    simp [exec, GoodR]
  | succ n ih =>
    intro p σ σ' ps ps' s cs hc hb hg
    cases p with
    | skip =>
      simp only [check] at hc
      cases hc
      simp only [exec, GoodR]
      exact hg
    | cmd c =>
      simp only [check] at hc
      obtain ⟨s', he, hg'⟩ := step1 hc hg
      simp only [exec, he, GoodR]
      exact hg'
    | seq p q =>
      simp only [check] at hc
      split at hc
      · rename_i σ₁ ps₁ h₁
        have hb₁ := bounded_check N p h₁ hb
        have g₁ := ih p cs h₁ hb hg
        cases he₁ : exec n p s cs with
        | ok s₁ cs₁ =>
          rw [he₁] at g₁
          simp only [GoodR] at g₁
          simp only [exec, he₁]
          exact ih q cs₁ hc hb₁ g₁
        | err => rw [he₁] at g₁; simp [GoodR] at g₁
        | oof => simp only [exec, he₁, GoodR]
      · contradiction
    | branch p q =>
      simp only [check] at hc
      split at hc
      · rename_i σa pa σb pb hpa hpb
        cases hc
        by_cases hcs : cs.headD false = true
        · have g := ih p cs.tail hpa hb hg
          simp only [exec, hcs, ite_true]
          exact goodR_weak le_join_left (fun e he => (joinL_mem he).1)
            (fun e he => join_yes (joinL_mem he).2.2.1 (joinL_mem he).2.2.2) g
        · have g := ih q cs.tail hpb hb hg
          simp only [exec, hcs]
          simp only [ite_false, Bool.false_eq_true] at *
          exact goodR_weak le_join_right (fun e he => (joinL_mem he).2.1)
            (fun e he => join_yes (joinL_mem he).2.2.1 (joinL_mem he).2.2.2) g
      · contradiction
    | loop b =>
      simp only [check] at hc
      split at hc
      · contradiction
      · rename_i σb pb hσb
        split at hc
        · contradiction
        · rename_i σ2 p2 h2
          split at hc
          · rename_i hcond
            obtain ⟨hle, hsub⟩ := hcond
            cases hc
            have hbb := bounded_check N b hσb hb
            have hbτ : Bounded N (join σ σb) := bounded_join hb hbb
            have hb2 := bounded_check N b h2 hbτ
            have hLe : Le σ2 (join σ σb) := leN_sound hle hb2 hbτ
            have hsub2 := subL_sound hsub
            have hyτ : ∀ e ∈ joinL σ σb ps pb, join σ σb e.2 = .yes :=
              fun e he => join_yes (joinL_mem he).2.2.1 (joinL_mem he).2.2.2
            have hy2 : ∀ e ∈ joinL σ σb ps pb, σ2 e.2 = .yes := by
              intro e he
              have hτ := hyτ e he
              cases hLe e.2 with
              | inl h => rw [h] at hτ; exact hτ
              | inr h => rw [h] at hτ; cases hτ
            have hJ := joinL_self hsub2 hyτ hy2
            -- 循环头是检查器的不动点
            have hfix : check N (.loop b) (join σ σb) (joinL σ σb ps pb) =
                some (join σ σb, joinL σ σb ps pb) := by
              simp [check, h2, join_of_le hLe, hJ, hle, hsub]
            have hgτ : Good N (join σ σb) (joinL σ σb ps pb) s :=
              good_weak le_join_left (fun e he => (joinL_mem he).1) hyτ hg
            by_cases hcs : cs.headD false = true
            · have g := ih b cs.tail h2 hbτ hgτ
              cases he : exec n b s cs.tail with
              | ok s₁ cs₁ =>
                rw [he] at g
                simp only [GoodR] at g
                simp only [exec, hcs, ite_true, he]
                exact ih (.loop b) cs₁ hfix hbτ (good_weak hLe hsub2 hyτ g)
              | err => rw [he] at g; simp [GoodR] at g
              | oof => simp only [exec, hcs, ite_true, he, GoodR]
            · simp only [exec, hcs]
              simp only [ite_false, Bool.false_eq_true] at *
              simp only [GoodR]
              exact hgτ
          · contradiction

/-! ## 主定理 -/

/-- **`Projection.Branches` 主定理。** 检查器接受的程序，无论燃料多少、分支怎么走、循环跑几轮：
执行不会出现内存错误（包括通过投影读到已释放的内存）；如果正常结束，
按 drop flag 释放也不出错，并且堆上没有活着的值。 -/
theorem safety_and_no_leak (N : Nat) (p : P) (σ' : SEnv) (ps' : Locks)
    (h : check N p (fun _ => .no) [] = some (σ', ps')) (fuel : Nat) (cs : List Bool) :
    exec fuel p St4.empty cs ≠ .err ∧
    ∀ s cs', exec fuel p St4.empty cs = .ok s cs' →
      ∃ b, dropAll s.b N = some b ∧ ∀ l, b.live l = false := by
  have g := sound N fuel p cs h (bounded_empty N) (good_empty N)
  constructor
  · intro he
    rw [he] at g
    simp [GoodR] at g
  · intro s cs' he
    rw [he] at g
    simp only [GoodR] at g
    obtain ⟨b, hb, hd, hf⟩ := dropAll_sound g.dinv N
    refine ⟨b, hb, ?_⟩
    intro l
    cases hl : b.live l with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨x, hx, _⟩ := hd.live_owned l hl
      have hxN := hd.bound x hx
      rw [hf x hxN] at hx
      contradiction

/-! ## 例子（投影名用 5） -/

def block : List P → P
  | []      => .skip
  | p :: ps => .seq p (block ps)

def isErr : Res → Bool
  | .err => true
  | _    => false

/-- 两个分支各自结束投影，之后释放源对象：接受。 -/
def brOk : P := block
  [.cmd (.base (.alloc 0)), .cmd (.proj 5 0),
   .branch (block [.cmd (.readp 5), .cmd (.endp 5)]) (.cmd (.endp 5)),
   .cmd (.base (.free 0))]
example : (check 2 brOk (fun _ => .no) []).isSome = true := rfl

/-- 投影只在一个分支里还活着：汇合后不再算活着，后面读它被拒绝。 -/
def brBad : P := block
  [.cmd (.base (.alloc 0)), .cmd (.proj 5 0),
   .branch (.cmd (.endp 5)) .skip,
   .cmd (.readp 5)]
example : (check 2 brBad (fun _ => .no) []).isNone = true := rfl

/-- 一个分支释放了源对象，汇合后再读投影：拒绝；不经检查走这个分支，执行出错。 -/
def brFree : P := block
  [.cmd (.base (.alloc 0)), .cmd (.proj 5 0),
   .branch (block [.cmd (.endp 5), .cmd (.base (.free 0))]) .skip,
   .cmd (.readp 5)]
example : (check 2 brFree (fun _ => .no) []).isNone = true := rfl
example : isErr (exec 50 brFree St4.empty [true]) = true := rfl

/-- 每轮创建、读取、结束一个投影，循环后释放源对象：接受，跑三轮不出错。 -/
def loopOk : P := block
  [.cmd (.base (.alloc 0)),
   .loop (block [.cmd (.proj 5 0), .cmd (.readp 5), .cmd (.endp 5)]),
   .cmd (.base (.free 0))]
example : (check 2 loopOk (fun _ => .no) []).isSome = true := rfl
example : isErr (exec 50 loopOk St4.empty [true, true, true, false]) = false := rfl

/-- 投影跨越整个循环，循环后结束投影再释放：接受。 -/
def loopKeep : P := block
  [.cmd (.base (.alloc 0)), .cmd (.proj 5 0),
   .loop (.cmd (.readp 5)),
   .cmd (.endp 5), .cmd (.base (.free 0))]
example : (check 2 loopKeep (fun _ => .no) []).isSome = true := rfl

/-- 投影跨越循环但没有结束就释放源对象：拒绝。 -/
def loopBad : P := block
  [.cmd (.base (.alloc 0)), .cmd (.proj 5 0),
   .loop (.cmd (.readp 5)),
   .cmd (.base (.free 0))]
example : (check 2 loopBad (fun _ => .no) []).isNone = true := rfl

/-- 循环体在第一轮结束了投影，第二轮还要读：拒绝。 -/
def loopBad2 : P := block
  [.cmd (.base (.alloc 0)), .cmd (.proj 5 0),
   .loop (block [.cmd (.readp 5), .cmd (.endp 5)])]
example : (check 2 loopBad2 (fun _ => .no) []).isNone = true := rfl

end Core.Projection.Branches

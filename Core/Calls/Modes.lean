import Core.Ownership.Branch

/-!
# 参数约定与排他性（两参数调用）

新增一种语句 `call a b`：调用一个内建函数，两个参数各带一个约定：

* `read`：只读借用（草案里的 `let`）
* `inout`：可变借用
* `sink`：转移所有权

**被调函数的动态模型**（故意做得“危险”，让违反排他性真的出错）：

1. 调用开始时取出两个参数的指针；
2. 依次处理每个参数：`sink` 释放值；`inout` 释放并重新分配（模拟 `Vec` 扩容换缓冲区），
   变量指向新位置；`read` 检查值还活着；
3. 最后再检查一遍所有 `read` 参数（被调函数可能在任何时候读）。

所以同一个变量同时以 `inout` 和 `read` 传入，`read` 拿到的旧指针就会悬空。

**静态检查**：两个参数都必须拥有值；如果是同一个变量，只能两边都是 `read`。
`sink` 的参数调用后不再拥有值。

**主定理** `safety_and_no_leak`：检查器接受的程序（普通语句 + 调用），
执行和作用域结束时按 drop flag 的释放都不会出错，并且结束时堆上没有活着的值。

两参数已经覆盖排他性的核心（它本来就是参数两两之间的条件）；
n 个参数的版本需要列表上的两两不同，留到之后。
-/

namespace Core.Calls.Modes
open Core.Ownership.Move (Stmt)
open Core.Ownership.Drop (varsOk)
open Core.Ownership.Branch

inductive Mode | read | inout | sink
  deriving DecidableEq, Repr

structure Arg where
  m : Mode
  x : Var

/-! ## 静态检查 -/

/-- 调用之后：`sink` 的参数不再拥有值，其余不变。 -/
def afterArg (r : Arg) (σ : SEnv) : SEnv :=
  if r.m = .sink then upd σ r.x .no else σ

def checkCall (σ : SEnv) (a b : Arg) : Option SEnv :=
  if σ a.x = .yes ∧ σ b.x = .yes ∧ (a.x ≠ b.x ∨ (a.m = .read ∧ b.m = .read)) then
    some (afterArg b (afterArg a σ))
  else none

inductive S3
  | base (t : Stmt)
  | call (a b : Arg)

def checkS3 (N : Nat) (σ : SEnv) : S3 → Option SEnv
  | .base t   => checkStmtV N σ t
  | .call a b => checkCall σ a b

def checkList3 (N : Nat) (σ : SEnv) : List S3 → Option SEnv
  | []      => some σ
  | t :: ts =>
    match checkS3 N σ t with
    | some σ' => checkList3 N σ' ts
    | none    => none

/-! ## 动态语义 -/

/-- 被调函数对一个参数做的事。`l` 是调用开始时取出的指针。 -/
def eff (m : Mode) (x : Var) (l : Loc) (s : St) : Option St :=
  if s.live l = true then
    match m with
    | .read  => some s
    | .inout => some (allocOp x (freeOp x l s))
    | .sink  => some (freeOp x l s)
  else none

/-- 最后再检查一遍只读参数。 -/
def recheck (m : Mode) (l : Loc) (s : St) : Option St :=
  match m with
  | .read => if s.live l = true then some s else none
  | _     => some s

def execCall (s : St) (a b : Arg) : Option St :=
  match s.env a.x, s.env b.x with
  | some la, some lb =>
    match eff a.m a.x la s with
    | none    => none
    | some s1 =>
      match eff b.m b.x lb s1 with
      | none    => none
      | some s2 =>
        match recheck a.m la s2 with
        | none    => none
        | some s3 => recheck b.m lb s3
  | _, _ => none

def execS3 (s : St) : S3 → Option St
  | .base t   => execS s t
  | .call a b => execCall s a b

def execList3 (s : St) : List S3 → Option St
  | []      => some s
  | t :: ts =>
    match execS3 s t with
    | some s' => execList3 s' ts
    | none    => none

/-! ## 单个参数 -/

theorem eff_spec {N : Nat} {s : St} {x : Var} {l : Loc} (m : Mode)
    (hd : DInv N s) (hf : s.flag x = true) (he : s.env x = some l) (hlive : s.live l = true) :
    ∃ s', eff m x l s = some s' ∧ DInv N s' ∧
      (∀ y, y ≠ x → s'.flag y = s.flag y ∧ s'.env y = s.env y) ∧
      (∀ k, k ≠ l → s.live k = true → s'.live k = true) ∧
      (m = .sink → s'.flag x = false) ∧
      (m ≠ .sink → s'.flag x = true) ∧
      (m = .read → s' = s) := by
  cases m with
  | read =>
    exact ⟨s, by simp [eff, hlive], hd, fun _ _ => ⟨rfl, rfl⟩, fun _ _ h => h,
      (fun h => by cases h), (fun _ => hf), (fun _ => rfl)⟩
  | sink =>
    refine ⟨freeOp x l s, by simp [eff, hlive], dinv_free hd hf he, ?_, ?_,
      (fun _ => by simp [freeOp, upd]), (fun h => absurd rfl h), (fun h => by cases h)⟩
    · intro y hy
      exact ⟨by simp [freeOp, upd, hy], rfl⟩
    · intro k hk h
      simp [freeOp, upd, hk, h]
  | inout =>
    have hd1 := dinv_free hd hf he
    have hxN : x < N := hd.bound x hf
    have hd2 := dinv_alloc (x := x) hd1 (by simp [freeOp, upd]) hxN
    refine ⟨allocOp x (freeOp x l s), by simp [eff, hlive], hd2, ?_, ?_,
      (fun h => by cases h), (fun _ => by simp [allocOp, upd]), (fun h => by cases h)⟩
    · intro y hy
      exact ⟨by simp [allocOp, freeOp, upd, hy], by simp [allocOp, freeOp, upd, hy]⟩
    · intro k hk h
      by_cases hkn : k = s.next
      · simp [allocOp, freeOp, upd, hkn]
      · simp [allocOp, freeOp, upd, hkn, hk, h]

theorem recheck_ok {m : Mode} {l : Loc} {s : St} (h : m = .read → s.live l = true) :
    recheck m l s = some s := by
  cases m with
  | read  => simp [recheck, h rfl]
  | inout => rfl
  | sink  => rfl

/-! ## 调用 -/

/-- `afterArg` 逐点展开：只有 `sink` 参数本身变成 `no`。 -/
theorem afterArg_apply (r : Arg) (σ : SEnv) (z : Var) :
    afterArg r σ z = if r.m = .sink ∧ z = r.x then .no else σ z := by
  unfold afterArg
  by_cases h : r.m = .sink
  · by_cases hz : z = r.x <;> simp [h, hz, upd]
  · simp [h]

theorem call_sound {N : Nat} {σ σ' : SEnv} {s : St} {a b : Arg}
    (hc : checkCall σ a b = some σ') (hc0 : Compat σ s.flag) (hd : DInv N s) :
    ∃ s', execCall s a b = some s' ∧ Compat σ' s'.flag ∧ DInv N s' := by
  simp only [checkCall] at hc
  split at hc
  · rename_i hcond
    cases hc
    obtain ⟨hya, hyb, hex⟩ := hcond
    have hfa := hc0.yes a.x hya
    have hfb := hc0.yes b.x hyb
    obtain ⟨la, hela, hla⟩ := hd.owned_live a.x hfa
    obtain ⟨lb, helb, hlb⟩ := hd.owned_live b.x hfb
    by_cases hab : a.x = b.x
    · -- 同一个变量：排他性要求两边都只读，调用不改变任何东西
      have hrd : a.m = .read ∧ b.m = .read := by
        cases hex with
        | inl h => exact absurd hab h
        | inr h => exact h
      obtain ⟨hra, hrb⟩ := hrd
      have hlab : lb = la := by
        rw [hab] at hela; rw [hela] at helb; exact (Option.some.inj helb).symm
      subst hlab
      refine ⟨s, ?_, ?_, hd⟩
      · simp [execCall, hela, helb, eff, recheck, hra, hrb, hla]
      · simpa [afterArg, hra, hrb] using hc0
    · -- 不同变量：拥有者唯一，所以两个指针不同，互不影响
      have hba : b.x ≠ a.x := Ne.symm hab
      have hlab : la ≠ lb := by
        intro h; rw [h] at hela; exact hab (hd.unique a.x b.x lb hfa hfb hela helb)
      obtain ⟨s1, he1, hd1, fr1, lv1, sk1, nsk1, rd1⟩ := eff_spec a.m hd hfa hela hla
      have hfb1 : s1.flag b.x = true := by rw [(fr1 b.x hba).1]; exact hfb
      have helb1 : s1.env b.x = some lb := by rw [(fr1 b.x hba).2]; exact helb
      have hlb1 : s1.live lb = true := lv1 lb (Ne.symm hlab) hlb
      obtain ⟨s2, he2, hd2, fr2, lv2, sk2, nsk2, rd2⟩ := eff_spec b.m hd1 hfb1 helb1 hlb1
      have hr3 : recheck a.m la s2 = some s2 := by
        apply recheck_ok
        intro hra
        have h1 : s1.live la = true := by rw [rd1 hra]; exact hla
        exact lv2 la hlab h1
      have hr4 : recheck b.m lb s2 = some s2 := by
        apply recheck_ok
        intro hrb
        rw [rd2 hrb]; exact hlb1
      refine ⟨s2, ?_, ?_, hd2⟩
      · simp only [execCall, hela, helb, he1, he2, hr3, hr4]
      · constructor
        · intro z hz
          rw [afterArg_apply, afterArg_apply] at hz
          by_cases hzb : z = b.x
          · rw [hzb] at hz ⊢
            by_cases hbs : b.m = .sink
            · simp [hbs] at hz
            · exact nsk2 hbs
          · by_cases hza : z = a.x
            · rw [hza] at hz ⊢
              by_cases has : a.m = .sink
              · simp [has, hab] at hz
              · rw [(fr2 a.x hab).1]; exact nsk1 has
            · simp [hza, hzb] at hz
              rw [(fr2 z hzb).1, (fr1 z hza).1]
              exact hc0.yes z hz
        · intro z hz
          rw [afterArg_apply, afterArg_apply] at hz
          by_cases hzb : z = b.x
          · rw [hzb] at hz ⊢
            by_cases hbs : b.m = .sink
            · exact sk2 hbs
            · simp [hbs, hba, hyb] at hz
          · by_cases hza : z = a.x
            · rw [hza] at hz ⊢
              by_cases has : a.m = .sink
              · rw [(fr2 a.x hab).1]; exact sk1 has
              · simp [has, hab, hya] at hz
            · simp [hza, hzb] at hz
              rw [(fr2 z hzb).1, (fr1 z hza).1]
              exact hc0.no z hz
  · contradiction

/-! ## 语句列表 -/

theorem stepS3 {N : Nat} {σ σ' : SEnv} {s : St} {t : S3}
    (hc : checkS3 N σ t = some σ') (hc0 : Compat σ s.flag) (hd : DInv N s) :
    ∃ s', execS3 s t = some s' ∧ Compat σ' s'.flag ∧ DInv N s' := by
  cases t with
  | base t =>
    simp only [checkS3, checkStmtV] at hc
    split at hc
    · rename_i hv
      exact stepS hv hc hc0 hd
    · contradiction
  | call a b =>
    simp only [checkS3] at hc
    exact call_sound hc hc0 hd

theorem listSound3 (N : Nat) (ts : List S3) :
    ∀ {σ σ' : SEnv} {s : St}, checkList3 N σ ts = some σ' → Compat σ s.flag → DInv N s →
      ∃ s', execList3 s ts = some s' ∧ Compat σ' s'.flag ∧ DInv N s' := by
  induction ts with
  | nil =>
    intro σ σ' s hc hc0 hd
    simp [checkList3] at hc
    subst hc
    exact ⟨s, by simp [execList3], hc0, hd⟩
  | cons t ts ih =>
    intro σ σ' s hc hc0 hd
    simp only [checkList3] at hc
    split at hc
    · rename_i σ₁ h₁
      obtain ⟨s₁, he₁, hc₁, hd₁⟩ := stepS3 h₁ hc0 hd
      obtain ⟨s₂, he₂, hc₂, hd₂⟩ := ih hc hc₁ hd₁
      exact ⟨s₂, by simp only [execList3, he₁, he₂], hc₂, hd₂⟩
    · contradiction

/-! ## 主定理 -/

/-- **`Calls.Modes` 主定理。** 检查器接受的程序（普通语句 + 带参数约定的调用），
执行和作用域结束时按 drop flag 的释放都不会出错，并且结束时堆上没有活着的值。 -/
theorem safety_and_no_leak (N : Nat) (ts : List S3) (σ' : SEnv)
    (h : checkList3 N (fun _ => .no) ts = some σ') :
    ∃ s', (execList3 St.empty ts).bind (fun s => dropAll s N) = some s' ∧
      ∀ l, s'.live l = false := by
  obtain ⟨s₁, he₁, _, hd₁⟩ := listSound3 N ts h compat_empty (dinv_empty N)
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

/-- 合法的调用：`f(inout 0, read 1)`、`g(read 0, read 0)`、`h(sink 0, read 1)`。 -/
def okProg : List S3 :=
  [.base (.alloc 0), .base (.alloc 1),
   .call ⟨.inout, 0⟩ ⟨.read, 1⟩,
   .call ⟨.read, 0⟩ ⟨.read, 0⟩,
   .call ⟨.sink, 0⟩ ⟨.read, 1⟩]

example : (checkList3 2 (fun _ => .no) okProg).isSome = true := rfl
example : ((execList3 St.empty okProg).bind (fun s => dropAll s 2)).isSome = true := rfl

/-- `sink` 之后 0 不再拥有值，再传给调用就被拒绝。 -/
example : (checkList3 2 (fun _ => .no) (okProg ++ [.call ⟨.read, 0⟩ ⟨.read, 1⟩])).isNone = true := rfl

/-- 违反排他性：同一个变量既 `inout` 又 `read`。检查器拒绝，不经检查执行真的会出错。 -/
def alias1 : List S3 := [.base (.alloc 0), .call ⟨.inout, 0⟩ ⟨.read, 0⟩]
example : (checkList3 1 (fun _ => .no) alias1).isNone = true := rfl
example : (execList3 St.empty alias1).isNone = true := rfl

/-- 反过来的顺序也一样：先 `read` 再 `inout`，最后的复查会读到已释放的旧值。 -/
def alias2 : List S3 := [.base (.alloc 0), .call ⟨.read, 0⟩ ⟨.inout, 0⟩]
example : (checkList3 1 (fun _ => .no) alias2).isNone = true := rfl
example : (execList3 St.empty alias2).isNone = true := rfl

/-- 同一个变量既 `read` 又 `sink`：同样被拒绝，执行也会出错。 -/
def alias3 : List S3 := [.base (.alloc 0), .call ⟨.read, 0⟩ ⟨.sink, 0⟩]
example : (checkList3 1 (fun _ => .no) alias3).isNone = true := rfl
example : (execList3 St.empty alias3).isNone = true := rfl

end Core.Calls.Modes

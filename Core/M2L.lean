import Core.M2b

/-!
# M2b（下·二）：循环

在任意嵌套分支的基础上加入 `loop b`：每一轮由外部输入决定继续（`true`）还是退出（`false`）。

**静态检查**（不动点，只算两轮）：

1. 先从进入前的状态 `σ` 检查一遍循环体，得到 `σb`；
2. 循环头状态 `τ := join σ σb`；
3. 再从 `τ` 检查一遍循环体，得到 `σ2`，要求 `σ2` 不比 `τ` 更强（`leN`），
   也就是循环体跑完一轮后，状态还能当作下一轮的循环头。

每个变量只会从 `yes` / `no` 变成 `maybe`，不会变回来，所以不需要无限迭代；
检查失败就拒绝程序，这样做是保守的。

**动态语义**：用燃料 `fuel` 保证执行函数一定终止。结果有三种：
`ok`（正常结束）、`err`（内存错误）、`oof`（燃料耗尽）。

**主定理** `safety_and_no_leak`：检查器接受的程序，无论燃料多少、分支怎么走、
循环跑几轮，执行都**不会出现内存错误**；如果正常结束，作用域结束时按 drop flag
释放也不出错，并且堆上没有活着的值。燃料耗尽不算错误。

**新增的静态不变式** `Bounded`：编号不小于 `N` 的变量永远是 `no`。
`leN` 只比较前 `N` 个变量，这条不变式保证其余变量也满足要求。
-/

namespace Core.M2L
open Core.M1 (Stmt)
open Core.M2 (varsOk)
open Core.M2b

inductive Prog
  | skip
  | stmt   (t : Stmt)
  | seq    (p q : Prog)
  | branch (p q : Prog)
  | loop   (b : Prog)

/-- 在前 `N` 个变量上检查 `τ` 不比 `σ` 更强：每个变量要么相同，要么在 `τ` 里是 `maybe`。 -/
def leN (N : Nat) (σ τ : SEnv) : Bool :=
  (List.range N).all (fun x => decide (τ x = σ x) || decide (τ x = .maybe))

def check (N : Nat) : Prog → SEnv → Option SEnv
  | .skip,       σ => some σ
  | .stmt t,     σ => checkStmtV N σ t
  | .seq p q,    σ =>
    match check N p σ with
    | some σ₁ => check N q σ₁
    | none    => none
  | .branch p q, σ =>
    match check N p σ, check N q σ with
    | some σa, some σb => some (join σa σb)
    | _, _             => none
  | .loop b,     σ =>
    match check N b σ with
    | none    => none
    | some σb =>
      match check N b (join σ σb) with
      | none    => none
      | some σ2 => if leN N σ2 (join σ σb) = true then some (join σ σb) else none

inductive Res
  | ok  (s : St) (cs : List Bool)
  | err
  | oof

def exec : Nat → Prog → St → List Bool → Res
  | 0,     _,            _, _  => .oof
  | _ + 1, .skip,        s, cs => .ok s cs
  | _ + 1, .stmt t,      s, cs =>
    match execS s t with
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

/-- 结果满足要求：正常结束时不变式成立，内存错误不可能，燃料耗尽不作要求。 -/
def Good (N : Nat) (σ' : SEnv) : Res → Prop
  | .ok s _ => Compat σ' s.flag ∧ DInv N s
  | .err    => False
  | .oof    => True

/-! ## 静态不变式 `Bounded` -/

def Bounded (N : Nat) (σ : SEnv) : Prop := ∀ x, N ≤ x → σ x = .no

theorem bounded_empty (N : Nat) : Bounded N (fun _ => .no) := by
  intro x _; rfl

theorem bounded_join {N : Nat} {σa σb : SEnv} (ha : Bounded N σa) (hb : Bounded N σb) :
    Bounded N (join σa σb) := by
  intro x hx
  simp only [join]
  rw [ha x hx, hb x hx]
  simp

theorem bounded_checkS {N : Nat} {σ σ' : SEnv} {t : Stmt}
    (hv : varsOk N t = true) (hc : checkS σ t = some σ') (hb : Bounded N σ) :
    Bounded N σ' := by
  cases t with
  | alloc x =>
    simp only [checkS] at hc
    split at hc
    · cases hc
      simp only [varsOk, decide_eq_true_eq] at hv
      intro z hz
      have hzx : z ≠ x := by
        intro h; rw [h] at hz; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hv hz)
      rw [upd_other σ .yes hzx]
      exact hb z hz
    · contradiction
  | move x y =>
    simp only [checkS] at hc
    split at hc
    · contradiction
    · split at hc
      · split at hc
        · cases hc
          simp only [varsOk, decide_eq_true_eq] at hv
          intro z hz
          have hzy : z ≠ y := by
            intro h; rw [h] at hz; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hv hz)
          rw [upd_other (upd σ x Own.no) Own.yes hzy]
          by_cases hzx : z = x
          · rw [hzx]; exact upd_same _ _ _
          · rw [upd_other σ .no hzx]; exact hb z hz
        · contradiction
      · contradiction
  | use x =>
    simp only [checkS] at hc
    split at hc
    · cases hc; exact hb
    · contradiction
  | free x =>
    simp only [checkS] at hc
    split at hc
    · cases hc
      intro z hz
      by_cases hzx : z = x
      · rw [hzx]; exact upd_same _ _ _
      · rw [upd_other σ .no hzx]; exact hb z hz
    · contradiction

theorem bounded_check (N : Nat) (p : Prog) :
    ∀ {σ σ' : SEnv}, check N p σ = some σ' → Bounded N σ → Bounded N σ' := by
  induction p with
  | skip =>
    intro σ σ' hc hb
    simp [check] at hc
    subst hc
    exact hb
  | stmt t =>
    intro σ σ' hc hb
    simp only [check, checkStmtV] at hc
    split at hc
    · rename_i hv
      exact bounded_checkS hv hc hb
    · contradiction
  | seq p q ihp ihq =>
    intro σ σ' hc hb
    simp only [check] at hc
    split at hc
    · rename_i σ₁ h₁
      exact ihq hc (ihp h₁ hb)
    · contradiction
  | branch p q ihp ihq =>
    intro σ σ' hc hb
    simp only [check] at hc
    split at hc
    · rename_i σa σb hpa hpb
      cases hc
      exact bounded_join (ihp hpa hb) (ihq hpb hb)
    · contradiction
  | loop b ih =>
    intro σ σ' hc hb
    simp only [check] at hc
    split at hc
    · contradiction
    · rename_i σb hσb
      split at hc
      · contradiction
      · split at hc
        · cases hc
          exact bounded_join hb (ih hσb hb)
        · contradiction

/-! ## 状态之间的“不更强”关系 -/

def Le (σ τ : SEnv) : Prop := ∀ x, τ x = σ x ∨ τ x = .maybe

theorem compat_le {σ τ : SEnv} {f : Var → Bool} (h : Le σ τ) (hc : Compat σ f) :
    Compat τ f := by
  constructor
  · intro x hx
    cases h x with
    | inl e => rw [e] at hx; exact hc.yes x hx
    | inr e => rw [e] at hx; cases hx
  · intro x hx
    cases h x with
    | inl e => rw [e] at hx; exact hc.no x hx
    | inr e => rw [e] at hx; cases hx

theorem le_join_left {σa σb : SEnv} : Le σa (join σa σb) := by
  intro x
  simp only [join]
  split
  · left; rfl
  · right; rfl

theorem le_join_right {σa σb : SEnv} : Le σb (join σa σb) := by
  intro x
  simp only [join]
  split
  · rename_i h; left; exact h
  · right; rfl

theorem leN_sound {N : Nat} {σ τ : SEnv} (h : leN N σ τ = true)
    (hbσ : Bounded N σ) (hbτ : Bounded N τ) : Le σ τ := by
  intro x
  by_cases hx : x < N
  · have := List.all_eq_true.mp h x (List.mem_range.mpr hx)
    simpa using this
  · have hx' : N ≤ x := Nat.le_of_not_lt hx
    left
    rw [hbσ x hx', hbτ x hx']

theorem join_of_le {σ τ : SEnv} (h : Le σ τ) : join τ σ = τ := by
  funext x
  simp only [join]
  split
  · rfl
  · rename_i hne
    cases h x with
    | inl e => exact absurd e hne
    | inr e => exact e.symm

theorem good_weaken {N : Nat} {σ τ : SEnv} {r : Res} (h : Le σ τ) :
    Good N σ r → Good N τ r := by
  cases r with
  | ok s cs =>
    intro g
    simp only [Good] at g ⊢
    exact ⟨compat_le h g.1, g.2⟩
  | err => intro g; simp [Good] at g
  | oof => intro _; simp [Good]

/-- 循环头状态是检查器的不动点：从 `τ` 再检查一次循环，结果还是 `τ`。 -/
theorem loop_fix {N : Nat} {b : Prog} {τ σ2 : SEnv}
    (h2 : check N b τ = some σ2) (hLe : Le σ2 τ) (hle : leN N σ2 τ = true) :
    check N (.loop b) τ = some τ := by
  simp [check, h2, join_of_le hLe, hle]

/-! ## 主引理 -/

theorem sound (N : Nat) (n : Nat) :
    ∀ (p : Prog) {σ σ' : SEnv} {s : St} (cs : List Bool),
      check N p σ = some σ' → Bounded N σ → Compat σ s.flag → DInv N s →
      Good N σ' (exec n p s cs) := by
  induction n with
  | zero =>
    intro p σ σ' s cs _ _ _ _
    simp [exec, Good]
  | succ n ih =>
    intro p σ σ' s cs hc hb hc0 hd
    cases p with
    | skip =>
      simp [check] at hc
      subst hc
      simp only [exec, Good]
      exact ⟨hc0, hd⟩
    | stmt t =>
      simp only [check, checkStmtV] at hc
      split at hc
      · rename_i hv
        obtain ⟨s', he, hc', hd'⟩ := stepS hv hc hc0 hd
        simp only [exec, he, Good]
        exact ⟨hc', hd'⟩
      · contradiction
    | seq p q =>
      simp only [check] at hc
      split at hc
      · rename_i σ₁ h₁
        have hb₁ := bounded_check N p h₁ hb
        have g₁ := ih p cs h₁ hb hc0 hd
        cases he₁ : exec n p s cs with
        | ok s₁ cs₁ =>
          rw [he₁] at g₁
          simp only [Good] at g₁
          obtain ⟨hc₁, hd₁⟩ := g₁
          simp only [exec, he₁]
          exact ih q cs₁ hc hb₁ hc₁ hd₁
        | err => rw [he₁] at g₁; simp [Good] at g₁
        | oof => simp only [exec, he₁, Good]
      · contradiction
    | branch p q =>
      simp only [check] at hc
      split at hc
      · rename_i σa σb hpa hpb
        cases hc
        by_cases hcs : cs.headD false = true
        · have g := ih p cs.tail hpa hb hc0 hd
          simp only [exec, hcs, ite_true]
          exact good_weaken le_join_left g
        · have g := ih q cs.tail hpb hb hc0 hd
          simp only [exec, hcs]
          simp only [ite_false, Bool.false_eq_true] at *
          exact good_weaken le_join_right g
      · contradiction
    | loop b =>
      simp only [check] at hc
      split at hc
      · contradiction
      · rename_i σb hσb
        split at hc
        · contradiction
        · rename_i σ2 h2
          split at hc
          · rename_i hle
            cases hc
            have hbb := bounded_check N b hσb hb
            have hbτ : Bounded N (join σ σb) := bounded_join hb hbb
            have hb2 := bounded_check N b h2 hbτ
            have hLe : Le σ2 (join σ σb) := leN_sound hle hb2 hbτ
            have hfix := loop_fix h2 hLe hle
            have hcτ : Compat (join σ σb) s.flag := compat_le le_join_left hc0
            by_cases hcs : cs.headD false = true
            · have g := ih b cs.tail h2 hbτ hcτ hd
              cases he : exec n b s cs.tail with
              | ok s₁ cs₁ =>
                rw [he] at g
                simp only [Good] at g
                obtain ⟨hc₁, hd₁⟩ := g
                simp only [exec, hcs, ite_true, he]
                exact ih (.loop b) cs₁ hfix hbτ (compat_le hLe hc₁) hd₁
              | err => rw [he] at g; simp [Good] at g
              | oof => simp only [exec, hcs, ite_true, he, Good]
            · simp only [exec, hcs]
              simp only [ite_false, Bool.false_eq_true] at *
              simp only [Good]
              exact ⟨hcτ, hd⟩
          · contradiction

/-! ## 主定理 -/

/-- **M2b（下·二）主定理。** 检查器接受的程序，无论燃料多少、分支怎么走、循环跑几轮：
执行不会出现内存错误；如果正常结束，按 drop flag 释放也不出错，并且堆上没有活着的值。 -/
theorem safety_and_no_leak (N : Nat) (p : Prog) (σ' : SEnv)
    (h : check N p (fun _ => .no) = some σ') (fuel : Nat) (cs : List Bool) :
    exec fuel p St.empty cs ≠ .err ∧
    ∀ s cs', exec fuel p St.empty cs = .ok s cs' →
      ∃ s', dropAll s N = some s' ∧ ∀ l, s'.live l = false := by
  have g := sound N fuel p cs h (bounded_empty N) compat_empty (dinv_empty N)
  constructor
  · intro he
    rw [he] at g
    simp [Good] at g
  · intro s cs' he
    rw [he] at g
    simp only [Good] at g
    obtain ⟨_, hd₁⟩ := g
    obtain ⟨s₂, he₂, hd₂, hf₂⟩ := dropAll_sound hd₁ N
    refine ⟨s₂, he₂, ?_⟩
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

def isErr : Res → Bool
  | .err => true
  | _    => false

/-- 每轮分配一个临时值并释放，循环结束后仍然可以使用外面的 0。 -/
def good : Prog :=
  .seq (.stmt (.alloc 0))
    (.seq (.loop (.seq (.stmt (.alloc 1)) (.stmt (.free 1)))) (.stmt (.use 0)))

/-- 检查器接受。 -/
example : (check 2 good (fun _ => .no)).isSome = true := rfl

/-- 循环三轮再退出，执行不出错。 -/
example : isErr (exec 20 good St.empty [true, true, true, false]) = false := rfl

/-- 循环体把外面的 0 移走：第二轮时 0 已经不在了，检查器拒绝。 -/
def bad : Prog :=
  .seq (.stmt (.alloc 0)) (.loop (.seq (.stmt (.move 0 1)) (.stmt (.free 1))))

example : (check 2 bad (fun _ => .no)).isNone = true := rfl

/-- 检查器为什么必要：同样的程序跑两轮，第二轮真的会读到已释放的内存。 -/
example : isErr (exec 20 bad St.empty [true, true, false]) = true := rfl

end Core.M2L

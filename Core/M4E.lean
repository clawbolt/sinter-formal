import Core.M4C

/-!
# M4（四）：分支、循环上的活跃性分析

M4（二）在直线代码上插入投影结束点；M4（三·上）在分支、循环里要求结束点显式写出。
这一轮把两者合起来：源程序里不写结束点，编译器在结构化控制流上自动算出来。

**结束点放在哪里**：顺序组合 `seq p q es` 带一张表 `es`，表示“执行完 `p` 之后、
执行 `q` 之前，结束这些投影”。源程序里所有的 `es` 都是空表；活跃性分析 `ends` 负责填写。
结束点不占用新的程序节点，所以擦掉结束点（`E`）之后，程序结构和燃料消耗都不变。

**活跃性分析** `liveIn`：
- `readp p` 使 `p` 活跃；`proj p x` 重新定义 `p`，在它之前 `p` 不活跃；
- 分支取两边的并集；循环按“循环之后活跃的 ∪ 循环体入口活跃的”迭代两轮。
在 `seq p q` 处，`p` 里用到、但在 `q` 入口已经不活跃的投影，放进 `es`。

**健全性不依赖分析是否精确**：检查器检查的是插入结束点之后的程序，
所以分析算错只会让程序被拒绝，不会让不安全的程序通过。证明只需要两件事：
- `erase_ends`：插入结束点再擦掉，得到的就是原来的源程序；
- `sim_exec`：带结束点和不带结束点的执行，堆完全相同，前者的投影指针是后者的子集，
  并且用同样的燃料走到同样的位置。

**主定理** `nll_safety`：只要插入结束点之后的程序通过检查，源程序本身无论燃料多少、
分支怎么走、循环跑几轮，执行都不会出现内存错误；正常结束时没有泄漏。

**已知的保守之处**：只在一个分支里用到的投影，在另一个分支里不会提前结束，
所以另一个分支不能释放或移走它的源对象。Rust 的 NLL 会接受这种程序。见文件末尾的例子。
-/

namespace Core.M4E
open Core.M2b (SEnv join dropAll dropAll_sound)
open Core.M2L (Bounded bounded_empty bounded_join Le leN leN_sound join_of_le
  le_join_left le_join_right)
open Core.M4 (Cmd Locks St4 check1 exec1 step1 Good good_empty Sim sim_step)
open Core.M4C (joinL subL joinL_mem join_yes joinL_self subL_sound good_weak goodR_weak
  bounded_check1 Res GoodR)

inductive P
  | skip
  | cmd    (c : Cmd)
  | seq    (p q : P) (es : List Var)
  | branch (p q : P)
  | loop   (b : P)

/-! ## 结束一组投影 -/

def endL (es : List Var) (ps : Locks) : Locks := ps.filter (fun e => !decide (e.1 ∈ es))

def endS (es : List Var) (s : St4) : St4 := ⟨s.b, fun p => if p ∈ es then none else s.pr p⟩

theorem good_endS {N : Nat} {σ : SEnv} {ps : Locks} {s : St4} (es : List Var)
    (hg : Good N σ ps s) : Good N σ (endL es ps) (endS es s) := by
  refine ⟨hg.compat, hg.dinv, ?_⟩
  intro p z hm
  unfold endL at hm
  obtain ⟨hm0, hn⟩ := List.mem_filter.mp hm
  have hpe : p ∉ es := by simpa using hn
  obtain ⟨hz, hpz⟩ := hg.pinv p z hm0
  exact ⟨hz, by simp [endS, hpe, hpz]⟩

/-! ## 静态检查与动态语义（和 M4（三·上）相同，只是 `seq` 多了结束点） -/

def check (N : Nat) : P → SEnv → Locks → Option (SEnv × Locks)
  | .skip,        σ, ps => some (σ, ps)
  | .cmd c,       σ, ps => check1 N σ ps c
  | .seq p q es,  σ, ps =>
    match check N p σ ps with
    | some (σ₁, ps₁) => check N q σ₁ (endL es ps₁)
    | none           => none
  | .branch p q,  σ, ps =>
    match check N p σ ps, check N q σ ps with
    | some (σa, pa), some (σb, pb) => some (join σa σb, joinL σa σb pa pb)
    | _, _                         => none
  | .loop b,      σ, ps =>
    match check N b σ ps with
    | none          => none
    | some (σb, pb) =>
      match check N b (join σ σb) (joinL σ σb ps pb) with
      | none          => none
      | some (σ2, p2) =>
        if leN N σ2 (join σ σb) = true ∧ subL (joinL σ σb ps pb) p2 = true then
          some (join σ σb, joinL σ σb ps pb)
        else none

def exec : Nat → P → St4 → List Bool → Res
  | 0,     _,             _, _  => .oof
  | _ + 1, .skip,         s, cs => .ok s cs
  | _ + 1, .cmd c,        s, cs =>
    match exec1 s c with
    | some s' => .ok s' cs
    | none    => .err
  | n + 1, .seq p q es,   s, cs =>
    match exec n p s cs with
    | .ok s₁ cs₁ => exec n q (endS es s₁) cs₁
    | .err       => .err
    | .oof       => .oof
  | n + 1, .branch p q,   s, cs =>
    if cs.headD false = true then exec n p s cs.tail else exec n q s cs.tail
  | n + 1, .loop b,       s, cs =>
    if cs.headD false = true then
      match exec n b s cs.tail with
      | .ok s₁ cs₁ => exec n (.loop b) s₁ cs₁
      | .err       => .err
      | .oof       => .oof
    else .ok s cs.tail

/-! ## 检查器的健全性（照搬 M4（三·上），`seq` 处多一步 `good_endS`） -/

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
  | seq p q es ihp ihq =>
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
    | seq p q es =>
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
          exact ih q cs₁ hc hb₁ (good_endS es g₁)
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

/-! ## 活跃性分析 -/

/-- 程序里用到的投影（创建或读取）。 -/
def usesP : P → List Var
  | .skip         => []
  | .cmd c        => (Core.M4.uses c).toList
  | .seq p q _    => usesP p ++ usesP q
  | .branch p q   => usesP p ++ usesP q
  | .loop b       => usesP b

def liveCmd (c : Cmd) (L : List Var) : List Var :=
  match c with
  | .proj p _ => L.filter (fun y => y != p)
  | .readp p  => p :: L
  | _         => L

/-- 入口处活跃的投影：`L` 是出口处活跃的投影。 -/
def liveIn : P → List Var → List Var
  | .skip,        L => L
  | .cmd c,       L => liveCmd c L
  | .seq p q _,   L => liveIn p (liveIn q L)
  | .branch p q,  L => liveIn p L ++ liveIn q L
  | .loop b,      L => L ++ liveIn b (L ++ liveIn b L)

/-- 插入结束点：`L` 是出口处活跃的投影。 -/
def ends : P → List Var → P
  | .skip,        _ => .skip
  | .cmd c,       _ => .cmd c
  | .seq p q _,   L =>
    .seq (ends p (liveIn q L)) (ends q L)
      ((usesP p).filter (fun x => !decide (x ∈ liveIn q L)))
  | .branch p q,  L => .branch (ends p L) (ends q L)
  | .loop b,      L => .loop (ends b (L ++ liveIn b (L ++ liveIn b L)))

/-- 擦掉所有结束点，得到实际运行的程序。 -/
def E : P → P
  | .skip        => .skip
  | .cmd c       => .cmd c
  | .seq p q _   => .seq (E p) (E q) []
  | .branch p q  => .branch (E p) (E q)
  | .loop b      => .loop (E b)

theorem erase_ends (p : P) : ∀ L, E (ends p L) = E p := by
  induction p with
  | skip => intro L; rfl
  | cmd c => intro L; rfl
  | seq p q es ihp ihq => intro L; simp [ends, E, ihp, ihq]
  | branch p q ihp ihq => intro L; simp [ends, E, ihp, ihq]
  | loop b ih => intro L; simp [ends, E, ih]

/-! ## 模拟：擦掉结束点不会让执行出错 -/

/-- 两个执行结果的关系：左边出错时不作要求；否则两边同时燃料耗尽，或者同时正常结束且状态满足 `Sim`。 -/
def RelR : Res → Res → Prop
  | .ok s cs, .ok t cs' => Sim s t ∧ cs = cs'
  | .oof,     .oof      => True
  | .err,     _         => True
  | _,        _         => False

theorem relR_err (r : Res) : RelR .err r := by
  cases r <;> simp [RelR]

theorem sim_endS {s t : St4} (es : List Var) (hs : Sim s t) :
    Sim (endS es s) (endS [] t) := by
  refine ⟨hs.eqb, ?_⟩
  intro p l h
  by_cases hp : p ∈ es
  · simp [endS, hp] at h
  · simp [endS, hp] at h
    simp [endS]
    exact hs.sub p l h

theorem sim_cmd {s t s' : St4} {c : Cmd} (hs : Sim s t) (he : exec1 s c = some s') :
    ∃ t', exec1 t c = some t' ∧ Sim s' t' := by
  cases c with
  | endp p =>
    simp only [exec1, Option.some.injEq] at he
    subst he
    refine ⟨⟨t.b, upd t.pr p none⟩, by simp [exec1], ⟨hs.eqb, ?_⟩⟩
    intro q l hq
    by_cases hqp : q = p
    · subst hqp
      simp at hq
    · simp [upd, hqp] at hq ⊢
      exact hs.sub q l hq
  | base t0 => exact sim_step hs he rfl
  | proj p x => exact sim_step hs he rfl
  | readp p => exact sim_step hs he rfl

theorem sim_exec (n : Nat) : ∀ (p : P) (s t : St4) (cs : List Bool), Sim s t →
    RelR (exec n p s cs) (exec n (E p) t cs) := by
  induction n with
  | zero =>
    intro p s t cs _
    simp [exec, RelR]
  | succ n ih =>
    intro p s t cs hs
    cases p with
    | skip =>
      simp only [E, exec]
      show Sim s t ∧ cs = cs
      exact ⟨hs, rfl⟩
    | cmd c =>
      cases he : exec1 s c with
      | some s' =>
        obtain ⟨t', ht, hs'⟩ := sim_cmd hs he
        simp only [E, exec, he, ht]
        show Sim s' t' ∧ cs = cs
        exact ⟨hs', rfl⟩
      | none =>
        simp only [E, exec, he]
        exact relR_err _
    | seq p q es =>
      have g := ih p s t cs hs
      simp only [E, exec]
      cases h1 : exec n p s cs with
      | ok s₁ cs₁ =>
        cases h2 : exec n (E p) t cs with
        | ok t₁ cs₂ =>
          rw [h1, h2] at g
          simp only [RelR] at g
          obtain ⟨hs₁, rfl⟩ := g
          exact ih q _ _ cs₁ (sim_endS es hs₁)
        | err => rw [h1, h2] at g; simp [RelR] at g
        | oof => rw [h1, h2] at g; simp [RelR] at g
      | err => exact relR_err _
      | oof =>
        cases h2 : exec n (E p) t cs with
        | oof => simp [RelR]
        | ok _ _ => rw [h1, h2] at g; simp [RelR] at g
        | err => rw [h1, h2] at g; simp [RelR] at g
    | branch p q =>
      by_cases hcs : cs.headD false = true
      · simp only [E, exec, hcs, ite_true]
        exact ih p s t cs.tail hs
      · simp only [E, exec, hcs]
        simp only [ite_false, Bool.false_eq_true] at *
        exact ih q s t cs.tail hs
    | loop b =>
      by_cases hcs : cs.headD false = true
      · simp only [E, exec, hcs, ite_true]
        have g := ih b s t cs.tail hs
        cases h1 : exec n b s cs.tail with
        | ok s₁ cs₁ =>
          cases h2 : exec n (E b) t cs.tail with
          | ok t₁ cs₂ =>
            rw [h1, h2] at g
            simp only [RelR] at g
            obtain ⟨hs₁, rfl⟩ := g
            exact ih (.loop b) s₁ t₁ cs₁ hs₁
          | err => rw [h1, h2] at g; simp [RelR] at g
          | oof => rw [h1, h2] at g; simp [RelR] at g
        | err => exact relR_err _
        | oof =>
          cases h2 : exec n (E b) t cs.tail with
          | oof => simp [RelR]
          | ok _ _ => rw [h1, h2] at g; simp [RelR] at g
          | err => rw [h1, h2] at g; simp [RelR] at g
      · simp only [E, exec, hcs]
        simp only [ite_false, Bool.false_eq_true] at *
        show Sim s t ∧ cs.tail = cs.tail
        exact ⟨hs, rfl⟩

/-! ## 主定理 -/

/-- **M4（四）主定理。** 源程序 `p` 里没有结束点（`E p = p`）。只要插入结束点后的程序
通过检查，源程序本身无论燃料多少、分支怎么走、循环跑几轮，执行都不会出现内存错误；
正常结束时按 drop flag 释放不出错，并且堆上没有活着的值。 -/
theorem nll_safety (N : Nat) (p : P) (σ' : SEnv) (ps' : Locks)
    (hsrc : E p = p)
    (h : check N (ends p []) (fun _ => .no) [] = some (σ', ps'))
    (fuel : Nat) (cs : List Bool) :
    exec fuel p St4.empty cs ≠ .err ∧
    ∀ t cs', exec fuel p St4.empty cs = .ok t cs' →
      ∃ b, dropAll t.b N = some b ∧ ∀ l, b.live l = false := by
  have g := sound N fuel (ends p []) cs h (bounded_empty N) (good_empty N)
  have r := sim_exec fuel (ends p []) St4.empty St4.empty cs ⟨rfl, fun _ _ h => h⟩
  rw [erase_ends, hsrc] at r
  constructor
  · intro he
    rw [he] at r
    cases hl : exec fuel (ends p []) St4.empty cs with
    | ok s cs₁ => rw [hl] at r; simp [RelR] at r
    | err => rw [hl] at g; simp [GoodR] at g
    | oof => rw [hl] at r; simp [RelR] at r
  · intro t cs' he
    rw [he] at r
    cases hl : exec fuel (ends p []) St4.empty cs with
    | ok s cs₁ =>
      rw [hl] at r g
      simp only [RelR] at r
      simp only [GoodR] at g
      obtain ⟨hs, _⟩ := r
      obtain ⟨b, hb, hd, hf⟩ := dropAll_sound g.dinv N
      refine ⟨b, by rw [← hs.eqb]; exact hb, ?_⟩
      intro l
      cases hl' : b.live l with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨x, hx, _⟩ := hd.live_owned l hl'
        have hxN := hd.bound x hx
        rw [hf x hxN] at hx
        contradiction
    | err => rw [hl] at g; simp [GoodR] at g
    | oof => rw [hl] at r; simp [RelR] at r

/-! ## 例子（投影名用 5；源程序里不写结束点） -/

def block : List P → P
  | []      => .skip
  | p :: ps => .seq p (block ps) []

def isErr : Res → Bool
  | .err => true
  | _    => false

/-- `let p = proj v.0; read p; move v`：不插结束点会被拒绝，插入后接受，源程序执行不出错。 -/
def ex1 : P := block
  [.cmd (.base (.alloc 0)), .cmd (.proj 5 0), .cmd (.readp 5), .cmd (.base (.move 0 1))]
example : (check 2 ex1 (fun _ => .no) []).isNone = true := rfl
example : (check 2 (ends ex1 []) (fun _ => .no) []).isSome = true := rfl
example : isErr (exec 50 ex1 St4.empty []) = false := rfl

/-- 只在一个分支里读投影，分支之后释放源对象：接受。 -/
def ex2 : P := block
  [.cmd (.base (.alloc 0)), .cmd (.proj 5 0),
   .branch (.cmd (.readp 5)) .skip,
   .cmd (.base (.free 0))]
example : (check 2 (ends ex2 []) (fun _ => .no) []).isSome = true := rfl

/-- 投影跨越循环，循环之后释放源对象：结束点落在循环出口，接受。 -/
def ex3 : P := block
  [.cmd (.base (.alloc 0)), .cmd (.proj 5 0),
   .loop (.cmd (.readp 5)),
   .cmd (.base (.free 0))]
example : (check 2 (ends ex3 []) (fun _ => .no) []).isSome = true := rfl
example : isErr (exec 50 ex3 St4.empty [true, true, false]) = false := rfl

/-- 每轮重新创建投影：`proj` 重新定义 `p`，结束点落在每轮读取之后，接受。 -/
def ex4 : P := block
  [.cmd (.base (.alloc 0)),
   .loop (block [.cmd (.proj 5 0), .cmd (.readp 5)]),
   .cmd (.base (.free 0))]
example : (check 2 (ends ex4 []) (fun _ => .no) []).isSome = true := rfl
example : isErr (exec 50 ex4 St4.empty [true, true, true, false]) = false := rfl

/-- 释放源对象之后还要读投影：插入结束点也救不了，拒绝。 -/
def bad1 : P := block
  [.cmd (.base (.alloc 0)), .cmd (.proj 5 0), .cmd (.base (.free 0)), .cmd (.readp 5)]
example : (check 2 (ends bad1 []) (fun _ => .no) []).isNone = true := rfl

/-- 已知的保守之处：一个分支读投影，另一个分支释放源对象。
Rust 的 NLL 接受；这里另一个分支不会提前结束投影，所以拒绝。 -/
def conservative : P := block
  [.cmd (.base (.alloc 0)), .cmd (.proj 5 0),
   .branch (.cmd (.readp 5)) (.cmd (.base (.free 0)))]
example : (check 2 (ends conservative []) (fun _ => .no) []).isNone = true := rfl

end Core.M4E

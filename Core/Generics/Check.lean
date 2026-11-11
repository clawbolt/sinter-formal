import Core.Unified.Base

/-!
# 泛型——定义处按抽象类型检查

**问题**：泛型函数在定义处检查一次，之后对每个实例生成代码（单态化）。
需要保证：定义处检查通过，则每个满足约束的实例在具体类型下也检查通过，
从而由 `Unified.Base` 的主定理得到实例的安全与无泄漏。

**类型的三类**（`Kind`）：可复制（`copy`，没有资源）、需要析构（`own`，作用域结束时自动析构）、
`linear`（`lin`，必须显式消费）。类型参数 `T` 在定义处的抽象类别：
普通的 `T` 按 `own` 检查（只能移动、可以隐式析构）；`T: linear` 按 `lin` 检查（只能移动、必须消费）。
实例化 `θ`：普通的 `T` 只能换成 `copy` 或 `own`，`T: linear` 可以换成任何类别。

**语言**：变量的命令 `new x`（得到一个值，例如参数入口、构造）、`use x`（读）、
`move x y`（`y := x`，同类型之间）、`give x`（以 `sink` 交给被调函数）；顺序、分支、循环。
按变量的类别翻译成 `Unified.Base` 的命令：`own` → 所有权命令，`lin` → 线性值命令，`copy` → 没有命令（没有资源要跟踪）。
读线性值记作“先消费再重建”，只用于检查它此刻是活的。

**主定理** `instance_accepted`：抽象类别下 `Unified.Base` 检查器接受，则实例类别下也接受。
证明是一个模拟：实例的静态状态由抽象状态逐变量算出（`R`）。
关键在于：实例类别总是“不比抽象类别严格”（`kle`），而 `lin` 的状态在汇合点两边必须相同，
所以换成 `own` 后合并结果和不合并一样。

**例子**说明两件事：定义处检查比逐个实例检查严格（错误报在定义处）；
普通的 `T` 实例化成 `linear` 类型会被拒绝（泛型代码可能隐式析构它）。
-/

namespace Core.Generics.Check
open Core.Unified.Base (C P SS)

inductive Kind | copy | own | lin
  deriving DecidableEq, Repr

/-- 实例类别不比抽象类别严格：`copy ≤ own ≤ lin`。 -/
def kle : Kind → Kind → Bool
  | .copy, _    => true
  | .own, .own  => true
  | .own, .lin  => true
  | .lin, .lin  => true
  | _, _        => false

/-- 变量的类型：具体类别，或者第 `i` 个类型参数。 -/
inductive Ty
  | k   (k : Kind)
  | par (i : Nat)
  deriving DecidableEq, Repr

/-- 定义处的抽象类别；`bnd i = true` 表示第 `i` 个参数写了 `T: linear`。 -/
def absK (bnd : Nat → Bool) : Ty → Kind
  | .k k   => k
  | .par i => if bnd i then .lin else .own

/-- 实例的类别。 -/
def instK (θ : Nat → Kind) : Ty → Kind
  | .k k   => k
  | .par i => θ i

/-- 实例化满足约束：没写 `T: linear` 的参数不能换成 `linear` 类型。 -/
def Respects (bnd : Nat → Bool) (θ : Nat → Kind) : Prop := ∀ i, bnd i = false → θ i ≠ .lin

inductive GC
  | new  (x : Var)
  | use  (x : Var)
  | move (x y : Var)
  | give (x : Var)

inductive G
  | skip
  | cmd    (c : GC)
  | seq    (p q : G)
  | branch (p q : G)
  | loop   (b : G)

/-! ## 翻译成 `Unified.Base` -/

def trC (K : Var → Kind) : GC → P
  | .new x =>
    match K x with
    | .copy => .skip
    | .own  => .cmd (.own (.base (.alloc x)))
    | .lin  => .cmd (.lin (.lnew x))
  | .use x =>
    match K x with
    | .copy => .skip
    | .own  => .cmd (.own (.base (.use x)))
    | .lin  => .seq (.cmd (.lin (.consume x))) (.cmd (.lin (.lnew x)))
  | .move x y =>
    match K x with
    | .copy => .skip
    | .own  => .cmd (.own (.base (.move x y)))
    | .lin  => .cmd (.lin (.lmove x y))
  | .give x =>
    match K x with
    | .copy => .skip
    | .own  => .cmd (.own (.base (.free x)))
    | .lin  => .cmd (.lin (.consume x))

def tr (K : Var → Kind) : G → P
  | .skip       => .skip
  | .cmd c      => trC K c
  | .seq p q    => .seq (tr K p) (tr K q)
  | .branch p q => .branch (tr K p) (tr K q)
  | .loop b     => .loop (tr K b)

/-- 良构：变量都小于 `N`，`move` 只在同类型的变量之间。 -/
def gcOk (N : Nat) (Γ : Var → Ty) : GC → Bool
  | .new x    => decide (x < N)
  | .use x    => decide (x < N)
  | .give x   => decide (x < N)
  | .move x y => decide (x < N) && decide (y < N) && decide (Γ x = Γ y)

def gOk (N : Nat) (Γ : Var → Ty) : G → Bool
  | .skip       => true
  | .cmd c      => gcOk N Γ c
  | .seq p q    => gOk N Γ p && gOk N Γ q
  | .branch p q => gOk N Γ p && gOk N Γ q
  | .loop b     => gOk N Γ b

/-- 定义处检查：按抽象类别翻译，交给 `Unified.Base` 的检查器。 -/
def genericOk (N : Nat) (Γ : Var → Ty) (bnd : Nat → Bool) (g : G) : Bool :=
  gOk N Γ g && Core.Unified.Base.accepts N (tr (fun x => absK bnd (Γ x)) g)

/-- 实例检查：按实例类别翻译。 -/
def instanceOk (N : Nat) (Γ : Var → Ty) (θ : Nat → Kind) (g : G) : Bool :=
  Core.Unified.Base.accepts N (tr (fun x => instK θ (Γ x)) g)

/-! ## 例子

变量 0、1 的类型是参数 `T`，变量 2 是具体的需要析构的类型。参数入口记作 `new`。 -/

def Γx : Var → Ty := fun x => if x = 2 then .k .own else .par 0
def plain : Nat → Bool := fun _ => false
def linB : Nat → Bool := fun _ => true
def θc : Nat → Kind := fun _ => .copy
def θo : Nat → Kind := fun _ => .own
def θl : Nat → Kind := fun _ => .lin

/-- `fn keep<T>(sink a: T) { let b = a }`：`b` 在作用域结束时隐式析构。 -/
def keep : G := .seq (.cmd (.new 0)) (.cmd (.move 0 1))

example : genericOk 3 Γx plain keep = true := rfl
example : instanceOk 3 Γx θc keep = true := rfl
example : instanceOk 3 Γx θo keep = true := rfl
/-- 普通的 `T` 换成 `linear` 类型：`b` 没被消费，实例被拒绝——所以约束是必要的。 -/
example : instanceOk 3 Γx θl keep = false := rfl
/-- 写了 `T: linear`，定义处就拒绝隐式析构。 -/
example : genericOk 3 Γx linB keep = false := rfl

/-- `fn pass<T: linear>(sink a: T) { sink_it(a) }`：三种实例都接受。 -/
def pass : G := .seq (.cmd (.new 0)) (.cmd (.give 0))

example : genericOk 3 Γx linB pass = true := rfl
example : instanceOk 3 Γx θc pass = true := rfl
example : instanceOk 3 Γx θo pass = true := rfl
example : instanceOk 3 Γx θl pass = true := rfl

/-- 交出之后再读：定义处拒绝；可复制的实例本身没有问题——错误报在定义处，而不是等到某个实例。 -/
def reuse : G := .seq (.cmd (.new 0)) (.seq (.cmd (.give 0)) (.cmd (.use 0)))

example : genericOk 3 Γx plain reuse = false := rfl
example : instanceOk 3 Γx θc reuse = true := rfl

/-- 分支里只在一边交出：普通的 `T` 按 drop flag 析构，接受；`T: linear` 要求两边一致，拒绝。 -/
def half : G := .seq (.cmd (.new 0)) (.branch (.cmd (.give 0)) .skip)

example : genericOk 3 Γx plain half = true := rfl
example : genericOk 3 Γx linB half = false := rfl

/-- 循环里每轮交出再重新得到：两种约束下都接受。 -/
def cyc : G := .seq (.cmd (.new 0)) (.seq (.loop (.seq (.cmd (.give 0)) (.cmd (.new 0)))) (.cmd (.give 0)))

example : genericOk 3 Γx linB cyc = true := rfl
example : instanceOk 3 Γx θo cyc = true := rfl

/-! ## `Unified.Base` 单条命令的展开 -/

open Core.Ownership.Branch (Own SEnv join)

section
variable {N : Nat}

theorem seq_inv {p q : P} {s s' : SS} (h : Core.Unified.Base.check N (.seq p q) s = some s') :
    ∃ s1, Core.Unified.Base.check N p s = some s1 ∧ Core.Unified.Base.check N q s1 = some s' := by
  simp only [Core.Unified.Base.check] at h
  split at h
  · rename_i s1 h1
    exact ⟨s1, h1, h⟩
  · contradiction

theorem seq_run {p q : P} {s s1 s2 : SS} (h1 : Core.Unified.Base.check N p s = some s1)
    (h2 : Core.Unified.Base.check N q s1 = some s2) : Core.Unified.Base.check N (.seq p q) s = some s2 := by
  simp [Core.Unified.Base.check, h1, h2]

theorem baseOk_nil (t : Core.Ownership.Move.Stmt) : Core.Projection.Lock.baseOk [] t = true := by
  cases t <;> rfl

theorem chk_own {s s' : SS} {t : Core.Ownership.Move.Stmt} (hps : s.ps = [])
    (h : Core.Unified.Base.check N (.cmd (.own (.base t))) s = some s') :
    ∃ σ', Core.Ownership.Branch.checkStmtV N s.σ t = some σ' ∧ s' = ⟨σ', [], s.Λ⟩ := by
  have hb := baseOk_nil t
  cases hc : Core.Ownership.Branch.checkStmtV N s.σ t with
  | none => simp [Core.Unified.Base.check, Core.Unified.Base.checkC, Core.Projection.Lock.check1, hps, hb, hc] at h
  | some σ' =>
    simp [Core.Unified.Base.check, Core.Unified.Base.checkC, Core.Projection.Lock.check1, hps, hb, hc] at h
    exact ⟨σ', rfl, by rw [← h]⟩

theorem run_own {c : SS} {t : Core.Ownership.Move.Stmt} {τ : SEnv} (hps : c.ps = [])
    (h : Core.Ownership.Branch.checkStmtV N c.σ t = some τ) :
    Core.Unified.Base.check N (.cmd (.own (.base t))) c = some ⟨τ, [], c.Λ⟩ := by
  have hb := baseOk_nil t
  simp [Core.Unified.Base.check, Core.Unified.Base.checkC, Core.Projection.Lock.check1, hps, hb, h]

theorem chk_lin {s s' : SS} {t : Core.Linearity.Linear.Stmt} (h : Core.Unified.Base.check N (.cmd (.lin t)) s = some s') :
    ∃ Λ', Core.Linearity.Linear.varsOk N t = true ∧ Core.Linearity.Linear.checkS s.Λ t = some Λ' ∧ s' = ⟨s.σ, s.ps, Λ'⟩ := by
  simp only [Core.Unified.Base.check, Core.Unified.Base.checkC] at h
  split at h
  · rename_i hv
    cases hc : Core.Linearity.Linear.checkS s.Λ t with
    | none => simp [hc] at h
    | some Λ' =>
      simp [hc] at h
      exact ⟨Λ', hv, rfl, by rw [← h]⟩
  · contradiction

theorem run_lin {c : SS} {t : Core.Linearity.Linear.Stmt} {Λ' : Core.Linearity.Linear.LEnv} (hv : Core.Linearity.Linear.varsOk N t = true)
    (h : Core.Linearity.Linear.checkS c.Λ t = some Λ') :
    Core.Unified.Base.check N (.cmd (.lin t)) c = some ⟨c.σ, c.ps, Λ'⟩ := by
  simp [Core.Unified.Base.check, Core.Unified.Base.checkC, hv, h]

/-! 所有权命令（`Ownership.Branch`）的展开 -/

theorem own_alloc_inv {σ σ' : SEnv} {x : Var}
    (h : Core.Ownership.Branch.checkStmtV N σ (.alloc x) = some σ') : σ x = .no ∧ σ' = upd σ x .yes := by
  simp only [Core.Ownership.Branch.checkStmtV, Core.Ownership.Branch.checkS] at h
  split at h
  · split at h
    · rename_i h1; cases h; exact ⟨h1, rfl⟩
    · contradiction
  · contradiction

theorem own_use_inv {σ σ' : SEnv} {x : Var}
    (h : Core.Ownership.Branch.checkStmtV N σ (.use x) = some σ') : σ x = .yes ∧ σ' = σ := by
  simp only [Core.Ownership.Branch.checkStmtV, Core.Ownership.Branch.checkS] at h
  split at h
  · split at h
    · rename_i h1; cases h; exact ⟨h1, rfl⟩
    · contradiction
  · contradiction

theorem own_free_inv {σ σ' : SEnv} {x : Var}
    (h : Core.Ownership.Branch.checkStmtV N σ (.free x) = some σ') : σ x = .yes ∧ σ' = upd σ x .no := by
  simp only [Core.Ownership.Branch.checkStmtV, Core.Ownership.Branch.checkS] at h
  split at h
  · split at h
    · rename_i h1; cases h; exact ⟨h1, rfl⟩
    · contradiction
  · contradiction

theorem own_move_inv {σ σ' : SEnv} {x y : Var}
    (h : Core.Ownership.Branch.checkStmtV N σ (.move x y) = some σ') :
    x ≠ y ∧ σ x = .yes ∧ σ y = .no ∧ σ' = upd (upd σ x .no) y .yes := by
  simp only [Core.Ownership.Branch.checkStmtV, Core.Ownership.Branch.checkS] at h
  split at h
  · split at h
    · contradiction
    · rename_i hxy
      split at h
      · rename_i hx
        split at h
        · rename_i hy; cases h; exact ⟨hxy, hx, hy, rfl⟩
        · contradiction
      · contradiction
  · contradiction

theorem own_alloc_run {σ : SEnv} {x : Var} (hx : x < N) (h : σ x = .no) :
    Core.Ownership.Branch.checkStmtV N σ (.alloc x) = some (upd σ x .yes) := by
  simp [Core.Ownership.Branch.checkStmtV, Core.Ownership.Drop.varsOk, Core.Ownership.Branch.checkS, hx, h]

theorem own_use_run {σ : SEnv} {x : Var} (h : σ x = .yes) :
    Core.Ownership.Branch.checkStmtV N σ (.use x) = some σ := by
  simp [Core.Ownership.Branch.checkStmtV, Core.Ownership.Drop.varsOk, Core.Ownership.Branch.checkS, h]

theorem own_free_run {σ : SEnv} {x : Var} (h : σ x = .yes) :
    Core.Ownership.Branch.checkStmtV N σ (.free x) = some (upd σ x .no) := by
  simp [Core.Ownership.Branch.checkStmtV, Core.Ownership.Drop.varsOk, Core.Ownership.Branch.checkS, h]

theorem own_move_run {σ : SEnv} {x y : Var} (hy : y < N) (hxy : x ≠ y) (hx : σ x = .yes)
    (hyn : σ y = .no) :
    Core.Ownership.Branch.checkStmtV N σ (.move x y) = some (upd (upd σ x .no) y .yes) := by
  simp [Core.Ownership.Branch.checkStmtV, Core.Ownership.Drop.varsOk, Core.Ownership.Branch.checkS, hy, hxy, hx, hyn]

end

/-! 线性值命令（`Linearity.Linear`）的展开 -/

theorem lin_lnew_inv {Λ Λ' : Core.Linearity.Linear.LEnv} {x : Var}
    (h : Core.Linearity.Linear.checkS Λ (.lnew x) = some Λ') : Λ x = false ∧ Λ' = upd Λ x true := by
  simp only [Core.Linearity.Linear.checkS] at h
  split at h
  · rename_i h1; cases h; exact ⟨h1, rfl⟩
  · contradiction

theorem lin_consume_inv {Λ Λ' : Core.Linearity.Linear.LEnv} {x : Var}
    (h : Core.Linearity.Linear.checkS Λ (.consume x) = some Λ') : Λ x = true ∧ Λ' = upd Λ x false := by
  simp only [Core.Linearity.Linear.checkS] at h
  split at h
  · rename_i h1; cases h; exact ⟨h1, rfl⟩
  · contradiction

theorem lin_lmove_inv {Λ Λ' : Core.Linearity.Linear.LEnv} {x y : Var}
    (h : Core.Linearity.Linear.checkS Λ (.lmove x y) = some Λ') :
    x ≠ y ∧ Λ x = true ∧ Λ y = false ∧ Λ' = upd (upd Λ x false) y true := by
  simp only [Core.Linearity.Linear.checkS] at h
  split at h
  · rename_i h1
    obtain ⟨a, b, c⟩ := h1
    cases h
    exact ⟨a, b, c, rfl⟩
  · contradiction

/-! ## 模拟关系

实例状态 `c` 由抽象状态 `s` 逐变量决定（只看前 `N` 个变量）：
- 实例是 `copy`：没有状态；
- 抽象、实例都是 `own`：所有权状态相同；
- 抽象 `lin`、实例 `own`：线性值“活着”对应“拥有”；
- 都是 `lin`：线性值状态相同。 -/

def Rel : Kind → Kind → SS → SS → Var → Prop
  | _,    .copy, _, c, z => c.σ z = .no ∧ c.Λ z = false
  | .own, .own,  s, c, z => c.σ z = s.σ z ∧ c.Λ z = false
  | .lin, .own,  s, c, z => c.σ z = (if s.Λ z = true then .yes else .no) ∧ c.Λ z = false
  | .lin, .lin,  s, c, z => c.σ z = .no ∧ c.Λ z = s.Λ z
  | _,    _,     _, _, _ => False

structure R (N : Nat) (Ka Kc : Var → Kind) (s c : SS) : Prop where
  ps  : s.ps = []
  cps : c.ps = []
  pt  : ∀ z, z < N → Rel (Ka z) (Kc z) s c z

theorem rel_congr {ka kc : Kind} {s c s' c' : SS} {z : Var}
    (h1 : s'.σ z = s.σ z) (h2 : s'.Λ z = s.Λ z) (h3 : c'.σ z = c.σ z) (h4 : c'.Λ z = c.Λ z) :
    Rel ka kc s c z → Rel ka kc s' c' z := by
  cases ka <;> cases kc <;> simp [Rel, h1, h2, h3, h4]

section
variable {N : Nat} {Ka Kc : Var → Kind}

/-- 只有 `chg` 里的变量变了，其余变量的关系照旧。 -/
theorem R_change {s c s' c' : SS} (hR : R N Ka Kc s c) (hps : s'.ps = []) (hcps : c'.ps = [])
    (chg : Var → Prop)
    (hs : ∀ z, ¬ chg z → s'.σ z = s.σ z ∧ s'.Λ z = s.Λ z)
    (hc : ∀ z, ¬ chg z → c'.σ z = c.σ z ∧ c'.Λ z = c.Λ z)
    (hpt : ∀ z, z < N → chg z → Rel (Ka z) (Kc z) s' c' z) : R N Ka Kc s' c' := by
  refine ⟨hps, hcps, fun z hz => ?_⟩
  by_cases hch : chg z
  · exact hpt z hz hch
  · obtain ⟨a1, a2⟩ := hs z hch
    obtain ⟨b1, b2⟩ := hc z hch
    exact rel_congr a1 a2 b1 b2 (hR.pt z hz)

/-- 实例里这些变量是 `copy`（没有命令），抽象状态怎么变都不影响关系。 -/
theorem R_copy {s c s' : SS} (hR : R N Ka Kc s c) (hps : s'.ps = []) (chg : Var → Prop)
    (hs : ∀ z, ¬ chg z → s'.σ z = s.σ z ∧ s'.Λ z = s.Λ z)
    (hcopy : ∀ z, chg z → Kc z = .copy) : R N Ka Kc s' c := by
  refine R_change hR hps hR.cps chg hs (fun _ _ => ⟨rfl, rfl⟩) (fun z hz hch => ?_)
  have hp := hR.pt z hz
  have hk := hcopy z hch
  rw [hk] at hp ⊢
  cases hka : Ka z <;> rw [hka] at hp <;> exact hp

theorem pt1 {P : Var → Prop} {x : Var} (px : P x) : ∀ z, z < N → z = x → P z := by
  intro z _ hz; subst hz; exact px

theorem pt2 {P : Var → Prop} {x y : Var} (px : P x) (py : P y) :
    ∀ z, z < N → z = x ∨ z = y → P z := by
  intro z _ hz
  rcases hz with hz | hz
  · subst hz; exact px
  · subst hz; exact py

/-- 单条命令的良构条件（抽象、实例两边的类别都由同一个类型决定，所以 `move` 两边类别相同）。 -/
def cOk (N : Nat) (Ka Kc : Var → Kind) : GC → Prop
  | .new x    => x < N
  | .use x    => x < N
  | .give x   => x < N
  | .move x y => x < N ∧ y < N ∧ Ka x = Ka y ∧ Kc x = Kc y

/-- **单条命令的模拟**：抽象类别下检查通过，实例类别下也通过，并且关系保持。 -/
theorem simC (g : GC) (hok : cOk N Ka Kc g) {s s' cs : SS} (hR : R N Ka Kc s cs)
    (hch : Core.Unified.Base.check N (trC Ka g) s = some s') :
    ∃ cs', Core.Unified.Base.check N (trC Kc g) cs = some cs' ∧ R N Ka Kc s' cs' := by
  cases g with
  | new x =>
    have hx : x < N := hok
    have hp := hR.pt x hx
    cases hka : Ka x <;> cases hkc : Kc x <;> rw [hka, hkc] at hp <;> simp only [Rel] at hp <;>
      simp only [trC, hka, hkc] at hch ⊢
    · simp only [Core.Unified.Base.check, Option.some.injEq] at hch
      subst hch
      exact ⟨cs, rfl, hR⟩
    · obtain ⟨σ', hσ, rfl⟩ := chk_own hR.ps hch
      obtain ⟨_, rfl⟩ := own_alloc_inv hσ
      exact ⟨cs, rfl, R_copy hR rfl (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun z (hz : z = x) => by rw [hz]; exact hkc)⟩
    · obtain ⟨σ', hσ, rfl⟩ := chk_own hR.ps hch
      obtain ⟨h1, rfl⟩ := own_alloc_inv hσ
      refine ⟨_, run_own hR.cps (own_alloc_run hx (by rw [hp.1]; exact h1)), ?_⟩
      refine R_change hR rfl rfl (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun z (hz : z ≠ x) => by simp [upd, hz]) (pt1 ?_)
      show Rel (Ka x) (Kc x) _ _ x
      rw [hka, hkc]; simp [Rel, hp.2]
    · obtain ⟨Λ', _, hΛ, rfl⟩ := chk_lin hch
      obtain ⟨_, rfl⟩ := lin_lnew_inv hΛ
      exact ⟨cs, rfl, R_copy hR hR.ps (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun z (hz : z = x) => by rw [hz]; exact hkc)⟩
    · obtain ⟨Λ', _, hΛ, rfl⟩ := chk_lin hch
      obtain ⟨h1, rfl⟩ := lin_lnew_inv hΛ
      refine ⟨_, run_own hR.cps (own_alloc_run hx (by simp [hp.1, h1])), ?_⟩
      refine R_change hR hR.ps rfl (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun z (hz : z ≠ x) => by simp [upd, hz]) (pt1 ?_)
      show Rel (Ka x) (Kc x) _ _ x
      rw [hka, hkc]; simp [Rel, hp.2]
    · obtain ⟨Λ', hv, hΛ, rfl⟩ := chk_lin hch
      obtain ⟨h1, rfl⟩ := lin_lnew_inv hΛ
      refine ⟨_, run_lin (Λ' := upd cs.Λ x true) hv (by simp [Core.Linearity.Linear.checkS, hp.2, h1]), ?_⟩
      refine R_change hR hR.ps hR.cps (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun z (hz : z ≠ x) => by simp [upd, hz]) (pt1 ?_)
      show Rel (Ka x) (Kc x) _ _ x
      rw [hka, hkc]; simp [Rel, hp.1]
  | use x =>
    have hx : x < N := hok
    have hp := hR.pt x hx
    cases hka : Ka x <;> cases hkc : Kc x <;> rw [hka, hkc] at hp <;> simp only [Rel] at hp <;>
      simp only [trC, hka, hkc] at hch ⊢
    · simp only [Core.Unified.Base.check, Option.some.injEq] at hch
      subst hch
      exact ⟨cs, rfl, hR⟩
    · obtain ⟨σ', hσ, rfl⟩ := chk_own hR.ps hch
      obtain ⟨_, rfl⟩ := own_use_inv hσ
      exact ⟨cs, rfl, R_copy hR rfl (fun z => z = x) (fun _ _ => ⟨rfl, rfl⟩)
        (fun z (hz : z = x) => by rw [hz]; exact hkc)⟩
    · obtain ⟨σ', hσ, rfl⟩ := chk_own hR.ps hch
      obtain ⟨h1, rfl⟩ := own_use_inv hσ
      refine ⟨_, run_own hR.cps (own_use_run (by rw [hp.1]; exact h1)), ?_⟩
      exact R_change hR rfl rfl (fun _ => False) (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩)
        (fun _ _ hf => hf.elim)
    · obtain ⟨s1, h1, h2⟩ := seq_inv hch
      obtain ⟨Λ1, _, hΛ1, rfl⟩ := chk_lin h1
      obtain ⟨Λ2, _, hΛ2, rfl⟩ := chk_lin h2
      obtain ⟨_, rfl⟩ := lin_consume_inv hΛ1
      obtain ⟨_, rfl⟩ := lin_lnew_inv hΛ2
      exact ⟨cs, rfl, R_copy hR hR.ps (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun z (hz : z = x) => by rw [hz]; exact hkc)⟩
    · obtain ⟨s1, h1, h2⟩ := seq_inv hch
      obtain ⟨Λ1, _, hΛ1, rfl⟩ := chk_lin h1
      obtain ⟨Λ2, _, hΛ2, rfl⟩ := chk_lin h2
      obtain ⟨a1, rfl⟩ := lin_consume_inv hΛ1
      obtain ⟨_, rfl⟩ := lin_lnew_inv hΛ2
      refine ⟨_, run_own hR.cps (own_use_run (by simp [hp.1, a1])), ?_⟩
      refine R_change hR hR.ps rfl (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun _ _ => ⟨rfl, rfl⟩) (pt1 ?_)
      show Rel (Ka x) (Kc x) _ _ x
      rw [hka, hkc]; simp [Rel, hp.1, hp.2, a1]
    · obtain ⟨s1, h1, h2⟩ := seq_inv hch
      obtain ⟨Λ1, hv1, hΛ1, rfl⟩ := chk_lin h1
      obtain ⟨Λ2, hv2, hΛ2, rfl⟩ := chk_lin h2
      obtain ⟨a1, rfl⟩ := lin_consume_inv hΛ1
      obtain ⟨_, rfl⟩ := lin_lnew_inv hΛ2
      refine ⟨_, seq_run (run_lin (Λ' := upd cs.Λ x false) hv1 (by simp [Core.Linearity.Linear.checkS, hp.2, a1]))
        (run_lin (Λ' := upd (upd cs.Λ x false) x true) hv2 (by simp [Core.Linearity.Linear.checkS])), ?_⟩
      refine R_change hR hR.ps hR.cps (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun z (hz : z ≠ x) => by simp [upd, hz]) (pt1 ?_)
      show Rel (Ka x) (Kc x) _ _ x
      rw [hka, hkc]; simp [Rel, hp.1]
  | give x =>
    have hx : x < N := hok
    have hp := hR.pt x hx
    cases hka : Ka x <;> cases hkc : Kc x <;> rw [hka, hkc] at hp <;> simp only [Rel] at hp <;>
      simp only [trC, hka, hkc] at hch ⊢
    · simp only [Core.Unified.Base.check, Option.some.injEq] at hch
      subst hch
      exact ⟨cs, rfl, hR⟩
    · obtain ⟨σ', hσ, rfl⟩ := chk_own hR.ps hch
      obtain ⟨_, rfl⟩ := own_free_inv hσ
      exact ⟨cs, rfl, R_copy hR rfl (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun z (hz : z = x) => by rw [hz]; exact hkc)⟩
    · obtain ⟨σ', hσ, rfl⟩ := chk_own hR.ps hch
      obtain ⟨h1, rfl⟩ := own_free_inv hσ
      refine ⟨_, run_own hR.cps (own_free_run (by rw [hp.1]; exact h1)), ?_⟩
      refine R_change hR rfl rfl (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun z (hz : z ≠ x) => by simp [upd, hz]) (pt1 ?_)
      show Rel (Ka x) (Kc x) _ _ x
      rw [hka, hkc]; simp [Rel, hp.2]
    · obtain ⟨Λ', _, hΛ, rfl⟩ := chk_lin hch
      obtain ⟨_, rfl⟩ := lin_consume_inv hΛ
      exact ⟨cs, rfl, R_copy hR hR.ps (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun z (hz : z = x) => by rw [hz]; exact hkc)⟩
    · obtain ⟨Λ', _, hΛ, rfl⟩ := chk_lin hch
      obtain ⟨h1, rfl⟩ := lin_consume_inv hΛ
      refine ⟨_, run_own hR.cps (own_free_run (by simp [hp.1, h1])), ?_⟩
      refine R_change hR hR.ps rfl (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun z (hz : z ≠ x) => by simp [upd, hz]) (pt1 ?_)
      show Rel (Ka x) (Kc x) _ _ x
      rw [hka, hkc]; simp [Rel, hp.2]
    · obtain ⟨Λ', hv, hΛ, rfl⟩ := chk_lin hch
      obtain ⟨h1, rfl⟩ := lin_consume_inv hΛ
      refine ⟨_, run_lin (Λ' := upd cs.Λ x false) hv (by simp [Core.Linearity.Linear.checkS, hp.2, h1]), ?_⟩
      refine R_change hR hR.ps hR.cps (fun z => z = x) (fun z (hz : z ≠ x) => by simp [upd, hz])
        (fun z (hz : z ≠ x) => by simp [upd, hz]) (pt1 ?_)
      show Rel (Ka x) (Kc x) _ _ x
      rw [hka, hkc]; simp [Rel, hp.1]
  | move x y =>
    obtain ⟨hx, hy, eKa, eKc⟩ := hok
    have hp := hR.pt x hx
    have hq := hR.pt y hy
    rw [← eKa, ← eKc] at hq
    have off : ∀ (f g : Var → Own) (z : Var), ¬(z = x ∨ z = y) → f z = g z →
        upd (upd f x .no) y .yes z = g z := by
      intro f g z hz he
      simp only [not_or] at hz
      simp [upd, hz.1, hz.2, he]
    have offL : ∀ (f g : Core.Linearity.Linear.LEnv) (z : Var), ¬(z = x ∨ z = y) → f z = g z →
        upd (upd f x false) y true z = g z := by
      intro f g z hz he
      simp only [not_or] at hz
      simp [upd, hz.1, hz.2, he]
    cases hka : Ka x <;> cases hkc : Kc x <;> rw [hka, hkc] at hp hq <;> simp only [Rel] at hp hq <;>
      simp only [trC, hka, hkc] at hch ⊢
    · simp only [Core.Unified.Base.check, Option.some.injEq] at hch
      subst hch
      exact ⟨cs, rfl, hR⟩
    · obtain ⟨σ', hσ, rfl⟩ := chk_own hR.ps hch
      obtain ⟨_, _, _, rfl⟩ := own_move_inv hσ
      exact ⟨cs, rfl, R_copy hR rfl (fun z => z = x ∨ z = y)
        (fun z hz => ⟨off _ _ z hz rfl, rfl⟩)
        (fun z (hz : z = x ∨ z = y) => by
          rcases hz with hz | hz
          · rw [hz]; exact hkc
          · rw [hz, ← eKc]; exact hkc)⟩
    · obtain ⟨σ', hσ, rfl⟩ := chk_own hR.ps hch
      obtain ⟨hxy, h1, h2, rfl⟩ := own_move_inv hσ
      refine ⟨_, run_own hR.cps (own_move_run hy hxy (by rw [hp.1]; exact h1) (by rw [hq.1]; exact h2)), ?_⟩
      refine R_change hR rfl rfl (fun z => z = x ∨ z = y) (fun z hz => ⟨off _ _ z hz rfl, rfl⟩)
        (fun z hz => ⟨off _ _ z hz rfl, rfl⟩) (pt2 ?_ ?_)
      · show Rel (Ka x) (Kc x) _ _ x
        rw [hka, hkc]; simp [Rel, upd, hxy, hp.2]
      · show Rel (Ka y) (Kc y) _ _ y
        rw [← eKa, ← eKc, hka, hkc]; simp [Rel, hq.2]
    · obtain ⟨Λ', _, hΛ, rfl⟩ := chk_lin hch
      obtain ⟨_, _, _, rfl⟩ := lin_lmove_inv hΛ
      exact ⟨cs, rfl, R_copy hR hR.ps (fun z => z = x ∨ z = y)
        (fun z hz => ⟨rfl, offL _ _ z hz rfl⟩)
        (fun z (hz : z = x ∨ z = y) => by
          rcases hz with hz | hz
          · rw [hz]; exact hkc
          · rw [hz, ← eKc]; exact hkc)⟩
    · obtain ⟨Λ', _, hΛ, rfl⟩ := chk_lin hch
      obtain ⟨hxy, h1, h2, rfl⟩ := lin_lmove_inv hΛ
      refine ⟨_, run_own hR.cps (own_move_run hy hxy (by simp [hp.1, h1]) (by simp [hq.1, h2])), ?_⟩
      refine R_change hR hR.ps rfl (fun z => z = x ∨ z = y) (fun z hz => ⟨rfl, offL _ _ z hz rfl⟩)
        (fun z hz => ⟨off _ _ z hz rfl, rfl⟩) (pt2 ?_ ?_)
      · show Rel (Ka x) (Kc x) _ _ x
        rw [hka, hkc]; simp [Rel, upd, hxy, hp.2]
      · show Rel (Ka y) (Kc y) _ _ y
        rw [← eKa, ← eKc, hka, hkc]; simp [Rel, hq.2]
    · obtain ⟨Λ', hv, hΛ, rfl⟩ := chk_lin hch
      obtain ⟨hxy, h1, h2, rfl⟩ := lin_lmove_inv hΛ
      refine ⟨_, run_lin (Λ' := upd (upd cs.Λ x false) y true) hv
        (by simp [Core.Linearity.Linear.checkS, hxy, hp.2, hq.2, h1, h2]), ?_⟩
      refine R_change hR hR.ps hR.cps (fun z => z = x ∨ z = y) (fun z hz => ⟨rfl, offL _ _ z hz rfl⟩)
        (fun z hz => ⟨rfl, offL _ _ z hz rfl⟩) (pt2 ?_ ?_)
      · show Rel (Ka x) (Kc x) _ _ x
        rw [hka, hkc]; simp [Rel, upd, hxy, hp.1]
      · show Rel (Ka y) (Kc y) _ _ y
        rw [← eKa, ← eKc, hka, hkc]; simp [Rel, hq.1]

end

/-! ## 汇合点、循环头与整个程序 -/

theorem eqN_iff {N : Nat} {a b : Core.Linearity.Linear.LEnv} : Core.Linearity.Linear.eqN N a b = true ↔ ∀ z, z < N → a z = b z := by
  simp [Core.Linearity.Linear.eqN, List.all_eq_true, List.mem_range]

theorem leN_iff {N : Nat} {σ τ : SEnv} :
    Core.Ownership.Loop.leN N σ τ = true ↔ ∀ z, z < N → τ z = σ z ∨ τ z = .maybe := by
  simp [Core.Ownership.Loop.leN, List.all_eq_true, List.mem_range]

theorem allOff_iff {N : Nat} {Λ : Core.Linearity.Linear.LEnv} : Core.Linearity.Linear.allOff N Λ = true ↔ ∀ z, z < N → Λ z = false := by
  simp [Core.Linearity.Linear.allOff, List.all_eq_true, List.mem_range]

section
variable {N : Nat} {Ka Kc : Var → Kind}

/-- 抽象两边的线性值状态相同，则实例两边也相同（`own` 实例没有线性值状态）。 -/
theorem eq_sim {a b ca cb : SS} (hRa : R N Ka Kc a ca) (hRb : R N Ka Kc b cb)
    (heq : ∀ z, z < N → a.Λ z = b.Λ z) : Core.Linearity.Linear.eqN N ca.Λ cb.Λ = true := by
  rw [eqN_iff]
  intro z hz
  have h1 := hRa.pt z hz
  have h2 := hRb.pt z hz
  have he := heq z hz
  clear hRa hRb heq
  generalize Ka z = ka at h1 h2
  generalize Kc z = kc at h1 h2
  cases ka <;> cases kc <;> simp only [Rel] at h1 h2 <;> simp_all

/-- 汇合：抽象的合并对应实例的合并。关键在 `lin → own`：两边线性值状态相同，所以实例两边的所有权状态也相同。 -/
theorem join_sim {a b ca cb : SS} (hRa : R N Ka Kc a ca) (hRb : R N Ka Kc b cb)
    (heq : ∀ z, z < N → a.Λ z = b.Λ z) :
    Core.Linearity.Linear.eqN N ca.Λ cb.Λ = true ∧
      R N Ka Kc ⟨join a.σ b.σ, Core.Projection.Branches.joinL a.σ b.σ a.ps b.ps, a.Λ⟩
        ⟨join ca.σ cb.σ, Core.Projection.Branches.joinL ca.σ cb.σ ca.ps cb.ps, ca.Λ⟩ := by
  refine ⟨eq_sim hRa hRb heq, ?_, ?_, fun z hz => ?_⟩
  · show Core.Projection.Branches.joinL a.σ b.σ a.ps b.ps = []
    rw [hRa.ps]; rfl
  · show Core.Projection.Branches.joinL ca.σ cb.σ ca.ps cb.ps = []
    rw [hRa.cps]; rfl
  · have h1 := hRa.pt z hz
    have h2 := hRb.pt z hz
    have he := heq z hz
    clear hRa hRb heq
    generalize Ka z = ka at h1 h2 ⊢
    generalize Kc z = kc at h1 h2 ⊢
    cases ka <;> cases kc <;> simp only [Rel] at h1 h2 ⊢ <;> simp_all [join]

/-- 循环头的 `leN` 检查：抽象通过，实例也通过。 -/
theorem le_sim {a b ca cb : SS} (hRa : R N Ka Kc a ca) (hRb : R N Ka Kc b cb)
    (heq : ∀ z, z < N → a.Λ z = b.Λ z) (hle : Core.Ownership.Loop.leN N a.σ b.σ = true) :
    Core.Ownership.Loop.leN N ca.σ cb.σ = true := by
  rw [leN_iff] at hle ⊢
  intro z hz
  have h1 := hRa.pt z hz
  have h2 := hRb.pt z hz
  have he := heq z hz
  have hl := hle z hz
  clear hRa hRb heq hle
  generalize Ka z = ka at h1 h2
  generalize Kc z = kc at h1 h2
  cases ka <;> cases kc <;> simp only [Rel] at h1 h2 <;> simp_all

theorem allOff_sim {s c : SS} (hR : R N Ka Kc s c) (h : ∀ z, z < N → s.Λ z = false) :
    ∀ z, z < N → c.Λ z = false := by
  intro z hz
  have h1 := hR.pt z hz
  have h2 := h z hz
  clear hR h
  generalize Ka z = ka at h1
  generalize Kc z = kc at h1
  cases ka <;> cases kc <;> simp only [Rel] at h1 <;> simp_all

/-- 程序开始时的空状态满足关系，只要每个实例类别都不比抽象类别严格。 -/
theorem R_empty (h : ∀ z, kle (Kc z) (Ka z) = true) : R N Ka Kc SS.empty SS.empty := by
  refine ⟨rfl, rfl, fun z _ => ?_⟩
  have hk := h z
  clear h
  generalize Ka z = ka at hk ⊢
  generalize Kc z = kc at hk ⊢
  cases ka <;> cases kc <;> simp [kle, Rel, SS.empty] at hk ⊢

theorem cOk_of {Γ : Var → Ty} (hK : ∀ x y, Γ x = Γ y → Ka x = Ka y ∧ Kc x = Kc y)
    {c : GC} (h : gcOk N Γ c = true) : cOk N Ka Kc c := by
  cases c with
  | new x => simpa [gcOk, cOk] using h
  | use x => simpa [gcOk, cOk] using h
  | give x => simpa [gcOk, cOk] using h
  | move x y =>
    simp only [gcOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨h1, h2, (hK _ _ h3).1, (hK _ _ h3).2⟩

/-- **整个程序的模拟。** -/
theorem sim (Γ : Var → Ty) (hK : ∀ x y, Γ x = Γ y → Ka x = Ka y ∧ Kc x = Kc y) (g : G) :
    gOk N Γ g = true → ∀ {s s' cs : SS}, R N Ka Kc s cs → Core.Unified.Base.check N (tr Ka g) s = some s' →
      ∃ cs', Core.Unified.Base.check N (tr Kc g) cs = some cs' ∧ R N Ka Kc s' cs' := by
  induction g with
  | skip =>
    intro _ s s' cs hR hch
    simp only [tr, Core.Unified.Base.check, Option.some.injEq] at hch
    subst hch
    exact ⟨cs, rfl, hR⟩
  | cmd c =>
    intro hok s s' cs hR hch
    exact simC c (cOk_of hK hok) hR hch
  | seq p q ih1 ih2 =>
    intro hok s s' cs hR hch
    simp only [gOk, Bool.and_eq_true] at hok
    obtain ⟨s1, h1, h2⟩ := seq_inv hch
    obtain ⟨c1, hc1, hR1⟩ := ih1 hok.1 hR h1
    obtain ⟨c2, hc2, hR2⟩ := ih2 hok.2 hR1 h2
    exact ⟨c2, seq_run hc1 hc2, hR2⟩
  | branch p q ih1 ih2 =>
    intro hok s s' cs hR hch
    simp only [gOk, Bool.and_eq_true] at hok
    simp only [tr, Core.Unified.Base.check] at hch
    split at hch
    · rename_i a b ha hb
      obtain ⟨ca, hca, hRa⟩ := ih1 hok.1 hR ha
      obtain ⟨cb, hcb, hRb⟩ := ih2 hok.2 hR hb
      simp only [Core.Unified.Base.joinS] at hch
      split at hch
      · rename_i heq
        cases hch
        obtain ⟨hE, hJ⟩ := join_sim hRa hRb (eqN_iff.1 heq)
        exact ⟨_, by simp [tr, Core.Unified.Base.check, hca, hcb, Core.Unified.Base.joinS, hE], hJ⟩
      · contradiction
    · contradiction
  | loop b ih =>
    intro hok s s' cs hR hch
    simp only [gOk] at hok
    simp only [tr, Core.Unified.Base.check] at hch
    split at hch
    · contradiction
    · rename_i sb hsb
      split at hch
      · rename_i heq1
        split at hch
        · contradiction
        · rename_i s2 hs2
          split at hch
          · rename_i hcond
            cases hch
            obtain ⟨hle, _, heq2⟩ := hcond
            obtain ⟨csb, hcsb, hRb⟩ := ih hok hR hsb
            have e1 := eqN_iff.1 heq1
            have e2 := eqN_iff.1 heq2
            have hH : R N Ka Kc (Core.Unified.Base.headS s sb) (Core.Unified.Base.headS cs csb) :=
              (join_sim hR hRb (fun z hz => (e1 z hz).symm)).2
            obtain ⟨cs2, hcs2, hR2⟩ := ih hok hH hs2
            have c1 : Core.Linearity.Linear.eqN N csb.Λ cs.Λ = true := eq_sim hRb hR e1
            have c2 : Core.Ownership.Loop.leN N cs2.σ (Core.Unified.Base.headS cs csb).σ = true := le_sim hR2 hH e2 hle
            have c3 : Core.Projection.Branches.subL (Core.Unified.Base.headS cs csb).ps cs2.ps = true := by rw [hH.cps]; rfl
            have c4 : Core.Linearity.Linear.eqN N cs2.Λ cs.Λ = true := eq_sim hR2 hR e2
            exact ⟨_, by simp [tr, Core.Unified.Base.check, hcsb, c1, hcs2, c2, c3, c4], hH⟩
          · contradiction
      · contradiction

end

/-- 满足约束的实例化，实例类别总是不比抽象类别严格。 -/
theorem respects_kle {bnd : Nat → Bool} {θ : Nat → Kind} (hθ : Respects bnd θ) (t : Ty) :
    kle (instK θ t) (absK bnd t) = true := by
  cases t with
  | k k => cases k <;> rfl
  | par i =>
    simp only [instK, absK]
    cases hb : bnd i with
    | false =>
      have hne := hθ i hb
      revert hne
      generalize θ i = k
      cases k <;> decide
    | true =>
      generalize θ i = k
      cases k <;> decide

/-! ## 主定理 -/

/-- **`Generics.Check` 主定理。** 泛型函数在定义处（按抽象类别）检查通过，
则每个满足约束的实例（按具体类别）也检查通过。 -/
theorem instance_accepted (N : Nat) (Γ : Var → Ty) (bnd : Nat → Bool) (θ : Nat → Kind) (g : G)
    (hg : genericOk N Γ bnd g = true) (hθ : Respects bnd θ) : instanceOk N Γ θ g = true := by
  simp only [genericOk, Bool.and_eq_true] at hg
  obtain ⟨hok, hacc⟩ := hg
  simp only [Core.Unified.Base.accepts] at hacc
  split at hacc
  · rename_i s' hs'
    have hK : ∀ x y, Γ x = Γ y →
        absK bnd (Γ x) = absK bnd (Γ y) ∧ instK θ (Γ x) = instK θ (Γ y) :=
      fun x y h => ⟨congrArg (absK bnd) h, congrArg (instK θ) h⟩
    have h0 : R N (fun x => absK bnd (Γ x)) (fun x => instK θ (Γ x)) SS.empty SS.empty :=
      R_empty (fun z => respects_kle hθ (Γ z))
    obtain ⟨cs', hcs', hR'⟩ := sim Γ hK g hok h0 hs'
    simp only [instanceOk, Core.Unified.Base.accepts, hcs']
    rw [allOff_iff] at hacc ⊢
    exact allOff_sim hR' hacc
  · contradiction

/-- 推论：每个满足约束的实例都满足 `Unified.Base` 的安全与无泄漏。 -/
theorem instance_safe (N : Nat) (Γ : Var → Ty) (bnd : Nat → Bool) (θ : Nat → Kind) (g : G)
    (hg : genericOk N Γ bnd g = true) (hθ : Respects bnd θ) (fuel : Nat) (cs : List Bool) :
    let p := tr (fun x => instK θ (Γ x)) g
    Core.Unified.Base.exec fuel p Core.Unified.Base.St.empty cs ≠ .err ∧
    ∀ st cs', Core.Unified.Base.exec fuel p Core.Unified.Base.St.empty cs = .ok st cs' →
      (∃ b, Core.Ownership.Branch.dropAll st.o.b N = some b ∧ ∀ l, b.live l = false) ∧
      (∀ l, st.l.live l = false) :=
  Core.Unified.Base.safety_and_no_leak N _ (instance_accepted N Γ bnd θ g hg hθ) fuel cs

end Core.Generics.Check

import Core.M5b

/-!
# M5（四）：D3，函数的区域参数之间没有顺序

函数签名里可以有多个区域参数，例如 `fn f[a, b](x: &T in a) -> &T in b`。
调用者可以用**任意**实际区域实例化 `a`、`b`：`a` 可能在外层，也可能在内层。
所以函数体里不能假设 `a` 比 `b` 活得久，也就不能把 `&T in a` 转成 `&T in b`。

**模型**：函数体是一串“`y := x`”。每个变量的类型里带一个区域参数（`lab`）。
实例化 `ρ` 把区域参数映到实际区域（深度编号，越小越外层）。
变量的值是它指向的实际区域，类型正确（`Typed`）指“指向的区域不比类型里的区域更内层”，
和 M5（二）的 `j ≤ kx` 相同。

**主定理** `d3_sound`：按 D3 检查（区域参数之间只有相等关系）通过的函数，
对**每一种**实例化，只要输入类型正确，返回值也类型正确。

**反例** `leakFn`：如果允许假设 `a` 比 `b` 活得久（`leOrder`），函数体可以把 `&T in a` 当作
`&T in b` 返回。调用者用“`a` 在内层、`b` 在外层”实例化时，返回值就指向了比类型声明更内层的区域。
把这次调用内联进 M5（二）的程序，就是 `inlined`：M5（二）的检查器拒绝它，不经检查执行则出错。
-/

namespace Core.M5d

abbrev Label := Nat

structure Fn where
  lab  : Var → Label            -- 每个变量类型里的区域参数
  body : List (Var × Var)       -- 依次执行 y := x
  out  : Var                    -- 返回值

/-- 函数体检查：每一步 `y := x` 都要求 `ord (lab x) (lab y)`。 -/
def checkFn (ord : Label → Label → Bool) (f : Fn) : Bool :=
  f.body.all (fun e => ord (f.lab e.1) (f.lab e.2))

/-- D3：区域参数之间只有相等关系。 -/
def noOrder (l l' : Label) : Bool := l == l'

def run : List (Var × Var) → (Var → Nat) → (Var → Nat)
  | [],            env => env
  | (x, y) :: rest, env => run rest (upd env y (env x))

def Typed (f : Fn) (ρ : Label → Nat) (env : Var → Nat) : Prop :=
  ∀ v, env v ≤ ρ (f.lab v)

theorem run_typed (f : Fn) (ρ : Label → Nat) : ∀ (b : List (Var × Var)) (env : Var → Nat),
    b.all (fun e => noOrder (f.lab e.1) (f.lab e.2)) = true →
    Typed f ρ env → Typed f ρ (run b env) := by
  intro b
  induction b with
  | nil => intro env _ ht; exact ht
  | cons e rest ih =>
    intro env h ht
    obtain ⟨x, y⟩ := e
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hxy, hr⟩ := h
    have hl : f.lab x = f.lab y := by simpa [noOrder] using hxy
    apply ih _ hr
    intro v
    by_cases hv : v = y
    · rw [hv, upd_same, ← hl]
      exact ht x
    · rw [upd_other env (env x) hv]
      exact ht v

/-- **M5（四）主定理。** 按 D3 检查通过的函数，对每一种实例化 `ρ`，
只要输入类型正确，返回值也类型正确。 -/
theorem d3_sound (f : Fn) (h : checkFn noOrder f = true) (ρ : Label → Nat)
    (env : Var → Nat) (ht : Typed f ρ env) :
    run f.body env f.out ≤ ρ (f.lab f.out) :=
  run_typed f ρ f.body env h ht f.out

/-! ## 反例 -/

/-- `fn f[a, b](x: &T in a) -> &T in b { return x }`：变量 0 是参数（区域 a = 0），
变量 1 是返回值（区域 b = 1）。 -/
def leakFn : Fn := ⟨fun v => if v = 0 then 0 else 1, [(0, 1)], 1⟩

/-- 假设区域参数之间有顺序（a 比 b 活得久）。 -/
def leOrder (l l' : Label) : Bool := decide (l ≤ l')

example : checkFn leOrder leakFn = true := rfl
example : checkFn noOrder leakFn = false := rfl

/-- 实例化：a 在内层（深度 1），b 在外层（深度 0）。 -/
def ρbad : Label → Nat := fun l => if l = 0 then 1 else 0
/-- 输入：参数指向内层区域 1，类型正确。 -/
def env0 : Var → Nat := fun v => if v = 0 then 1 else 0

example : Typed leakFn ρbad env0 := by
  intro v
  by_cases hv : v = 0 <;> simp [leakFn, ρbad, env0, hv]

/-- 返回值指向内层区域 1，但类型声明的是外层区域 0。 -/
example : ¬ (run leakFn.body env0 leakFn.out ≤ ρbad (leakFn.lab leakFn.out)) := by decide

/-- 把这次调用内联进 M5（二）的程序：`y : &T in 0` 在外层，`x : &T in 1` 在内层，
`y := f(x)`，内层结束后读 `y`。 -/
def inlined : Core.M5b.P := .block (Core.M5b.seqL
  [.cmd (.decl 1 0),
   .block (Core.M5b.seqL [.cmd (.decl 0 1), .cmd (.ralloc 0 1), .cmd (.copy 0 1)]),
   .cmd (.read 1)])

/-- M5（二）的检查器拒绝它…… -/
example : (Core.M5b.check .plainOnly inlined 0 Core.M5b.SEnv.empty).isNone = true := rfl
/-- ……不经检查执行，读到了已经结束的区域。 -/
example : (Core.M5b.exec inlined Core.M5b.St.empty).isNone = true := rfl

end Core.M5d

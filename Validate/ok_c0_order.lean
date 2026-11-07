-- 由 sinterc --emit=core 生成，不要手工修改。
import Core.C5
set_option maxRecDepth 100000
open Core.M7h

/-- show -/
def f0 : CFG := [
  ⟨.nop, [], false⟩]

/-- sub -/
def f1 : CFG := [
  ⟨.nop, [], false⟩]

/-- main -/
def f2 : CFG := [
  ⟨.nop, [], false⟩]

#eval Core.C5.report [("show", 1, f0), ("sub", 1, f1), ("main", 1, f2)] true

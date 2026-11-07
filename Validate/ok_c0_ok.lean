-- 由 sinterc --emit=core 生成，不要手工修改。
import Core.C5
set_option maxRecDepth 100000
open Core.M7h

/-- add -/
def f0 : CFG := [
  ⟨.nop, [], false⟩]

/-- fact -/
def f1 : CFG := [
  ⟨.nop, [1, 2], false⟩,
  ⟨.nop, [3], false⟩,
  ⟨.nop, [3], false⟩,
  ⟨.nop, [], false⟩]

/-- main -/
def f2 : CFG := [
  ⟨.nop, [1], false⟩,
  ⟨.nop, [2, 3], false⟩,
  ⟨.nop, [1], false⟩,
  ⟨.nop, [4, 5], false⟩,
  ⟨.nop, [6], false⟩,
  ⟨.nop, [6], false⟩,
  ⟨.nop, [], false⟩]

#eval Core.C5.report [("add", 1, f0), ("fact", 1, f1), ("main", 1, f2)] true

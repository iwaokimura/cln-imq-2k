import Lean
/-! Kernel replay of the dependency closure of the B-4 final theorems, from an empty environment
(the method of lean4checker --fresh, restricted to the closure). Run with `lake env lean --run`. -/
open Lean

partial def closure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet := Id.run do
  let mut seen := seen
  let mut todo := todo
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some ci =>
      for m in ci.getUsedConstantsAsSet do
        if !seen.contains m then todo := m :: todo
      -- inductives: constructors and recursors are added with the type
      match ci with
      | .inductInfo v => todo := v.ctors ++ v.all ++ todo
      | .ctorInfo v => todo := v.induct :: todo
      | .recInfo v => todo := v.all ++ todo
      | _ => pure ()
    | none => pure ()
  return seen

def targets : List Name :=
  [`B4.ClassNumber.classNumber_gt_100, `B4.ClassNumber.classNumber_gt_200,
   `B4.ClassNumber.classNumber_gt_500, `B4.ClassNumber.classNumber_gt_1000,
   `B4.ClassNumber.classNumber_gt_2000,
   `B4.Cert.zero_gap_all, `B4.Chi8.re_LFunction_pos, `B4.Chi8.zero_gap_all, `B4.Chi8.zero_gap_large]

def main (args : List String) : IO UInt32 := do
  let extra := args.map System.FilePath.mk
  initSearchPath (← findSysroot) extra
  let env ← importModules #[{ module := `B4ClassNumber }, { module := `B4Chi8 }] {} (trustLevel := 0) (loadExts := false)
  for t in targets do
    unless env.contains t do
      IO.eprintln s!"missing target {t}"; return 1
  let cl := closure env targets {}
  let mut m : Std.HashMap Name ConstantInfo := {}
  for n in cl do
    if let some ci := env.find? n then m := m.insert n ci
  IO.println s!"closure: {cl.size} names, {m.size} constants"
  let mut ax : Array Name := #[]
  for (n, ci) in m do
    if let .axiomInfo _ := ci then ax := ax.push n
  IO.println s!"axioms in closure: {ax.qsort Name.lt}"
  let start ← IO.monoMsNow
  let empty ← mkEmptyEnvironment
  let env' ← Kernel.Environment.replay m empty.toKernelEnv
  IO.println s!"kernel replay from empty environment: OK ({(← IO.monoMsNow) - start} ms)"
  for t in targets do
    match env'.find? t, env.find? t with
    | some a, some b =>
      if a.type == b.type then IO.println s!"{t}: replayed, type unchanged"
      else IO.eprintln s!"{t}: TYPE MISMATCH"; return 1
    | _, _ => IO.eprintln s!"{t}: not in replayed environment"; return 1
  IO.println "REPLAY DONE"
  return 0

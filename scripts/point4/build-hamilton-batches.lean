/-
Audit-owned orchestration using official Lake 4.29.0 APIs.
Source-reviewed against leanprover/lean4 commit
98dc76e3c0a9b856c9b98726b713fb04fab16740; not yet compiler-verified.

Run with the real pinned compiler, not the observer executable:
  REAL_LEAN --plugin REAL_SYSROOT/lib/lean/libLake_shared.so --run
    build-hamilton-batches.lean PLAN_JSON EVIDENCE_DIR
Use the existing observed-toolchain environment and upstream root as cwd.
This driver never supplies a compiler command or constructs a ModuleSetup.
-/
import Lake
import Lake.CLI.Build
import Lake.Load.Workspace

open Lean Lake System

structure HamiltonBatch where
  modules : Array String
  chains : Array (Array String)
  deriving FromJson

structure HamiltonPlan where
  batches : Array HamiltonBatch
  deriving FromJson

private def writeJsonAtomic (path : FilePath) (value : Json) : IO Unit := do
  let temporary := FilePath.mk (path.toString ++ s!".tmp-{← IO.Process.getPID}")
  IO.FS.writeFile temporary (value.pretty ++ "\n")
  IO.FS.rename temporary path

private def batchRecordPath (evidence : FilePath) (batch : Nat) : FilePath :=
  let number := toString batch
  let batchPrefix := String.ofList (List.replicate (4 - number.length) '0')
  evidence / "batch-results" / (batchPrefix ++ number ++ ".json")

private def batchTargets (batch : HamiltonBatch) (jobs : Nat) : IO (Array String) := do
  if batch.modules.isEmpty || batch.chains.isEmpty || batch.chains.size > jobs then
    throw <| IO.userError "Empty batch or excess compiler-chain width"
  let mut seen : Array String := #[]
  let mut targets : Array String := #[]
  for chain in batch.chains do
    let some tip := chain.back?
      | throw <| IO.userError "Empty compiler chain"
    for moduleName in chain do
      if seen.contains moduleName || !batch.modules.contains moduleName then
        throw <| IO.userError "Duplicate or out-of-batch chain module"
      seen := seen.push moduleName
    targets := targets.push ("+" ++ tip ++ ":olean")
  if seen.size != batch.modules.size || !batch.modules.all seen.contains then
    throw <| IO.userError "Compiler chains do not cover the batch"
  return targets

private def runBatches
    (ws : Workspace) (plan : HamiltonPlan) (evidence : FilePath) (jobs : Nat)
    : FetchM Unit := do
  let mut batchNumber := 0
  for batch in plan.batches do
    batchNumber := batchNumber + 1
    let targets ← batchTargets batch jobs
    let specs ← (parseTargetSpecs ws targets.toList).adapt (fun e => IO.userError e.toString)
    let recordPath := batchRecordPath evidence batchNumber
    let record := Json.mkObj [
      ("batch", toJson batchNumber), ("targets", toJson targets),
      ("status", toJson "running")]
    writeJsonAtomic (evidence / "active-batch.json") <| Json.mkObj [
      ("batch", toJson batchNumber), ("allowed_modules", toJson batch.modules)]
    writeJsonAtomic recordPath record
    let started ← IO.monoMsNow
    try
      -- Fetch only this bounded batch. Await it before fetching the next.
      -- All iterations share this run's official Lake BuildStore.
      let job ← buildSpecs specs
      let _ ← job.await
      let elapsed := (← IO.monoMsNow) - started
      let finished := record
        |>.setObjVal! "status" (toJson "finished")
        |>.setObjVal! "lake_job_success" (toJson true)
        |>.setObjVal! "elapsed_milliseconds" (toJson elapsed)
      writeJsonAtomic recordPath finished
    catch failure =>
      let elapsed := (← IO.monoMsNow) - started
      let finished := record
        |>.setObjVal! "status" (toJson "finished")
        |>.setObjVal! "lake_job_success" (toJson false)
        |>.setObjVal! "elapsed_milliseconds" (toJson elapsed)
        |>.setObjVal! "error" (toJson "Lake fetch or await failed; see frontend log")
      writeJsonAtomic recordPath finished
      throw failure

def main (args : List String) : IO UInt32 := do
  let [planName, evidenceName] := args
    | throw <| IO.userError "Expected PLAN_JSON EVIDENCE_DIR"
  let planText ← IO.FS.readFile planName
  let plan : HamiltonPlan ← IO.ofExcept (Json.parse planText >>= fromJson?)
  if plan.batches.isEmpty then
    throw <| IO.userError "Empty batch plan"
  let evidence ← IO.FS.realPath evidenceName
  let control ← IO.ofExcept <| Json.parse (← IO.FS.readFile (evidence / "compiler-control.json"))
  let jobs : Nat ← IO.ofExcept (control.getObjValAs? Nat "jobs")
  if jobs != 1 && jobs != 2 then
    throw <| IO.userError "Unsupported compiler worker bound"
  IO.FS.createDirAll (evidence / "batch-results")
  let (elan?, lean?, lake?) ← findInstall?
  let some lean := lean? | throw <| IO.userError "Pinned Lean installation unavailable"
  let some lake := lake? | throw <| IO.userError "Pinned Lake installation unavailable"
  if lean.githash != Lean.githash then
    throw <| IO.userError "Lake and compiler git revisions differ"
  let lakeEnv ← (Env.compute lake lean elan? (some true)).adapt IO.userError
  let loadConfig : LoadConfig := {
    lakeEnv, wsDir := ← IO.currentDir, relConfigFile := "lakefile.toml",
    updateDeps := false, updateToolchain := false }
  let logConfig : LogConfig := { outLv := .warning, ansiMode := .noAnsi }
  let some ws ← (loadWorkspace loadConfig).toBaseIO logConfig
    | throw <| IO.userError "Official Lake workspace load failed"
  let buildConfig : BuildConfig := {
    verbosity := .quiet, outLv := .warning, failLv := .error,
    ansiMode := .noAnsi, showSuccess := false }
  ws.runFetchM (runBatches ws plan evidence jobs) buildConfig
  return 0

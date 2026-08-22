/-!
# A proof-carrying loader and HMR boundary

This module is the finite, executable part of the pinned CORDIS loader paper:
Definition 74's entry record, keyed configuration reconciliation, Algorithm 8's
accepted/declined module classification, and Algorithm 10's transactional reload
order.  The model deliberately does not pretend to perform dynamic imports,
filesystem watching, cache mutation, fiber execution, or rollback of arbitrary
external effects.  Those operations enter through explicit values and proof
obligations at the boundary.

The representation is intentionally small but not merely a classifier: entries
carry the six paper fields, reconciliation emits field-sensitive actions, the
classification loop is executable over a finite import graph, and reload is an
indexed state machine whose failure branch restores the exact pre-reload state.
-/

set_option autoImplicit false

namespace Cordis.LoaderHMR

/-! ## Definition 74: entries and keyed configuration updates -/

abbrev EntryId := String
abbrev Url := String
abbrev AnnotationKey := String
abbrev AnnotationValue := String
abbrev ConfigValue := String

inductive IsolationAnnotation where
  | local
  | global (label : String)
  deriving DecidableEq, Repr

abbrev Isolation := List (AnnotationKey × IsolationAnnotation)
abbrev Interception := List (AnnotationKey × AnnotationValue)

/-- The six fields named by Definition 74, with opaque payloads retained. -/
structure Entry where
  id : EntryId
  url : Url
  isolate : Isolation
  intercept : Interception
  config : ConfigValue
  disabled : Bool
  deriving DecidableEq, Repr

abbrev EntryKey := EntryId

inductive ChangeKind where
  | unchanged
  | rebuild
  | reassignIsolation
  | patchInterception
  | patchConfig
  | disable
  | enable
  deriving DecidableEq, Repr

def changeKind (before after : Entry) : ChangeKind :=
  if before.url != after.url then .rebuild
  else if before.isolate != after.isolate then .reassignIsolation
  else if before.intercept != after.intercept then .patchInterception
  else if before.config != after.config then .patchConfig
  else if before.disabled && !after.disabled then .enable
  else if !before.disabled && after.disabled then .disable
  else .unchanged

inductive ReconcileAction where
  | add (entry : Entry)
  | update (before after : Entry) (kind : ChangeKind)
  | remove (entry : Entry)
  deriving DecidableEq, Repr

def ReconcileAction.key : ReconcileAction → EntryKey
  | .add entry => entry.id
  | .update before _ _ => before.id
  | .remove entry => entry.id

def ReconcileAction.target : ReconcileAction → Option Entry
  | .add entry => some entry
  | .update _ after _ => some after
  | .remove _ => none

def findEntry : List Entry → EntryKey → Option Entry
  | [], _ => none
  | entry :: entries, key => if entry.id = key then some entry else findEntry entries key

def actionFor (before : List Entry) (after : Entry) : ReconcileAction :=
  match findEntry before after.id with
  | none => .add after
  | some previous => .update previous after (changeKind previous after)

def actionsForNew (before after : List Entry) : List ReconcileAction :=
  after.map (actionFor before)

def removalsFor (before after : List Entry) : List ReconcileAction :=
  before.filterMap fun entry =>
    if (findEntry after entry.id).isNone then some (.remove entry) else none

def reconcile (before after : List Entry) : List ReconcileAction :=
  actionsForNew before after ++ removalsFor before after

theorem changeKind_url_rebuild
    (before after : Entry)
    (h : before.url ≠ after.url) :
    changeKind before after = .rebuild := by
  simp [changeKind, h]

theorem changeKind_isolation_reassign
    (before after : Entry)
    (hUrl : before.url = after.url)
    (hIsolation : before.isolate ≠ after.isolate) :
    changeKind before after = .reassignIsolation := by
  simp [changeKind, hUrl, hIsolation]

theorem changeKind_intercept_patch
    (before after : Entry)
    (hUrl : before.url = after.url)
    (hIsolation : before.isolate = after.isolate)
    (hIntercept : before.intercept ≠ after.intercept) :
    changeKind before after = .patchInterception := by
  simp [changeKind, hUrl, hIsolation, hIntercept]

theorem changeKind_config_patch
    (before after : Entry)
    (hUrl : before.url = after.url)
    (hIsolation : before.isolate = after.isolate)
    (hIntercept : before.intercept = after.intercept)
    (hConfig : before.config ≠ after.config) :
    changeKind before after = .patchConfig := by
  simp [changeKind, hUrl, hIsolation, hIntercept, hConfig]

theorem changeKind_disable
    (before after : Entry)
    (hUrl : before.url = after.url)
    (hIsolation : before.isolate = after.isolate)
    (hIntercept : before.intercept = after.intercept)
    (hConfig : before.config = after.config)
    (hDisabled : before.disabled = false)
    (hAfter : after.disabled = true) :
    changeKind before after = .disable := by
  simp [changeKind, hUrl, hIsolation, hIntercept, hConfig, hDisabled, hAfter]

theorem changeKind_enable
    (before after : Entry)
    (hUrl : before.url = after.url)
    (hIsolation : before.isolate = after.isolate)
    (hIntercept : before.intercept = after.intercept)
    (hConfig : before.config = after.config)
    (hDisabled : before.disabled = true)
    (hAfter : after.disabled = false) :
    changeKind before after = .enable := by
  simp [changeKind, hUrl, hIsolation, hIntercept, hConfig, hDisabled, hAfter]

theorem actionFor_existing
    (before : List Entry) (after previous : Entry)
    (h : findEntry before after.id = some previous) :
    actionFor before after = .update previous after (changeKind previous after) := by
  simp [actionFor, h]

theorem actionsForNew_length (before after : List Entry) :
    (actionsForNew before after).length = after.length := by
  simp [actionsForNew]

theorem reconcile_singleton_same
    (before after : Entry)
    (h : before.id = after.id) :
    reconcile [before] [after] =
      [.update before after (changeKind before after)] := by
  simp [reconcile, actionsForNew, actionFor, removalsFor, findEntry, h]

theorem reconcile_singleton_add
    (before after : Entry)
    (h : before.id ≠ after.id) :
    reconcile [before] [after] = [.add after, .remove before] := by
  have h' : after.id ≠ before.id := by
    intro equality
    exact h equality.symm
  simp [reconcile, actionsForNew, actionFor, removalsFor, findEntry, h, h']

/-! ## Algorithm 8: finite module classification -/

structure ModuleGraph where
  imports : Url → List Url

structure Classification where
  accepted : List Url
  declined : List Url
  pending : List Url

def insertUnique (url : Url) : List Url → List Url
  | urls => if url ∈ urls then urls else url :: urls

def unionUnique : List Url → List Url → List Url
  | [], right => right
  | left :: rest, right => unionUnique rest (insertUnique left right)

def difference : List Url → List Url → List Url
  | [], _ => []
  | left :: rest, removed => if left ∈ removed then difference rest removed
    else left :: difference rest removed

def importsOf (graph : ModuleGraph) : List Url → List Url
  | [] => []
  | url :: urls => unionUnique (graph.imports url) (importsOf graph urls)

def initialClassification
    (graph : ModuleGraph) (stashed externals : List Url) : Classification :=
  let accepted := stashed
  let declined := externals
  let pending := difference (importsOf graph stashed) (accepted ++ declined)
  { accepted, declined, pending }

def removeUrl (url : Url) (urls : List Url) : List Url :=
  urls.filter fun candidate => candidate ≠ url

def intersects (left right : List Url) : Bool :=
  left.any fun url => decide (url ∈ right)

def subsetOf (left right : List Url) : Bool :=
  left.all fun url => decide (url ∈ right)

def resolveCandidate
    (graph : ModuleGraph) (state : Classification) (url : Url) :
    Classification × Bool :=
  let rest := { state with pending := removeUrl url state.pending }
  if url ∈ state.accepted || url ∈ state.declined then
    (rest, false)
  else
    let children := graph.imports url
    if intersects children state.accepted then
      ({ rest with accepted := insertUnique url rest.accepted }, true)
    else if subsetOf children state.declined then
      ({ rest with declined := insertUnique url rest.declined }, true)
    else
      let unseen := difference children (state.accepted ++ state.declined)
      ({ rest with pending := unionUnique (insertUnique url rest.pending) unseen },
        !unseen.isEmpty)

def processPending
    (graph : ModuleGraph) : List Url → Classification → Classification × Bool
  | [], state => (state, false)
  | url :: urls, state =>
      let (next, changed) := resolveCandidate graph state url
      let (final, laterChanged) := processPending graph urls next
      (final, changed || laterChanged)

def classifyRound (graph : ModuleGraph) (state : Classification) : Classification × Bool :=
  processPending graph state.pending state

def classifyAux (graph : ModuleGraph) : Nat → Classification → Classification
  | 0, state => { state with declined := unionUnique state.declined state.pending, pending := [] }
  | fuel + 1, state =>
      let (next, changed) := classifyRound graph state
      if changed then classifyAux graph fuel next
      else { next with declined := unionUnique next.declined next.pending, pending := [] }

/-- Algorithm 8 with an explicit finite fuel bound for the graph fixed point. -/
def classify
    (graph : ModuleGraph) (fuel : Nat) (stashed externals : List Url) : Classification :=
  classifyAux graph fuel (initialClassification graph stashed externals)

theorem initialClassification_accepts_stashed
    (graph : ModuleGraph) (stashed externals : List Url) (url : Url)
    (h : url ∈ stashed) :
    url ∈ (initialClassification graph stashed externals).accepted := by
  exact h

theorem classify_zero_has_no_pending
    (graph : ModuleGraph) (stashed externals : List Url) :
    (classify graph 0 stashed externals).pending = [] := by
  rfl

theorem resolveCandidate_accepted
    (graph : ModuleGraph) (state : Classification) (url : Url)
    (hNotAccepted : url ∉ state.accepted)
    (hNotDeclined : url ∉ state.declined)
    (hImported : intersects (graph.imports url) state.accepted = true) :
    (resolveCandidate graph state url).1.accepted = insertUnique url state.accepted := by
  simp [resolveCandidate, hNotAccepted, hNotDeclined, hImported, removeUrl]

theorem resolveCandidate_declined
    (graph : ModuleGraph) (state : Classification) (url : Url)
    (hNotAccepted : url ∉ state.accepted)
    (hNotDeclined : url ∉ state.declined)
    (hImported : intersects (graph.imports url) state.accepted = false)
    (hAllDeclined : subsetOf (graph.imports url) state.declined = true) :
    (resolveCandidate graph state url).1.declined = insertUnique url state.declined := by
  simp [resolveCandidate, hNotAccepted, hNotDeclined, hImported, hAllDeclined, removeUrl]

/-! ## Algorithm 9: stale-entry detection with a declined boundary -/

def reachAux
    (graph : ModuleGraph) (declined : List Url) :
    Nat → List Url → List Url → List Url
  | 0, seen, _ => seen
  | _fuel + 1, seen, [] => seen
  | fuel + 1, seen, url :: work =>
      if url ∈ seen || url ∈ declined then
        reachAux graph declined fuel seen work
      else
        reachAux graph declined fuel (insertUnique url seen) (graph.imports url ++ work)

/-- Transitive imports of an entry, stopping at modules already classified declined. -/
def dependencies
    (graph : ModuleGraph) (declined : List Url) (fuel : Nat) (root : Url) : List Url :=
  if root ∈ declined then []
  else insertUnique root (reachAux graph declined fuel [] (graph.imports root))

def staleEntry
    (graph : ModuleGraph) (accepted declined : List Url) (fuel : Nat) (entry : Entry) : Bool :=
  intersects (dependencies graph declined fuel entry.url) accepted

def detectStale
    (graph : ModuleGraph) (accepted declined : List Url) (fuel : Nat)
    (entries : List Entry) : List Entry :=
  entries.filter (staleEntry graph accepted declined fuel)

theorem dependencies_root_mem
    (graph : ModuleGraph) (declined : List Url) (fuel : Nat) (root : Url)
    (hDeclined : root ∉ declined) :
    root ∈ dependencies graph declined fuel root := by
  unfold dependencies
  simp only [if_neg hDeclined]
  by_cases hMem : root ∈ reachAux graph declined fuel [] (graph.imports root)
  · simp [insertUnique, hMem]
  · simp [insertUnique, hMem]

theorem staleEntry_iff_import_intersects
    (graph : ModuleGraph) (accepted declined : List Url) (fuel : Nat) (entry : Entry) :
    staleEntry graph accepted declined fuel entry =
      intersects (dependencies graph declined fuel entry.url) accepted := by
  rfl

/-! ## Transactional reload -/

inductive ReloadPhase where
  | ready
  | invalidated
  | imported
  | disposed
  | installed
  | committed
  | rolledBack
  deriving DecidableEq, Repr

structure CacheEntry where
  url : Url
  module : String
  deriving DecidableEq, Repr

structure ReloadState where
  entry : Entry
  cache : List CacheEntry
  fiber : Option Nat
  deriving DecidableEq, Repr

structure InvalidatedState where
  ready : ReloadState
  backup : List CacheEntry

structure ImportedState where
  invalidated : InvalidatedState
  replacement : String

structure DisposedState where
  imported : ImportedState

structure InstalledState where
  disposed : DisposedState
  fiber : Nat

structure CommittedState where
  installed : InstalledState
  state : ReloadState

structure RolledBackState where
  invalidated : InvalidatedState
  state : ReloadState

def invalidate (ready : ReloadState) : InvalidatedState :=
  { ready, backup := ready.cache }

def importReplacement
    (loader : Url → Except String String)
    (state : InvalidatedState) :
    Except String ImportedState := do
  let replacement ← loader state.ready.entry.url
  pure { invalidated := state, replacement }

def dispose (state : ImportedState) : DisposedState :=
  { imported := state }

def install (state : DisposedState) (fiber : Nat) : InstalledState :=
  { disposed := state, fiber }

def commit (state : InstalledState) : CommittedState :=
  let old := state.disposed.imported.invalidated.ready
  let replacement := state.disposed.imported.replacement
  let cache := CacheEntry.mk old.entry.url replacement ::
    old.cache.filter fun cached => cached.url ≠ old.entry.url
  { installed := state
    state := { old with cache, fiber := some state.fiber } }

def rollback (state : InvalidatedState) : RolledBackState :=
  { invalidated := state, state := { state.ready with cache := state.backup } }

inductive ReloadResult where
  | success (state : CommittedState)
  | failure (error : String) (state : RolledBackState)

def transactionalReload
    (loader : Url → Except String String)
    (ready : ReloadState)
    (fiber : Nat) : ReloadResult :=
  let invalidated := invalidate ready
  match importReplacement loader invalidated with
  | .error error => .failure error (rollback invalidated)
  | .ok imported =>
      .success (commit (install (dispose imported) fiber))

def ReloadResult.phaseTrace : ReloadResult → List ReloadPhase
  | .success _ => [.ready, .invalidated, .imported, .disposed, .installed, .committed]
  | .failure _ _ => [.ready, .invalidated, .rolledBack]

theorem phaseTrace_success
    (loader : Url → Except String String)
    (ready : ReloadState) (fiber : Nat) (replacement : String)
    (h : loader ready.entry.url = .ok replacement) :
    (transactionalReload loader ready fiber).phaseTrace =
      [.ready, .invalidated, .imported, .disposed, .installed, .committed] := by
  unfold transactionalReload importReplacement
  simp only [invalidate]
  rw [h]
  rfl

theorem phaseTrace_failure
    (loader : Url → Except String String)
    (ready : ReloadState) (fiber : Nat) (error : String)
    (h : loader ready.entry.url = .error error) :
    (transactionalReload loader ready fiber).phaseTrace =
      [.ready, .invalidated, .rolledBack] := by
  unfold transactionalReload importReplacement
  simp only [invalidate]
  rw [h]
  rfl

theorem rollback_exact
    (loader : Url → Except String String)
    (ready : ReloadState) (fiber : Nat) (error : String)
    (h : loader ready.entry.url = .error error) :
    match transactionalReload loader ready fiber with
    | .failure _ result => result.state = ready
    | .success _ => False := by
  unfold transactionalReload importReplacement
  simp only [invalidate]
  rw [h]
  rfl

/-! ## Executable examples -/

namespace Example

def entry : Entry := {
  id := "counter"
  url := "file:///counter.js"
  isolate := [("counter", .local)]
  intercept := [("logger", "warn")]
  config := "{enabled:true}"
  disabled := false
}

def updatedEntry : Entry := { entry with config := "{enabled:false}" }

def loader : Url → Except String String
  | "file:///counter.js" => .ok "counter-v2"
  | url => .error ("unknown module: " ++ url)

def badLoader : Url → Except String String
  | "file:///counter.js" => .error "syntax error"
  | url => .error ("unknown module: " ++ url)

def graph : ModuleGraph where
  imports
    | "changed.js" => ["plugin.js"]
    | "plugin.js" => []
    | _ => []

def classified : Classification := classify graph 2 ["changed.js"] ["framework.js"]

def staleGraph : ModuleGraph where
  imports
    | "file:///counter.js" => ["changed.js"]
    | "changed.js" => []
    | _ => []

def staleEntries : List Entry := detectStale staleGraph ["changed.js"] ["framework.js"] 3 [entry]

def declinedBoundaryEntries : List Entry :=
  detectStale staleGraph ["changed.js"] ["changed.js"] 3 [entry]

def cycleGraph : ModuleGraph where
  imports
    | "source.js" => ["left.js"]
    | "left.js" => ["right.js"]
    | "right.js" => ["left.js"]
    | _ => []

def cycleClassified : Classification := classify cycleGraph 4 ["source.js"] []

def ready : ReloadState := {
  entry
  cache := [{ url := entry.url, module := "counter-v1" }]
  fiber := some 7
}

theorem config_update_is_patch :
    changeKind entry updatedEntry = .patchConfig := by
  simp [entry, updatedEntry, changeKind]

theorem reconciliation_is_keyed :
    reconcile [entry] [updatedEntry] = [.update entry updatedEntry .patchConfig] := by
  calc
    reconcile [entry] [updatedEntry] =
        [.update entry updatedEntry (changeKind entry updatedEntry)] :=
      reconcile_singleton_same entry updatedEntry (by rfl)
    _ = [.update entry updatedEntry .patchConfig] := by
      rw [config_update_is_patch]

theorem reload_success :
    (transactionalReload loader ready 8).phaseTrace =
      [.ready, .invalidated, .imported, .disposed, .installed, .committed] := by
  apply phaseTrace_success
  rfl

theorem reload_failure_restores :
    match transactionalReload badLoader ready 8 with
    | .failure _ result => result.state = ready
    | .success _ => False := by
  simpa [badLoader] using (rollback_exact badLoader ready 8 "syntax error" (by rfl))

theorem classification_fixed_point :
    classified.accepted = ["changed.js"] ∧
      classified.declined = ["framework.js", "plugin.js"] ∧
      classified.pending = [] := by
  decide

theorem stale_entry_detected : staleEntries = [entry] := by
  decide

theorem declined_boundary_stops_walk : declinedBoundaryEntries = [] := by
  decide

theorem unresolved_cycle_defaults_declined :
    cycleClassified.accepted = ["source.js"] ∧
      cycleClassified.declined = ["right.js", "left.js"] ∧
      cycleClassified.pending = [] := by
  decide

end Example

end Cordis.LoaderHMR

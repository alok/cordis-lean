import Cordis.Codec
import Cordis.Effect
import Cordis.Harness
import Cordis.Lifecycle
import Cordis.Policy
import Cordis.Registry

/-!
# Headline theorem axiom audit

Building this module prints the logical dependencies of the guarantees exposed
by the verified kernel. The repository audit separately rejects project-defined
axioms and proof placeholders.
-/

#print axioms Cordis.Codec.decode_encode
#print axioms Cordis.Effect.seq_recovers
#print axioms Cordis.Effect.seq_assoc
#print axioms Cordis.UndoStack.recover_after
#print axioms Cordis.Observational.Effect.seq_recovers
#print axioms Cordis.Registry.setAt_restore
#print axioms Cordis.Registry.setAt_commute
#print axioms Cordis.Registry.setEffect_recovers
#print axioms Cordis.Registry.setEffect_commute
#print axioms Cordis.View.provider_present
#print axioms Cordis.Decision.denied_never_allows
#print axioms Cordis.LeasePool.consumed_absent
#print axioms Cordis.LeasePool.consume_after_consumed
#print axioms Cordis.LeasePool.cannot_consume_twice
#print axioms Cordis.PolicyTransition.denied_cannot_dispatch
#print axioms Cordis.PolicyTransition.dispatched_lease_absent
#print axioms Cordis.ToolWire.validate_declared
#print axioms Cordis.Event.noOrphanResult
#print axioms Cordis.applyRaw_eraseEvent
#print axioms Cordis.replayRaw_eraseTrace
#print axioms Cordis.Lifecycle.Transition.unload_recovers
#print axioms Cordis.Lifecycle.Transition.unload_rejects_relied
#print axioms Cordis.Harness.replayRaw_append
#print axioms Cordis.Harness.certifiedTwoCallTrace_replays

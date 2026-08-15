import Cordis.Batch
import Cordis.Codec
import Cordis.Effect
import Cordis.Harness
import Cordis.Lifecycle
import Cordis.Policy
import Cordis.Registry
import Cordis.Stream

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
#print axioms Cordis.Effect.IndependentAt.seq_applied_eq
#print axioms Cordis.CertifiedTwoBatch.execute_order_irrelevant
#print axioms Cordis.CertifiedTwoBatch.execute_outputs_in_model_order
#print axioms Cordis.CertifiedTwoBatch.execute_recovers
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
#print axioms Cordis.SubjectPolicyTransition.dispatched_lease_absent
#print axioms Cordis.SubjectPolicyTrace.dispatchCount_le_one
#print axioms Cordis.SubjectPolicyTrace.dispatchCount_to_completed
#print axioms Cordis.SubjectPolicyTrace.cannot_dispatch_twice
#print axioms Cordis.SubjectPolicyTrace.denied_dispatchCount_eq_zero
#print axioms Cordis.ToolWire.validate_declared
#print axioms Cordis.ToolWire.decode_encoded_result
#print axioms Cordis.ToolWire.decode_encoded_certified_result
#print axioms Cordis.Event.noOrphanResult
#print axioms Cordis.applyRaw_eraseEvent
#print axioms Cordis.ValidatedEvent.applies
#print axioms Cordis.replayRaw_eraseTrace
#print axioms Cordis.ValidatedTrace.replays
#print axioms Cordis.Stream.noChunkAfterFinished
#print axioms Cordis.Stream.replayRaw_eraseTrace
#print axioms Cordis.Stream.replay_completeTrace
#print axioms Cordis.Lifecycle.Transition.unload_recovers
#print axioms Cordis.Lifecycle.Transition.unload_rejects_relied
#print axioms Cordis.Harness.replayRaw_append
#print axioms Cordis.Harness.RecordChain.length_eq_nextCall
#print axioms Cordis.Harness.RecordChain.ids_eq_range
#print axioms Cordis.Harness.certifiedTwoCallTrace_replays

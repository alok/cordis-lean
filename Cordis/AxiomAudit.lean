import Cordis.Batch
import Cordis.Codec
import Cordis.Effect
import Cordis.Examples.DependentChoice
import Cordis.Harness
import Cordis.Lifecycle
import Cordis.Policy
import Cordis.Registry
import Cordis.Session
import Cordis.Stream

/-!
# Headline theorem axiom audit

Building this module prints the logical dependencies of the guarantees exposed
by the verified kernel. The repository audit separately rejects project-defined
axioms and proof placeholders.
-/

set_option format.width 200

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
#print axioms Cordis.Decision.tighten_associative
#print axioms Cordis.LeasePool.consumed_absent
#print axioms Cordis.LeasePool.consume_after_consumed
#print axioms Cordis.LeasePool.cannot_consume_twice
#print axioms Cordis.LeasePool.consume_after_issue_restores
#print axioms Cordis.PolicyTransition.denied_cannot_dispatch
#print axioms Cordis.PolicyTransition.dispatched_lease_absent
#print axioms Cordis.SubjectPolicyTransition.dispatched_lease_absent
#print axioms Cordis.SubjectPolicyTransition.denied_cannot_dispatch
#print axioms Cordis.SubjectPolicyTransition.phase_strict
#print axioms Cordis.SubjectPolicyTrace.dispatchCount_le_one
#print axioms Cordis.SubjectPolicyTrace.dispatchCount_to_completed
#print axioms Cordis.SubjectPolicyTrace.cannot_dispatch_twice
#print axioms Cordis.SubjectPolicyTrace.denied_dispatchCount_eq_zero
#print axioms Cordis.SubjectPolicyTrace.phase_monotone
#print axioms Cordis.ToolWire.validate_declared
#print axioms Cordis.ToolWire.decode_encoded_result
#print axioms Cordis.ToolWire.decode_encoded_certified_result
#print axioms Cordis.Event.noOrphanResult
#print axioms Cordis.Event.preservesWellFormed
#print axioms Cordis.applyRaw_eraseEvent
#print axioms Cordis.ValidatedEvent.applies
#print axioms Cordis.replayRaw_eraseTrace
#print axioms Cordis.ValidatedTrace.replays
#print axioms Cordis.Stream.noChunkAfterFinished
#print axioms Cordis.Stream.replayRaw_eraseTrace
#print axioms Cordis.Stream.replay_completeTrace
#print axioms Cordis.Lifecycle.Transition.unload_recovers
#print axioms Cordis.Lifecycle.Transition.unload_rejects_relied
#print axioms Cordis.Lifecycle.Transition.active_successor_keeps_view
#print axioms Cordis.Lifecycle.not_withdrawable_of_relied
#print axioms Cordis.Harness.replayRaw_append
#print axioms Cordis.Harness.RecordChain.length_eq_nextCall
#print axioms Cordis.Harness.RecordChain.ids_eq_range
#print axioms Cordis.Harness.RecordChain.boundaries_eq_records
#print axioms Cordis.Harness.RecordChain.leases_threaded
#print axioms Cordis.Harness.RunnerState.callBoundaries_eq_records
#print axioms Cordis.Harness.RunnerState.leases_threaded
#print axioms Cordis.Harness.RunnerState.protocolProjection_eq_log
#print axioms Cordis.Harness.RunnerState.protocolProjection_replays
#print axioms Cordis.Harness.certifiedTwoCallTrace_replays
#print axioms Cordis.GenericHarness.CallEvidence.policyRejected_dispatchCount_eq_zero
#print axioms Cordis.GenericHarness.CallEvidence.completed_dispatchCount_eq_one
#print axioms Cordis.GenericHarness.CallEvidence.completed_terminal_lease_absent
#print axioms Cordis.GenericHarness.CallEvidence.leases_restored
#print axioms Cordis.GenericHarness.RecordChain.length_eq_nextCall
#print axioms Cordis.GenericHarness.RecordChain.ids_eq_range
#print axioms Cordis.GenericHarness.RecordChain.boundaries_eq_records
#print axioms Cordis.GenericHarness.RecordChain.models_threaded
#print axioms Cordis.GenericHarness.RecordChain.leases_threaded
#print axioms Cordis.GenericHarness.Runner.records_length_eq_nextCall
#print axioms Cordis.GenericHarness.Runner.ids_eq_range
#print axioms Cordis.GenericHarness.Runner.models_threaded
#print axioms Cordis.GenericHarness.Runner.callBoundaries_eq_records
#print axioms Cordis.GenericHarness.Runner.leases_threaded
#print axioms Cordis.GenericHarness.Runner.beginTurn_log
#print axioms Cordis.GenericHarness.Runner.beginStep_log
#print axioms Cordis.GenericHarness.Runner.finishStep_log
#print axioms Cordis.GenericHarness.Runner.finishTurn_log
#print axioms Cordis.Session.SurfaceTransition.replacement_exact_shadow
#print axioms Cordis.Session.SurfaceTransition.replacement_coverage
#print axioms Cordis.Session.ValidLog.length_eq_nextSeq
#print axioms Cordis.Session.ValidLog.seqs_eq_range
#print axioms Cordis.Session.ValidLog.surface_nodup
#print axioms Cordis.Session.ValidLog.surface_references_earlier
#print axioms Cordis.Session.ValidLog.latest_header_eq
#print axioms Cordis.Session.ProtocolCertificate.replays
#print axioms Cordis.Session.Session.protocolProjection_appendRequestHeader
#print axioms Cordis.Session.Session.protocolProjection_appendUserMessage
#print axioms Cordis.Session.Session.protocolProjection_appendAssistantMessage
#print axioms Cordis.Session.certifiedSession_messages
#print axioms Cordis.Session.certifiedSession_protocol_replays
#print axioms Cordis.Session.certifiedSession_request_values
#print axioms Cordis.Session.replacementSession_messages
#print axioms Cordis.Session.replacementSession_sources_cover_shadowed
#print axioms Cordis.Examples.DependentChoice.request_selects_exact_output_type
#print axioms Cordis.Examples.DependentChoice.allowed_call_has_typed_encoded_result
#print axioms Cordis.Examples.DependentChoice.label_call_is_exact_policy_rejection
#print axioms Cordis.Examples.DependentChoice.rejected_call_has_zero_dispatches
#print axioms Cordis.Examples.DependentChoice.rejected_call_preserves_model

import Cordis.Batch
import Cordis.Codec
import Cordis.Coeffect
import Cordis.Effect
import Cordis.Examples.DependentChoice
import Cordis.Harness
import Cordis.Lifecycle
import Cordis.Policy
import Cordis.Registry
import Cordis.RichStream
import Cordis.Schedule
import Cordis.Session
import Cordis.SessionValidation
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
#print axioms Cordis.Session.ValidatedSuffix.events_eq
#print axioms Cordis.Session.replacementEvent_revalidates
#print axioms Cordis.Session.wrongSequenceEvent_rejected
#print axioms Cordis.Session.missingStartEvent_rejected
#print axioms Cordis.Session.missingEndEvent_rejected
#print axioms Cordis.Session.incompleteCoverageEvent_rejected
#print axioms Cordis.Session.shortRawLog_validates
#print axioms Cordis.Coeffect.removeAt_setAt_of_absent
#print axioms Cordis.Coeffect.setAt_removeAt_of_present
#print axioms Cordis.Coeffect.setAt_commute
#print axioms Cordis.Coeffect.setEffect_recovers
#print axioms Cordis.Coeffect.CoeffectAt.lift_recovers
#print axioms Cordis.Coeffect.activating_iff
#print axioms Cordis.Coeffect.deactivating_iff
#print axioms Cordis.Coeffect.neutral_iff
#print axioms Cordis.Coeffect.notify_exhaustive
#print axioms Cordis.Coeffect.setting_unrelated_key_is_neutral
#print axioms Cordis.Coeffect.removing_unrelated_key_is_neutral
#print axioms Cordis.Coeffect.setting_last_missing_key_activates
#print axioms Cordis.Coeffect.removing_required_key_deactivates
#print axioms Cordis.Schedule.seq_commute
#print axioms Cordis.Schedule.runEffects_eq_of_perm
#print axioms Cordis.Schedule.CertifiedSchedule.effect_eq
#print axioms Cordis.Schedule.CertifiedSchedule.after_eq
#print axioms Cordis.Schedule.CertifiedSchedule.undo_eq
#print axioms Cordis.Schedule.CertifiedSchedule.recovers
#print axioms Cordis.Schedule.example_orders_equal
#print axioms Cordis.Schedule.reverseSchedule_recovers
#print axioms Cordis.RichStream.AlignedMetadata.hasFinalBlockCount
#print axioms Cordis.RichStream.noEventAfterTerminal
#print axioms Cordis.RichStream.noFinishWithoutUsage
#print axioms Cordis.RichStream.applyRaw_eraseEvent
#print axioms Cordis.RichStream.replayRaw_eraseTrace
#print axioms Cordis.RichStream.ValidatedChunk.applyRaw_eq
#print axioms Cordis.RichStream.ValidatedTrace.replayRaw_eq
#print axioms Cordis.RichStream.validate_interleaved_exact
#print axioms Cordis.RichStream.replay_interleaved_exact
#print axioms Cordis.RichStream.interleaved_rawArgumentsExact
#print axioms Cordis.RichStream.interleaved_metadataAligned
#print axioms Cordis.RichStream.reject_metadataLengthMismatch
#print axioms Cordis.RichStream.reject_afterErrorFinish
#print axioms Cordis.RichStream.reject_afterAbortFinish

import Cordis.Batch
import Cordis.Codec
import Cordis.Coeffect
import Cordis.CoeffectQuotient
import Cordis.ContextualEquivalence
import Cordis.Effect
import Cordis.Examples.DependentChoice
import Cordis.GlobalCalculus
import Cordis.GlobalDynamics
import Cordis.GlobalLifecycle
import Cordis.GlobalRegistry
import Cordis.GlobalTraceFacts
import Cordis.Harness
import Cordis.Lifecycle
import Cordis.MediatedIndependence
import Cordis.MediatedTheorem
import Cordis.OperationIndependence
import Cordis.OperationalEquivalence
import Cordis.Policy
import Cordis.QuotientEffect
import Cordis.Registry
import Cordis.Removal
import Cordis.RichStream
import Cordis.RuntimeRefinement
import Cordis.Schedule
import Cordis.Session
import Cordis.SessionRefinement
import Cordis.SessionValidation
import Cordis.Stream
import Cordis.StreamSession
import Cordis.Transformation
import Cordis.UnifiedContext

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
#print axioms Cordis.StreamSession.toSessionToolCalls_length
#print axioms Cordis.StreamSession.interleavedPayload_exact
#print axioms Cordis.StreamSession.bridgedSession_messages
#print axioms Cordis.StreamSession.interleaved_assignment_is_unique
#print axioms Cordis.Coeffect.Observational.related_iff
#print axioms Cordis.Coeffect.Observational.contextSetoid
#print axioms Cordis.Coeffect.Observational.setAt_related
#print axioms Cordis.Coeffect.Observational.removeAt_related
#print axioms Cordis.Coeffect.Observational.setApplied_recovers
#print axioms Cordis.Coeffect.Observational.satisfies_iff_of_related
#print axioms Cordis.Coeffect.Observational.notify_eq_of_related
#print axioms Cordis.Coeffect.Observational.Example.left_related_right
#print axioms Cordis.UnifiedContext.InPlace.recover_eq
#print axioms Cordis.UnifiedContext.Derived.discard_eq
#print axioms Cordis.UnifiedContext.updateAt_commute
#print axioms Cordis.UnifiedContext.IsolatedContext.resolve_isolate_same
#print axioms Cordis.UnifiedContext.IsolatedContext.resolve_isolate_other
#print axioms Cordis.UnifiedContext.IsolatedContext.isolate_reassign
#print axioms Cordis.UnifiedContext.IsolatedContext.isolate_commute
#print axioms Cordis.UnifiedContext.IsolatedContext.setEffect_recovers
#print axioms Cordis.UnifiedContext.InterceptionContext.intercept_same
#print axioms Cordis.UnifiedContext.InterceptionContext.intercept_commute
#print axioms Cordis.UnifiedContext.InterceptionContext.get_intercept_assoc
#print axioms Cordis.UnifiedContext.InterceptionContext.setEffect_recovers
#print axioms Cordis.UnifiedContext.approximation_zero
#print axioms Cordis.UnifiedContext.approximation_succ
#print axioms Cordis.UnifiedContext.Layer.record_twice_recovers
#print axioms Cordis.UnifiedContext.Layer.liftCoeffect_recovers
#print axioms Cordis.UnifiedContext.pushApproximation_discard
#print axioms Cordis.RuntimeRefinement.WireUsage.toLocal
#print axioms Cordis.RuntimeRefinement.ValidatedJsonTrace.replay_eq
#print axioms Cordis.RuntimeRefinement.decode_example_exact
#print axioms Cordis.RuntimeRefinement.validate_example_exact
#print axioms Cordis.RuntimeRefinement.example_optionalUsage_normalization
#print axioms Cordis.RuntimeRefinement.reject_opaqueReplayState
#print axioms Cordis.RuntimeRefinement.reject_unmodeledErrorFinish
#print axioms Cordis.RuntimeRefinement.reject_unmodeledAbortedFinish
#print axioms Cordis.RuntimeRefinement.reject_semantic_noncontiguousStart
#print axioms Cordis.RuntimeRefinement.reject_unmodeledImageBlock
#print axioms Cordis.RuntimeRefinement.reject_unmodeledToolResultBlock
#print axioms Cordis.RuntimeRefinement.decode_toolCallDelta_exact
#print axioms Cordis.RuntimeRefinement.reject_nestedFieldType
#print axioms Cordis.RuntimeRefinement.reject_unsafeInteger
#print axioms Cordis.Observational.Quotient.Respects.comp
#print axioms Cordis.Observational.Quotient.MapRelated.comp
#print axioms Cordis.Observational.Quotient.AppliedRelated.trans
#print axioms Cordis.Observational.Quotient.Admissible.seq
#print axioms Cordis.Observational.Quotient.Program.run_admissible
#print axioms Cordis.Observational.Quotient.Program.accumulated_inverse_respects
#print axioms Cordis.Observational.Quotient.Program.recovers
#print axioms Cordis.Observational.Quotient.ofExact_admissible
#print axioms Cordis.Observational.Quotient.Example.program_recovers
#print axioms Cordis.Coeffect.Quotient.undoAt_related
#print axioms Cordis.Coeffect.Quotient.lift_results_related
#print axioms Cordis.Coeffect.Quotient.liftApplied
#print axioms Cordis.Coeffect.Quotient.Example.counter_lifts_related
#print axioms Cordis.OperationalEquivalence.indistinguishableSetoid
#print axioms Cordis.OperationalEquivalence.indistinguishable_admissible
#print axioms Cordis.OperationalEquivalence.contained_in_indistinguishable
#print axioms Cordis.OperationalEquivalence.declaredEquivalence_admissible
#print axioms Cordis.OperationalEquivalence.declaredEquivalence_contained
#print axioms Cordis.OperationalEquivalence.withOperationalEquivalence
#print axioms Cordis.OperationalEquivalence.Example.initial_not_indistinguishable_from_bumped
#print axioms Cordis.OperationalEquivalence.Example.leftContext_related_renamedContext
#print axioms Cordis.OperationalEquivalence.PairedGap.seeds_indistinguishable
#print axioms Cordis.OperationalEquivalence.PairedGap.pairedInverseCoherent_fails
#print axioms Cordis.SessionRefinement.RefinedEvent.projection_exact
#print axioms Cordis.SessionRefinement.RefinedEvent.events_eq
#print axioms Cordis.SessionRefinement.ValidatedSequence.protocolTrace_erase
#print axioms Cordis.SessionRefinement.ValidatedSequence.sessionProjection_eq
#print axioms Cordis.SessionRefinement.ValidatedJsonLog.projection_exact
#print axioms Cordis.SessionRefinement.validate_example
#print axioms Cordis.SessionRefinement.example_turnEndStep_isDerived
#print axioms Cordis.SessionRefinement.reject_surfaceMetadataOnStepStart
#print axioms Cordis.SessionRefinement.reject_ignorableCoreEvent
#print axioms Cordis.SessionRefinement.reject_unmodeledTurnEndReason
#print axioms Cordis.SessionRefinement.reject_mismatchedToolResultIds
#print axioms Cordis.SessionRefinement.reject_underdeterminedTurnEnd
#print axioms Cordis.Transformation.Closure.commute
#print axioms Cordis.Transformation.commute_of_generators
#print axioms Cordis.Transformation.seq_monoid_subset_joint
#print axioms Cordis.Transformation.inverseStable_of_generators
#print axioms Cordis.Transformation.Independent.of_generators
#print axioms Cordis.Transformation.Independent.independentAt
#print axioms Cordis.Transformation.Independent.seq_commute
#print axioms Cordis.Transformation.Example.either_order_same
#print axioms Cordis.OperationIndependence.outcomeStable_of_generators
#print axioms Cordis.OperationIndependence.ExactOperationIndependent.of_generators
#print axioms Cordis.OperationIndependence.ExactOperationIndependent.seq_effect_eq
#print axioms Cordis.OperationIndependence.applyLocal_commute
#print axioms Cordis.OperationIndependence.inspectForwardAt_stable_of_other
#print axioms Cordis.OperationIndependence.distinctKeys_finiteIndependent
#print axioms Cordis.OperationIndependence.Computation.run_recovers
#print axioms Cordis.OperationIndependence.Example.Exact.independent
#print axioms Cordis.OperationIndependence.Example.ForwardOnlyGap.inverse_stability_fails
#print axioms Cordis.GlobalRegistry.WellFormed.activeProvider_unique
#print axioms Cordis.GlobalRegistry.WellFormed.activeValue_unique
#print axioms Cordis.GlobalRegistry.activeContext_value_iff
#print axioms Cordis.GlobalRegistry.IsTargetView.unique
#print axioms Cordis.GlobalRegistry.targetView_sound
#print axioms Cordis.GlobalRegistry.targetView_eq_of_isTarget
#print axioms Cordis.GlobalRegistry.preserve_insert
#print axioms Cordis.GlobalRegistry.preserve_retire
#print axioms Cordis.GlobalRegistry.preserve_remove
#print axioms Cordis.GlobalRegistry.OrchestrationStep.preservesWellFormed
#print axioms Cordis.GlobalRegistry.Ancestor.birth_lt
#print axioms Cordis.GlobalRegistry.parent_acyclic
#print axioms Cordis.GlobalRegistry.Trace.preservesWellFormed
#print axioms Cordis.GlobalRegistry.Example.orchestrationTrace_preserves
#print axioms Cordis.Removal.execution_retainedInverses
#print axioms Cordis.Removal.RemovalTrace.step
#print axioms Cordis.Removal.buildRemovalTrace
#print axioms Cordis.Removal.removal_forward_relation
#print axioms Cordis.Removal.removal_inverse_relation
#print axioms Cordis.Removal.later_inverses_unchanged
#print axioms Cordis.Removal.RemovalTrace.suffix_occurrence_has_inverseAgreement
#print axioms Cordis.Removal.applyMaps_eq_of_perm
#print axioms Cordis.Removal.reverse_yieldedInverses_recovers
#print axioms Cordis.Removal.headInverse_commutes_yielded
#print axioms Cordis.Removal.yieldedInverses_commuting
#print axioms Cordis.Removal.inverse_permutation_recovers
#print axioms Cordis.Removal.Example.pairwise
#print axioms Cordis.Removal.Example.inverseOrder_permutation
#print axioms Cordis.MediatedIndependence.RealizedPath.run_eq_some
#print axioms Cordis.MediatedIndependence.ObservationalMediatedClosure.toExact
#print axioms Cordis.MediatedIndependence.Counterexample.results_related
#print axioms Cordis.MediatedIndependence.Counterexample.sequential_results_related
#print axioms Cordis.MediatedIndependence.Counterexample.exact_mediatedClosure_fails
#print axioms Cordis.MediatedIndependence.Counterexample.representative_coherence_fails
#print axioms Cordis.MediatedIndependence.BranchExample.firstStage_outcome
#print axioms Cordis.MediatedIndependence.BranchExample.path
#print axioms Cordis.MediatedTheorem.PairwiseOverlap.left_continuation
#print axioms Cordis.MediatedTheorem.liftedInverses_commute
#print axioms Cordis.MediatedTheorem.stageInterchangeComplete
#print axioms Cordis.MediatedTheorem.stageOutcomeAlignment
#print axioms Cordis.MediatedTheorem.swap_executed_stages
#print axioms Cordis.MediatedTheorem.evaluate_step
#print axioms Cordis.MediatedTheorem.rawStage_interchange
#print axioms Cordis.MediatedTheorem.rawStage_movesAcross
#print axioms Cordis.MediatedTheorem.rawComputation_swap_success
#print axioms Cordis.MediatedTheorem.evaluateSequential_commute
#print axioms Cordis.MediatedTheorem.RawMediatedIndependence.toBoundedPartial
#print axioms Cordis.MediatedTheorem.pairwiseOverlap_boundedPartialIndependence
#print axioms Cordis.MediatedTheorem.partialPairwiseOverlapComplete
#print axioms Cordis.MediatedTheorem.Example.old_pairwiseOverlapComplete_fails
#print axioms Cordis.MediatedTheorem.Example.IndependentBranching.overlap
#print axioms Cordis.MediatedTheorem.Example.IndependentBranching.independent
#print axioms Cordis.GlobalDynamics.Dynamics.applyUndo_respects
#print axioms Cordis.GlobalDynamics.Dynamics.recover_respects
#print axioms Cordis.GlobalDynamics.Dynamics.recover_append
#print axioms Cordis.GlobalDynamics.RegistrationAdmission.after_wellFormed
#print axioms Cordis.GlobalDynamics.IterationStep.preservesWellFormed
#print axioms Cordis.GlobalDynamics.executeOne
#print axioms Cordis.GlobalDynamics.Accumulator.seq
#print axioms Cordis.GlobalDynamics.Trace.preservesWellFormed
#print axioms Cordis.GlobalDynamics.RunResult.recovers
#print axioms Cordis.GlobalDynamics.RunResult.preservesWellFormed
#print axioms Cordis.GlobalDynamics.Example.ordinary_then_registration
#print axioms Cordis.GlobalDynamics.Example.one_fuel_retains_next_code
#print axioms Cordis.GlobalDynamics.Example.complete_run_recovers_ambient
#print axioms Cordis.GlobalLifecycle.setPhase_inactive_preserves
#print axioms Cordis.GlobalLifecycle.Landing.committedSafe
#print axioms Cordis.GlobalLifecycle.Transition.preservesWellFormed
#print axioms Cordis.GlobalLifecycle.Transition.rule_inventory
#print axioms Cordis.GlobalLifecycle.Transition.iterator_map_iff
#print axioms Cordis.GlobalLifecycle.Transition.recovery_map_iff
#print axioms Cordis.GlobalLifecycle.Trace.preservesWellFormed
#print axioms Cordis.GlobalLifecycle.Example.firstStep_executed
#print axioms Cordis.GlobalLifecycle.Example.finalStep_executed
#print axioms Cordis.GlobalLifecycle.Example.bridgedPath_wellFormed
#print axioms Cordis.GlobalLifecycle.Example.unloaded_phase_exact
#print axioms Cordis.GlobalLifecycle.Example.unloaded_ambient_exact
#print axioms Cordis.GlobalLifecycle.Example.stable_leave_guard_rejected
#print axioms Cordis.GlobalLifecycle.Example.abort_guard_rejected
#print axioms Cordis.GlobalLifecycle.Example.raise_guard_rejected
#print axioms Cordis.GlobalCalculus.allRules_nodup
#print axioms Cordis.GlobalCalculus.Step.actor_exact
#print axioms Cordis.GlobalCalculus.Step.orchestration_map_identity
#print axioms Cordis.GlobalCalculus.Step.identity_map_iff_footprint
#print axioms Cordis.GlobalCalculus.Step.recovery_map_iff
#print axioms Cordis.GlobalCalculus.Step.preservesWellFormed
#print axioms Cordis.GlobalCalculus.Step.installation_semantics
#print axioms Cordis.GlobalCalculus.Step.installedAt_change_only_boundary
#print axioms Cordis.GlobalCalculus.Trace.preservesWellFormed
#print axioms Cordis.GlobalCalculus.FromEmpty.final_wellFormed
#print axioms Cordis.GlobalCalculus.Example.unified_rule_projection
#print axioms Cordis.GlobalCalculus.Example.unified_stateMap_projection
#print axioms Cordis.GlobalCalculus.Example.unified_endpoint_exact
#print axioms Cordis.GlobalTraceFacts.iteration_foreign_lookup
#print axioms Cordis.GlobalTraceFacts.iteration_owner_static
#print axioms Cordis.GlobalTraceFacts.foreignExact_of_notUnload
#print axioms Cordis.GlobalTraceFacts.foreignTables_preserved
#print axioms Cordis.GlobalTraceFacts.foreignControl_continuous
#print axioms Cordis.GlobalTraceFacts.actorStatic_continuous
#print axioms Cordis.GlobalTraceFacts.namedCommitted_continuous
#print axioms Cordis.GlobalTraceFacts.accumulatedRecovery_iff_unload
#print axioms Cordis.GlobalTraceFacts.Trace.aligned
#print axioms Cordis.GlobalTraceFacts.Trace.states_length
#print axioms Cordis.GlobalTraceFacts.Trace.installedAt_forward
#print axioms Cordis.GlobalTraceFacts.BoundedEpisode.interior_close_installed
#print axioms Cordis.GlobalTraceFacts.BoundedEpisode.open_rule
#print axioms Cordis.GlobalTraceFacts.BoundedEpisode.close_rule
#print axioms Cordis.GlobalTraceFacts.Counterexample.bareAdmission_breaks_foreignTables
#print axioms Cordis.GlobalTraceFacts.Counterexample.bareAdmission_not_recoveryConfinement

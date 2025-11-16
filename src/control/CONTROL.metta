;;Declarative inference (deriving events and knowledge from observed events)

;Derived belief event priority
(= (ConclusionPriority $EPrio $CPrio $ConcTV) (* (* $EPrio $CPrio) (Truth_Expectation $ConcTV)))

;making declarative inferences on two events (task from PQ and belief from concept)
(= (Conclude (Event $S1 ($time1 $ev1 $prio1)) (Event $S2 ($time2 $ev2 $prio2)) $CPrio $t)
   (let $ConclusionStamp (TupleConcat $ev1 $ev2)
        (If (StampDisjoint $ev1 $ev2)
            (let ($ConcTerm $ConcTV) (superpose ((|- $S1 $S2) (|- $S2 $S1)))
                 (Event ($ConcTerm $ConcTV)
                        ($time1 $ConclusionStamp
                                ($t (ConclusionPriority (EventPriorityNow $prio1 $t)
                                                        (ConceptPriorityNow $CPrio $t)
                                                        $ConcTV))))))))

;find a belief for the task to generate conclusions with
(= (ReasonWithTask (Event $S1 ($time1 $ev1 $prio1)) $t)
   (let ($Belief $CPrio) (case (get-atoms &attentional_focus)
                               (((Concept $Term (Event $SE2 ($timeE2 $evE2 $prioE2)) (Event $S2 ($time2 $ev2 $prio2)) $CPrio)
                                 (If (and (not (== $time1 eternal)) (> (abs (- $time1 $time2)) 20))
                                     ((Event $SE2 ($timeE2 $evE2 $prioE2)) $Cprio)
                                     ((Event $S2 ($time2 $ev2 $prio2)) $CPrio)))))
        (case (Conclude (Event $S1 ($time1 $ev1 $prio1)) (TemporallyAlignedBelief $time1 $Belief) $CPrio $t)
              (((Event $1 $2) (ProcessBeliefEvent (Event (trace! (.: $1) $1) $2) $t))))))

;select the highest priority belief event from the PQ and use it for reasoning
(= (BeliefCycle $t) (do (sequential ((let $Ev (SelectHighestPriorityEvent &belief_events $t)
                                          (sequential ((remove-atom &belief_events $Ev)
                                                       (ReasonWithTask $Ev $t))))
                                     (UpdateReasonerState)
                                     (BoundEvents &belief_events 0.0 0.1 (BeliefEventsMax) $t)
                                     (BoundAttention 0.0 0.1 (AttentionalFocusConceptsMax) $t)))))
;;Temporal inference (sequence and implication formation based on FIFO)

;use the event's evidence to induce a time-independent belief which can be used in the future
(= (Eternalize $Ev) (let (Event ($Term $TV) ($Time $Evidence $EPrio)) $Ev
                         (If (== $Time eternal) $Ev
                             (Event ($Term (Truth_Eternalize $TV)) (eternal $Evidence (0 0.0))))))

;use evidence of an event at a slightly different moment in time
(= (Projection (Event ($Term ($f $c)) ($Time $Evidence $EPrio)) $TargetTime)
   (Event ($Term ($f (* $c (min 1 (/ 1 (abs (- $Time $TargetTime))))))) ($TargetTime $Evidence $EPrio)))

;make the belief occurrence time compatible with the task's
(= (TemporallyAlignedBelief $TaskTime $Belief) (If (== $TaskTime eternal)
                                                   (Eternalize $Belief)
                                                   (Projection $Belief $TaskTime)))

;FIFO max. size bound
!(bind! &FIFO (new-state ()))
(= (EventWithFIFO3 $New ($1 $2 $3)) ($New $1 $2))
(= (EventWithFIFO3 $New ($1 $2)) ($New $1 $2))
(= (EventWithFIFO3 $New ($1)) ($New $1))
(= (EventWithFIFO3 $New ()) ($New))

;Add event to FIFO
(= (EventToFIFO $Ev)
   (let $newlist (EventWithFIFO3 $Ev (get-state &FIFO))
        (change-state! &FIFO $newlist)))

;Form a sequence of two events
(= (TemporalSequence $Ev1 (Event ($Term2 $Truth2) ($Time2 $Evidence2 $EPrio2)))
   (let (Event ($Term1 $Truth1) ($Time1 $Evidence1 $EPrio1)) (Projection $Ev1 $Time2)
        (Event (($Term1 &/ $Term2) (Truth_Intersection $Truth1 $Truth2)) ($Time2 (TupleConcat $Evidence1 $Evidence2) (0 0.0)))))

;Form a temporal implication between two events
(= (TemporalImplication $Ev1 (Event ($Term2 $Truth2) ($Time2 $Evidence2 $EPrio2)))
   (let (Event ($Term1 $Truth1) ($Time1 $Evidence1 $EPrio1)) (Projection $Ev1 $Time2)
        (trace! (.: (($Term1 =/> $Term2) (Truth_Induction $Truth1 $Truth2)))
                (Event (($Term1 =/> $Term2) (Truth_Induction $Truth1 $Truth2)) ($Time2 (TupleConcat $Evidence1 $Evidence2) (0 0.0))))))

;Whether an event's term is an operation
(= (IsOp (Event ($Term $Truth) $Metadata))
   (case $Term (((^ $Opname) True)
                ($Otherwise False))))

;Find implications in the event FIFO:
;procedural implications
(= (TemporalImplicationInduction ($Cons $Op $Prec))
   (If (and (IsOp $Op) (and (not (IsOp $Cons)) (not (IsOp $Prec))))
       (let $PrecOp (TemporalSequence $Prec $Op)
            (TemporalImplication $PrecOp $Cons))))
;and temporal without operation
;(= (TemporalImplicationInduction ($Cons $Prec $Trail))
;   (If (and (not (IsOp $Prec)) (not (IsOp $Cons)))
;       (TemporalImplication $Prec $Cons)))

;Add negative evidence for implications which predicted the input unsuccessfully
(= (NegConfirmation $PrecTerm $ObservedCons $t)
   (let (Event (($PrecTerm =/> $PredictedCons) $ImpTV) $ImpMetadata) (WhatWillHappenQuestion $PrecTerm)
        (If (not (== $ObservedCons $PredictedCons))
            (UpdateConcept (Event (($PrecTerm =/> $PredictedCons) (0.0 0.1)) ($t () (0 0.0))) $t))))

;Check if the implication's preconditions are met to anticipate the by the implication predicted outcome
;(= (Anticipate ($Pos $Pre $Trail) $t)
;   (let* (((Event ($PreTerm $PreTV) $PreMetadata) $Pre)
;          ((Event ($PosTerm $PosTV) $PosMetadata) $Pos))
;         (If (not (IsOp $Pre))
;             (NegConfirmation $PreTerm $PosTerm $t))))
(= (Anticipate ($Pos $Op $Pre) $t)
   (let* (((Event ($PreTerm $PreTV) $PreMetadata) $Pre)
          ((Event ($OpTerm $OpTV) $OpMetadata) $Op)
          ((Event ($PosTerm $PosTV) $PosMetadata) $Pos))
         (If (and (IsOp $Op) (not (IsOp $Pre)))
             (NegConfirmation ($PreTerm &/ $OpTerm) $PosTerm $t))))

;Input procedure
(= (AddBeliefEvent $Sentence)
   (let* ((($t $evidentialBase) (GetReasonerState))
          ($InputEvent (Event (trace! (.: $Sentence) $Sentence) ($t $evidentialBase ($t 1.0))))
          ($notAnOperation (not (IsOp $InputEvent))))
          (do (sequential ((EventToFIFO $InputEvent)
                           (Anticipate (get-state &FIFO) $t)
                           (If $notAnOperation
                               (sequential ((let $InducedHypothesis (TemporalImplicationInduction (get-state &FIFO))
                                                 (UpdateConcept $InducedHypothesis $t))
                                            (ProcessBeliefEvent $InputEvent $t)
                                            (BeliefCycle $t)))
                               (UpdateReasonerState)))))))
;;Procedural inference (decision making with operation execution and subgoaling)

;Derived goal event priority
(= (SubgoalPriority $EPrio $ConcTV) (* $EPrio (Truth_Expectation $ConcTV)))

;Expectation of an operation is the truth expectation of its desire value
(= (OpExpectation (Decision ($Opname $DVOp) $Subgoal) $t) (Truth_Expectation $DVOp))

;Inject executed operation as an event and return its name
(= (Execute $Opname) (superpose ((AddBeliefEvent ($Opname (1.0 0.9))) $Opname)))

;Add subgoals to the PQ
(= (DeriveSubgoals $Options)
   (do (let (Decision $Op (Event $S $Metadata)) (superpose $Options)
            (let $Subgoal (Event (trace! (!: $S) $S) $Metadata)
                 (add-atom &goal_events $Subgoal)))))

;execute the operation which most likely gets the goal achieved in current contexts, and if contexts are not yet fulfilled, derive them as subgoals
(= (BestDecision $t (Event ($Term $DV) ($GoalTime $GoalEvBase $GoalPrio)))
   (let $Options (collapse (let* (((Event ((($Prec &/ (^ $Op)) =/> $Term) $ImpTV) ($ImpTime $ImpEvBase $ImpPrio))
                                   (HowAchieveQuestion $Term))
                                  ($DVPrecOp (Truth_Deduction $DV $ImpTV))
                                  ((Event ($PrecTerm $PrecTV) $PrecMetadata)
                                   (Projection (EventQuestion $Prec) $t))
                                  ($DVOp (Truth_Deduction $PrecTV $DVPrecOp))
                                  ($DVPrec (Truth_StructuralDeduction $DVPrecOp))
                                  ($SubgoalStamp (TupleConcat $GoalEvBase $ImpEvBase))
                                  ($SubgoalPrio (SubgoalPriority (EventPriorityNow $GoalPrio $t) $DVPrec)))
                                 (If (StampDisjoint $GoalEvBase $ImpEvBase)
                                     (Decision ((^ $Op) $DVOp) (Event ($Prec $DVPrec)
                                                                      ($t $SubgoalStamp ($t $SubgoalPrio)))))))
        (let (Decision ($Opname $DVOp) $Subgoal) (BestCandidate $Options OpExpectation $t)
             (If (> (Truth_Expectation $DVOp) 0.5)
                 (Execute $Opname)
                 (DeriveSubgoals $Options)))))

;select the highest priority goal event from the PQ and use it for decision making
(= (GoalCycle $t) (sequential ((let $Ev (SelectHighestPriorityEvent &goal_events $t)
                                    (sequential ((do (remove-atom &goal_events $Ev))
                                                 (BestDecision $t $Ev))))
                               (do (UpdateReasonerState))
                               (do (BoundEvents &goal_events 0.0 0.1 (GoalEventsMax) $t)))))

;Input procedure
(= (AddGoalEvent $Sentence)
   (let* ((($t $evidentialBase) (GetReasonerState))
          ($InputEvent (Event (trace! (!: $Sentence) $Sentence) ($t $evidentialBase ($t 1.0)))))
         (sequential ((do (add-atom &goal_events $InputEvent))
                      (GoalCycle $t)))))

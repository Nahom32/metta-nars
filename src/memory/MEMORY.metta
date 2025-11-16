;params
(= (BeliefEventsMax) 10)
(= (GoalEventsMax) 10)

;spaces
!(bind! &belief_events (new-space))
!(bind! &goal_events (new-space))

;states
!(bind! &currentTime (new-state 1))
!(bind! &evidentialBase (new-state 1))
(= (increment $atom) (sequential ((change-state! $atom (+ 1 (get-state $atom))))))
(= (UpdateReasonerState) (sequential ((trace! (time := (get-state &currentTime)) 42) (increment &currentTime) (increment &evidentialBase))))
(= (GetReasonerState) ((get-state &currentTime) ((get-state &evidentialBase))))

;priority of events
(= (EventPriorityNow ($T $P) $t) (* $P (/ 1 (+ 1 (- $t $T)))))

;retrieve the best candidate (allows to use tuples / collapse results / spaces as a PQ)
!(bind! &tempbest (new-state ()))
!(bind! &tempbestscore (new-state 0))
(= (BestCandidate $tuple $evaluateCandidateFunction $t)
   (sequential ((do (change-state! &tempbestscore 0))
                (do (change-state! &tempbest ()))
                (do (let* (($x (superpose $tuple))
                               ($fx ($evaluateCandidateFunction $x $t)))
                              (superpose ((If (> $fx (get-state &tempbestscore))
                                              (sequential ((change-state! &tempbest $x)
                                                           (change-state! &tempbestscore $fx))))))))
                (get-state &tempbest))))

;functions to select highest-priority events in belief and goal PQ
(= (PriorityOf (Event $Sentence ($occT $Ev $Prio)) $t) (EventPriorityNow $Prio $t))
(= (SelectHighestPriorityEvent $collection $t)
   (BestCandidate (collapse (get-atoms $collection)) PriorityOf $t))

;a belief event to process, which demands adding it to the PQ and updating its concept
(= (ProcessBeliefEvent $Ev $t)
   (sequential ((add-atom &belief_events $Ev)
                (UpdateConcept $Ev $t))))

;bound the size of the attentional focus for tasks / events
(= (BoundEvents $collection $Threshold $Increment $TargetAmount $t)
   (sequential ((do (let* (($Ev (get-atoms $collection))
                            ((Event $Sentence ($Time $Evidence $EPrio)) $Ev))
                          (If (< (EventPriorityNow $EPrio $t) $Threshold)
                              (remove-atom $collection $Ev))))
                (let $CurrentAmount (TupleCount (collapse (CountElement (get-atoms $collection))))
                     (If (> $CurrentAmount $TargetAmount)
                         (BoundEvents $collection (+ $Threshold $Increment) $Increment $TargetAmount $t))))))
;params
(= (AttentionalFocusConceptsMax) 10)

;spaces
!(bind! &concepts (new-space))
!(bind! &attentional_focus (new-space))

;priority of concepts
(= (ConceptPriorityNow ($T $P) $t) (* $P (/ 1 (+ 1 (- $t $T)))))

;Whether evidence was just counted once
(= (StampDisjoint $Ev1 $Ev2)
   (If (or (== $Ev1 ()) (== $Ev2 ())) ;check only needed due to a bug in the MeTTa interpreter
       True                           ;https://github.com/trueagi-io/hyperon-experimental/issues/481
       (== () (collapse (let* (($x (superpose $Ev1))
                               ($y (superpose $Ev2)))
                              (case (== $x $y) ((True overlap))))))))

;revise if there is no evidential overlap, else use higher-confident candidate
(= (RevisionAndChoice (Event ($Term1 ($f1 $c1)) (eternal $ev1 $EPrio1)) (Event ($Term2 ($f2 $c2)) (eternal $ev2 $EPrio2)))
   (let $ConclusionStamp (TupleConcat $ev1 $ev2)
        (If (StampDisjoint $ev1 $ev2)
            (Event ($Term1 (Truth_Revision ($f1 $c1) ($f2 $c2))) (eternal $ConclusionStamp (0 0.0)))
            (If (> $c1 $c2)
                (Event ($Term1 ($f1 $c1)) (eternal $ev1 (0 0.0)))
                (Event ($Term2 ($f2 $c2)) (eternal $ev2 (0 0.0)))))))

;update beliefs in existing concept with the new event or create new concept to enter the new evidence
(= (UpdateConcept $NewEvent $t)
   (let* (((Event ($Term $TV) ($Time $Evidence $EPrio)) $NewEvent)
          ($NewEventEternalized (Eternalize $NewEvent)))
                      (case (match &attentional_focus (Concept $TermX $Belief $BeliefEvent $CPrio) 
                                                       (If (== $TermX $Term) (Concept $TermX $Belief $BeliefEvent $CPrio)))
                            (((Concept $TermX $Belief $BeliefEvent $CPrio) (sequential ((remove-atom &attentional_focus (Concept $TermX $Belief $BeliefEvent $CPrio))
                                                                                         (let* (((Event $RevSentence $Metadata) (RevisionAndChoice $Belief $NewEventEternalized))
                                                                                                ($RevisedBelief (Event (trace! (@ $RevSentence) $RevSentence) $Metadata))
                                                                                                ($MaxPrio (If (> (EventPriorityNow $EPrio $t) (ConceptPriorityNow $CPrio $t))
                                                                                                              $EPrio $CPrio)))
                                                                                               (add-atom &attentional_focus (Concept $Term $RevisedBelief $NewEvent $MaxPrio))))))
                             (%void% (case (match &concepts (Concept $TermX2 $Belief2 $BeliefEvent2 $CPrio2)
                                           (If (== $TermX2 $Term) (Concept $TermX2 $Belief2 $BeliefEvent2 $CPrio2)))
                                               (((Concept $TermX2 $Belief2 $BeliefEvent2 $CPrio2) (sequential ((remove-atom &concepts (Concept $TermX2 $Belief2 $BeliefEvent2 $CPrio2))
                                                                                                                (add-atom &attentional_focus (Concept $TermX2 $Belief2 $BeliefEvent2 $CPrio2))
                                                                                                                (UpdateConcept $NewEvent $t))))
                                               (%void% (sequential ((add-atom &attentional_focus (Concept $Term $NewEventEternalized $NewEvent $EPrio))))))))))))

;bound the size of attentional focus of concepts
(= (BoundAttention $Threshold $Increment $TargetAmount $t)
   (sequential ((do (let* (($C (get-atoms &attentional_focus))
                           ((Concept $Term (Event $Sentence $Metadata) $BeliefEvent $CPrio) $C))
                          (If (< (ConceptPriorityNow $CPrio $t) $Threshold) (sequential ((remove-atom &attentional_focus $C)
                                                                                         (add-atom &concepts $C))))))
                (let $CurrentAmount (TupleCount (collapse (CountElement (get-atoms &attentional_focus))))
                     (If (> $CurrentAmount $TargetAmount)
                         (BoundAttention (+ $Threshold $Increment) $Increment $TargetAmount $t))))))

;get eternal belief of concept
(: EternalQuestion (-> Expression %Undefined%))
(= (EternalQuestion $Term) (case (match (superpose (&attentional_focus &concepts)) (Concept $TermX $Belief $BeliefEvent $CPrio) (If (== $Term $TermX) $Belief))
                                 (($Ev $Ev) (%void% (Event (None (0.5 0.0)) (eternal () 0.0))))))

(: HowAchieveQuestion (-> Expression %Undefined%))
(= (HowAchieveQuestion $Cons) (case (match (superpose (&attentional_focus &concepts)) (Concept (($Prec &/ (^ $Op)) =/> $ConsX) $Belief $BeliefEvent $CPrio) (If (== $Cons $ConsX) $Belief))
                                    (($Ev $Ev) (%void% (Event (None (0.5 0.0)) (eternal () 0.0))))))

(: WhatWillHappenQuestion (-> Expression %Undefined%))
(= (WhatWillHappenQuestion $Prec) (case (match (superpose (&attentional_focus &concepts)) (Concept ($PrecX =/> $Cons) $Belief $BeliefEvent $CPrio) (If (== $Prec $PrecX) $Belief))
                                    (($Ev $Ev) (%void% (Event (None (0.5 0.0)) (eternal () 0.0))))))


;get event belief of concept
(: EventQuestion (-> Expression %Undefined%))
(= (EventQuestion $Term) (case (match (superpose (&attentional_focus &concepts)) (Concept $TermX $Belief $BeliefEvent $CPrio) (If (== $TermX $Term) $BeliefEvent))
                               (($Ev $Ev) (%void% (Event (None (0.5 0.0)) (0 () 0.0))))))

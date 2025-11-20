!(register-module! ../metta-nars)
!(import! &self metta-nars:src:logic:nal1)
!(import! &self metta-nars:src:NARS)
!(bind! &test (new-space))
(( r1 ((TTV 1 (STV 0.8 0.7)) (IMPLICATION_LINK 
              (AND_LINK ((Goal Conversation-Started 0.9 0.6) initiate-dialogue)) (Goal Send-Greeting 1.0 1.0)))) 4)
(= (convertScheme (( $handle ($tv (IMPLICATION_LINK (AND_LINK ($context $action)) $goal))) $weight))
    (let (TTV $time (STV $f $c)) $tv (((AND_LINK ($context $action)) --> $goal) ($f $c))))
(= (findRulesWithHandle $space $handle)
    (collapse (match $space (( $handle ((TTV $time (STV $bel $conf)) (IMPLICATION_LINK (AND_LINK ($context $action)) (Goal $goal $x $y)))) $weight)
        (( $handle ((TTV $time (STV $bel $conf)) (IMPLICATION_LINK (AND_LINK ($context $action)) (Goal $goal $x $y)))) $weight)
        
    ))
)

(= (addRules $space) 
    (add-reduct $space (superpose (

    ;; r30 Return to base on alert
    (( r30 ((TTV 1 (STV 0.8 0.75)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal battery_alert 0.95 0.8) return)) 
            (Goal base_reached 1.0 1.0)))) 5)

    ;; r31 Dock when base reached
    (( r31 ((TTV 1 (STV 0.7 0.65)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal base_reached 0.9 0.75) dock)) 
            (Goal docked 1.0 1.0)))) 2)

    ;; r32 Charge when docked
    (( r32 ((TTV 1 (STV 0.85 0.8)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal docked 0.95 0.85) charge)) 
            (Goal full_energy 1.0 1.0)))) 3)

    ;; r33 Shutdown after charge
    (( r33 ((TTV 1 (STV 0.65 0.6)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal full_energy 0.9 0.75) shutdown)) 
            (Goal system_off 1.0 1.0)))) 1)
    (( r33' ((TTV 1 (STV 0.65 0.6)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal less_energy 0.9 0.75) shutdown)) 
            (Goal system_off 1.0 1.0)))) 1)


    ;; r34 Wake when system off
    (( r34 ((TTV 1 (STV 0.75 0.7)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal system_off 0.85 0.7) wake)) 
            (Goal system_on 1.0 1.0)))) 3)

    ;; r35 Initialize sensors
    (( r35 ((TTV 1 (STV 0.7 0.65)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal system_on 0.9 0.75) init_sensors)) 
            (Goal sensors_ready 1.0 1.0)))) 2)

    ;; r36 Train model after sensors ready
    (( r36 ((TTV 1 (STV 0.85 0.8)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal sensors_ready 0.95 0.85) train)) 
            (Goal model_trained 1.0 1.0)))) 4)

    ;; r37 Predict after training
    (( r37 ((TTV 1 (STV 0.7 0.65)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal model_trained 0.9 0.75) predict)) 
            (Goal prediction_ready 1.0 1.0)))) 3)

    ;; r38 Validate after prediction
    (( r38 ((TTV 1 (STV 0.75 0.7)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal prediction_ready 0.85 0.7) validate)) 
            (Goal validation_done 1.0 1.0)))) 2)

    ;; r39 Save model after validation
    (( r39 ((TTV 1 (STV 0.8 0.75)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal validation_done 0.95 0.8) save)) 
            (Goal model_saved 1.0 1.0)))) 3)

    ;; r40 Deploy after saving model
    (( r40 ((TTV 1 (STV 0.9 0.85)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal model_saved 0.9 0.75) deploy)) 
            (Goal model_deployed 1.0 1.0)))) 5)
))))

(= (convertRulesToNars $space)
  (let $values (collapse (get-atoms $space)) (collapse (convertScheme (superpose $values))))
)
!(addRules &test)

(: isMember (-> $aa Expression Bool))
(= (isMember $item $list) 
        (if (== $list ()) 
            False 
            (let ($head $tail) (decons-atom $list) 
                (if (== $head $item) 
                    True 
                    (isMember $item $tail)))))


(= (all $expression)
    (let $exp (collapse (if (== (superpose $expression) True) True (empty))) (if (< (size-atom $exp) (size-atom $expression)) False True))
)
(= (any $expression)
    (let $exp (collapse (if (== (superpose $expression) True) True (empty))) (if (== $exp ()) False True)))


( isReduced (-> Expression Bool))
;;(= (isReduced $value) (all (collapse (not (isMember reason (superpose $value))))))
(= (isReduced $value) (not (isMember reason $value)))
(= (applyInferenceForRule $rule $rules $accum)
  (if (== $rules ())
     $accum
    (let* (
        (($head $tail) (decons-atom $rules))
        ($results (reason $rule $head))
        ($_ (println! (results $results)))
        ($reduced (isReduced $results))
        ($_ (println! (reduced $reduced)))
        ($accum' (if (not $reduced) $accum (union-atom $accum ($results))))
    ) 
      (applyInferenceForRule $rule $tail  $accum')
  )
))

(= (applyInference' $rules $counter $accum)
  (if (== $rules ())
     $accum
    (let* (
      (($head $tail) (decons-atom $rules))
      ($inferedRules (applyInferenceForRule $head $tail ()))
      ($ruleSize (size-atom $inferedRules))
      ($accum' (union-atom $accum $inferedRules))
    )
     (applyInference' $tail $counter' $accum')
    )
  )
)

(= (applyInference $space)
  (let* (
    ($narsRules (convertRulesToNars $space))
    ($newRules (applyInference' $narsRules $counter ()))
  )
    $newRules
  )
)
!(applyInference  &test)


!(reason (convertScheme (( r33' ((TTV 1 (STV 0.65 0.6)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal less_energy 0.9 0.75) shutdown)) 
            (Goal system_off 1.0 1.0)))) 1)
)

(convertScheme 
    (( r33 ((TTV 1 (STV 0.65 0.6)) 
            (IMPLICATION_LINK 
            (AND_LINK ((Goal full_energy 0.9 0.75) shutdown))  
            (Goal system_off 1.0 1.0)))) 1)))

!(size-atom (collapse (match &test ((r33 $schema) $weight) $schema)))

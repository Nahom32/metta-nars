!(register-module! ../metta-nars)
!(import! &self metta-nars:src:logic:nal1)

((: r1 ((TTV 1 (STV 0.8 0.7)) (IMPLICATION_LINK 
              (AND_LINK ((Goal Conversation-Started 0.9 0.6) initiate-dialogue)) (Goal Send-Greeting 1.0 1.0)))) 4)
(= (convertScheme ((: $handle $tv (IMPLICATION_LINK (AND_LINK $context $action) $goal)) $weight))
    (((AND_LINK $context $action)--> $goal) $tv)
)

;;(($a --> $b) $T1) 

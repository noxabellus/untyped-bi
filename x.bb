effect Exn e =
    fail : e -> 'a

maybe_fail : (() -> 'a in [Exn 'e] <> 'eff) -> Maybe 'a in 'eff
fun maybe_fail action {
    with Exn 'e {
        fail _ { Nothing }  ;; does not continue; this is why it can have type 'a
        return a { Just a } ;; may never continue
    }
    action()
}

(maybe_fail
    (with
        (input Function)
        (local 'a)
        (output (Maybe 'a)))
   ($entry
        (WITH_HANDLER_V 0 $body 2 #O 0
            (return
                (with
                    (input 'a)
                    (local Function)
                    (output (Maybe 'a)))
                ($entry
                    (STORE_IMM #L0 @Just)
                    (CALL 1 #L0 #O #I0)
                    (RETURN)))
            (fail
                (with
                    (input 'e)
                    (output (Maybe 'a)))
                ($entry
                    (STORE_IMM #O @Nothing)
                    (RETURN))))
        (RETURN))
    ($body
        (CALL 0 #I0 #L0)                ;; fail called from in here breaks the block
        (BR_V $body #LO 0 (sizeof 'a))) ;; return is called here
)

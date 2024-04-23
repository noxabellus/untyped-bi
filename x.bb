effect Exn e =
    fail : e -> 'a

maybe_fail : (() -> 'a in [Exn 'e] <> 'eff) -> Maybe 'a in 'eff
fun maybe_fail action {
    with {
        Exn 'e {
            fail _ { Nothing }  ;; does not continue; this is why it can have type 'a
        }

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
        (CALL 0 #I0 #L0)                 ;; fail called from in here breaks the block
        (BR_V $body #LO 0 (sizeof 'a)))) ;; return is called here


effect Read =
    at_end : () -> Bool
    read_ln : () -> String

read_file : () -> String in [Read]
fun read_file {
    if at_end() { "" }
    else { read_ln() ++ "\n" ++ read_file() }
}

with_file : (File, () -> 'a in [Read] <> 'eff) -> 'a in 'eff
fun with_file (mut f) a {
    with {
        Read {
            at_end () => continue (File.at_end f)
            read_ln () => continue (File.read_ln f)
        }
        finally => File.close f ;; finally should run even if the block is exited by an exception
    }
    a()
}

(with_file
    (with
        (input File Function)
        (output 'a))
    ($entry
        (WITH_HANDLER_V 0 $body 2 #O 0
            (at_end
                (with
                    (input ())
                    (output Bool))
                ($entry
                    (CALL 1 @File.at_end #O #U1)
                    (CONTINUE)))
            (read_ln
                (with
                    (input ())
                    (output String))
                ($entry
                    (CALL 1 @File.read_ln #O #U1)
                    (CONTINUE)))
            (finally
                (with
                    (input ())
                    (output ()))
                ($entry
                    (CALL 1 @File.close #O #U1)
                    (RETURN))))
        (RETURN))
    ($body
        (CALL 0 #I0 #L0)
        (BR_V $body #LO 0 (sizeof 'a))))

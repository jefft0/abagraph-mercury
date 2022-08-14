:- module options.
:- interface.

:- type option_key
        ---> derivation_type
        ;    fileID
        ;    num_sols
        ;    opponent_abagraph_choice
        ;    opponent_sentence_choice
        ;    print_to_file
        ;    proponent_sentence_choice
        ;    proponent_rule_choice
        ;    show_solution
        ;    turn_choice
        ;    verbose.

:- pred option(option_key::in, string::out) is det.
:- pred verbose is semidet.

:- implementation.

option(derivation_type, "ab").
option(fileID, "_sol_").
option(num_sols, "0").    % all solutions
option(opponent_abagraph_choice, "s").
option(opponent_sentence_choice, "p").
option(print_to_file, "fail").
option(proponent_sentence_choice, "p").
option(proponent_rule_choice, "l1").
option(show_solution, "true").
option(turn_choice, "p").  % Use "p" instead of "[p,o]" like the web page documentation.
option(verbose, "true").

verbose :-
  option(verbose, "true").

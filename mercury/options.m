% Ported to Mercury from abagraph in Prolog by Robert Craven:
% http://robertcraven.org/proarg/abagraph.html

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

:- type turn_choice ---> p; o; s.

:- type proponent_sentence_choice ---> p. %TODO: Implement others o; n; e; p; pn; be; bp.

:- pred option(option_key::in, string::out) is det.
:- pred verbose is semidet.
:- pred get_turn_choice(turn_choice::out) is det.
:- pred get_proponent_sentence_choice(proponent_sentence_choice::out) is det.

:- implementation.

:- import_module require.

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

get_turn_choice(Out) :-
  option(turn_choice, Val),
  (Val = "p" -> Out = p ;
  (Val = "o" -> Out = o ;
  (Val = "s" -> Out = s ;
    unexpected($file, $pred, "invalid turn_choice")))).

get_proponent_sentence_choice(Out) :-
  option(proponent_sentence_choice, Val),
  %TODO: Implement others.
  %(Val = "o" -> Out = o ;
  %(Val = "n" -> Out = n ;
  %(Val = "e" -> Out = e ;
  (Val = "p" -> Out = p ;
  %(Val = "pn" -> Out = pn ;
  %(Val = "be" -> Out = be ;
  %(Val = "bp" -> Out = bp ;
    unexpected($file, $pred, "invalid proponent_sentence_choice")).

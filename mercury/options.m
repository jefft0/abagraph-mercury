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

:- type opponent_abagraph_choice ---> o; n. %TODO: Implement others: s; l; lmb.

:- type opponent_sentence_choice ---> p; pn. %TODO: Implement others: o; n; e.

:- type proponent_sentence_choice ---> o; n; e; p; pn. %TODO: Implement others: be; bp.

:- type turn_choice ---> p; o; s.

:- pred option(option_key::in, string::out) is det.
:- pred verbose is semidet.
:- pred get_opponent_abagraph_choice(opponent_abagraph_choice::out) is det.
:- pred get_proponent_sentence_choice(proponent_sentence_choice::out) is det.
:- pred get_opponent_sentence_choice(opponent_sentence_choice::out) is det.
:- pred get_turn_choice(turn_choice::out) is det.

:- implementation.

:- import_module require.

option(derivation_type, "ab").
option(fileID, "_sol_").
option(num_sols, "0").    % all solutions
%Debug option(opponent_abagraph_choice, "s").
option(opponent_abagraph_choice, "o").
option(opponent_sentence_choice, "p").
option(print_to_file, "fail").
option(proponent_sentence_choice, "p").
option(proponent_rule_choice, "l1").
option(show_solution, "true").
option(turn_choice, "p").  % Use "p" instead of "[p,o]" like the web page documentation.
option(verbose, "true").

verbose :-
  option(verbose, "true").

get_opponent_abagraph_choice(Out) :-
  option(opponent_abagraph_choice, Val),
  %TODO: Implement others.
  (Val = "o" -> Out = o ;
  (Val = "n" -> Out = n ;
  %(Val = "s" -> Out = s ;
  %(Val = "l" -> Out = l ;
  %(Val = "lmb" -> Out = lmb ;
    unexpected($file, $pred, "invalid proponent_sentence_choice"))).

get_proponent_sentence_choice(Out) :-
  option(proponent_sentence_choice, Val),
  %TODO: Implement others.
  (Val = "o" -> Out = o ;
  (Val = "n" -> Out = n ;
  (Val = "e" -> Out = e ;
  (Val = "p" -> Out = p ;
  (Val = "pn" -> Out = pn ;
  %(Val = "be" -> Out = be ;
  %(Val = "bp" -> Out = bp ;
    unexpected($file, $pred, "invalid proponent_sentence_choice")))))).

get_opponent_sentence_choice(Out) :-
  option(opponent_sentence_choice, Val),
  %TODO: Implement others.
  %(Val = "o" -> Out = o ;
  %(Val = "n" -> Out = n ;
  %(Val = "e" -> Out = e ;
  (Val = "p" -> Out = p ;
  (Val = "pn" -> Out = pn ;
  %(Val = "be" -> Out = be ;
  %(Val = "bp" -> Out = bp ;
    unexpected($file, $pred, "invalid proponent_sentence_choice"))).

get_turn_choice(Out) :-
  option(turn_choice, Val),
  (Val = "p" -> Out = p ;
  (Val = "o" -> Out = o ;
  (Val = "s" -> Out = s ;
    unexpected($file, $pred, "invalid turn_choice")))).

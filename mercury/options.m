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

:- type derivation_type ---> ab; gb.

:- type opponent_abagraph_choice ---> o; n; s; l. %TODO: Implement others: lmb.

:- type opponent_sentence_choice ---> p; pn. %TODO: Implement others: o; n; e.

:- type proponent_sentence_choice ---> o; n; e; p; pn. %TODO: Implement others: be; bp.

:- type proponent_rule_choice ---> s. %TODO: Implement others: l1.

:- type turn_choice ---> p; o; s.

:- pred option(option_key::in, string::out) is det.
:- pred verbose is semidet.
:- pred ab_derivation is semidet.
:- pred gb_derivation is semidet.

:- pred get_derivation_type(derivation_type::out) is det.
:- pred get_opponent_abagraph_choice(opponent_abagraph_choice::out) is det.
:- pred get_opponent_sentence_choice(opponent_sentence_choice::out) is det.
:- pred get_proponent_sentence_choice(proponent_sentence_choice::out) is det.
:- pred get_proponent_rule_choice(proponent_rule_choice::out) is det.
:- pred get_turn_choice(turn_choice::out) is det.

:- implementation.

:- import_module require.

option(derivation_type, "ab").
option(fileID, "_sol_").
option(num_sols, "0").    % all solutions
option(opponent_abagraph_choice, "s").
option(opponent_sentence_choice, "p").
option(print_to_file, "fail").
option(proponent_sentence_choice, "p").
%Debug option(proponent_rule_choice, "l1").
option(proponent_rule_choice, "s").
option(show_solution, "true").
option(turn_choice, "p").  % Use "p" instead of "[p,o]" like the web page documentation.
option(verbose, "fail").

% OPTIONS: checking

ab_derivation :-
 get_derivation_type(ab).
gb_derivation :-
 get_derivation_type(gb).

verbose :-
  option(verbose, "true").

get_derivation_type(Out) :-
  option(derivation_type, Val),
  (Val = "ab" -> Out = ab ;
  (Val = "gb" -> Out = gb ;
    unexpected($file, $pred, "invalid value"))).

get_opponent_abagraph_choice(Out) :-
  option(opponent_abagraph_choice, Val),
  %TODO: Implement others.
  (Val = "o" -> Out = o ;
  (Val = "n" -> Out = n ;
  (Val = "s" -> Out = s ;
  (Val = "l" -> Out = l ;
  %(Val = "lmb" -> Out = lmb ;
    unexpected($file, $pred, "invalid value"))))).

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
    unexpected($file, $pred, "invalid value"))).

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
    unexpected($file, $pred, "invalid value")))))).

get_proponent_rule_choice(Out) :-
  option(proponent_rule_choice, Val),
  %TODO: Implement others.
  (Val = "s" -> Out = s ;
  %(Val = "l1" -> Out = l1 ;
    unexpected($file, $pred, "invalid value")).

get_turn_choice(Out) :-
  option(turn_choice, Val),
  (Val = "p" -> Out = p ;
  (Val = "o" -> Out = o ;
  (Val = "s" -> Out = s ;
    unexpected($file, $pred, "invalid turn_choice")))).

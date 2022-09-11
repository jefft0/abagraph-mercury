
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% OPTIONS and HELP

% OPTIONS: generic

set_opt(Option, Value) :-
 retractall(option(Option,_)),
 assert(option(Option, Value)).

options :-
 option(Opt, Val),
 format('~w = ~w~n', [Opt,Val]),
 fail.
options.

% OPTIONS: setting

set_ab :-
 set_derivation(ab).
set_gb :-
 set_derivation(gb).

set_derivation(Type) :-
 set_opt(derivation_type, Type).

set_print :-
 set_opt(print_to_file, true).
set_noprint :-
 set_opt(print_to_file, fail).

set_strategies([TurnChoice,OppABAGrph,Prop,Opp,PropRule]) :-
 set_opt(turn_choice, TurnChoice),
 set_opt(opponent_abagraph_choice, OppABAGrph),
 set_opt(proponent_sentence_choice, Prop),
 set_opt(opponent_sentence_choice, Opp),
 set_opt(proponent_rule_choice, PropRule).

set_verbose :-
 set_opt(verbose, true).
set_quiet :-
 set_opt(verbose, fail).

set_show :-
 set_opt(show_solution, true).
set_noshow :-
 set_opt(show_solution, fail).

% OPTIONS: checking

ab_derivation :-
 option(derivation_type, ab).
gb_derivation :-
 option(derivation_type, gb).

verbose :-
 option(verbose, Verbose),
 Verbose.


% Ported to Mercury from abagraph in Prolog by Robert Craven:
% http://robertcraven.org/proarg/abagraph.html

:- module abagraph.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module pair.
:- import_module list.
:- import_module set.
:- import_module int.
:- import_module options.
:- import_module printing.

:- type turn
        ---> proponent
        ;    opponent.        

:- pred assumption(sentence::in) is semidet.
:- pred non_assumption(sentence::in) is semidet.
:- pred rule(sentence::in, list(sentence)::in) is semidet.
:- pred contrary(sentence::in, sentence::out) is det.

:- pred derive(sentence::in) is det.
:- pred initial_derivation_tuple(set(sentence)::in, step_tuple::out) is det.
:- pred derivation(step_tuple::in, int::in, derive_result::out, int::out) is det.
:- pred derivation_step(step_tuple::in, step_tuple::out) is det.
:- pred proponent_step(step_tuple::in, step_tuple::out) is det.
:- pred proponent_asm(sentence::in, set(sentence)::in, pair(set(sentence), arg_graph)::in, 
          opponent_arg_graph_set::in, set(sentence)::in, set(sentence)::in, step_tuple::out) is det.
%:- pred proponent_nonasm(sentence::in, set(sentence)::in, pair(set(sentence), arg_graph)::in, 
%          opponent_arg_graph_set::in, set(sentence)::in, set(sentence)::in, step_tuple::out) is det.
:- pred opponent_step(step_tuple::in, step_tuple::out) is det.
:- pred choose_turn(proponent_state::in, opponent_arg_graph_set::in, turn::out) is det.
:- pred turn_choice(string::in, proponent_state::in, opponent_arg_graph_set::in, turn::out) is det.

main(!IO) :-
  derive(fact("a")).

% TODO: This should be dynamic.
assumption(fact("a")).
assumption(fact("b")).

% TODO: Compute this like in loadf.
non_assumption(fact("p")).
non_assumption(fact("q")).

% TODO: This should be dynamic.
rule(fact("p"), [fact("b")]).
rule(fact("q"), []).

%contrary(A, not(A)).
contrary(A, Contrary) :-
  (if A = fact("a") then
    Contrary = fact("p")
  else
    % A = fact("b")
    Contrary = fact("q")).

% ("set some options" moved to options.m.)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CONTROL: entry predicates

derive(S) :-
  %retractall(proving(_)),
  %assert(proving(S)),
  initial_derivation_tuple(make_singleton_set(S), InitTuple),
  (if verbose then
    print_step(0, InitTuple)
  else
    true),
  %retractall(sols(_)),
  %assert(sols(1)),
  derivation(InitTuple, 1, Result, _),
  print_result(Result),
  %incr_sols.
  true.

initial_derivation_tuple(
    PropUnMrk,
    step_tuple(PropUnMrk-set.init-PropGr, % PropUnMrk-PropM-PropGr
               set.init-set.init,         % OppUnMrk-OppM (members of each are Claim-UnMrk-Mrk-Graph)
               % TODO: Support GB. 
               D0,                        % D
               set.init)) :-              % C
               % TODO: Do we need Att?
  % PropUnMrk is already a set. Instead of findall, use the set filter.
  %list_to_ord_set(PropUnMrk, O_PropUnMrk),
  %findall(A, (member(A, O_PropUnMrk),
  %            assumption(A)),
  %        D0),
  D0 = filter(assumption, PropUnMrk),
  PropGr = map((func(V) = V-set.init), PropUnMrk).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CONTROL: basic control structure

derivation(T, InN, Result, N) :-
  (if T = step_tuple(set.init-PropMrk-PropG, set.init-OppM, D, C) then
    Result = derive_result(PropMrk-PropG, OppM, D, C),
    N = InN
  else
    derivation_step(T, T1),
    (if verbose then
      print_step(InN, T1)
    else
      true),
    OutN = InN + 1,
    derivation(T1, OutN, Result, N)).

derivation_step(step_tuple(P, O, D, C), T1) :-
  choose_turn(P, O, Turn),
  (if Turn = proponent then
    proponent_step(step_tuple(P, O, D, C), T1)
  else
    opponent_step(step_tuple(P, O, D, C), T1)).

proponent_step(step_tuple(PropUnMrk-PropMrk-PropGr, O, D, C), T1) :-
  % TODO: proponent_sentence_choice(PropUnMrk, S, PropUnMrkMinus),
  S = fact("a"), PropUnMrkMinus = set.init, % Debug
  (if assumption(S) then
    proponent_asm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, T1),
    poss_print_case("1.(i)")
  else
    % Don't check non_assumption(S) because there is no other case.
    % non_assumption(S),
    proponent_asm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, T1), % Debug: Use proponent_nonasm.
    poss_print_case("1.(ii)")).

opponent_step(T, T1) :-
  % TODO: Implement.
  T1 = T.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CASES

%%%%%%%%%% proponent

proponent_asm(A, PropUnMrkMinus, PropMrk-PropGr, OppUnMrk-OppMrk, D, C, 
              step_tuple(PropUnMrkMinus-PropMrk1-PropGr, OppUnMrk1-OppMrk, D, C)) :-
  contrary(A, Contrary),
  (if \+ (member(Member1, OppUnMrk), Member1 = Contrary-_-_-_), 
      \+ (member(Member2, OppMrk),   Member2 = Contrary-_-_-_) then
    OppUnMrk1 = OppUnMrk %Debug append_element_nodup(OppUnMrk, Contrary-[Contrary]-[]-[Contrary-[]], OppUnMrk1)
  else
    OppUnMrk1 = OppUnMrk),
  insert(A, PropMrk, PropMrk1).
  % TODO: Do we need Att? ord_add_element(Att, (Contrary,A), Att1).
  % TODO: Support GB. gb_acyclicity_check(G, A, [Contrary], G1).

%proponent_nonasm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, step_tuple(PropUnMrk1-PropMrk1-PropGr1, O, D1, C)) :-
%  rule_choice(S, Body, proponent, [D,PropGr]),
%  \+ (member(X, Body), member(X, C)),
%  update_argument_graph(S, Body, PropMrk-PropGr, NewUnMrk, NewUnMrkAs, PropMrk1-PropGr1),
%  append_elements_nodup(NewUnMrk, PropUnMrkMinus, PropUnMrk1),
%  ord_add_elements(NewUnMrkAs, D, D1).
%  % TODO: Support GB. gb_acyclicity_check(G, S, Body, G1).

%%%%%%%%%% opponent

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SUBSIDIARY FUNCTIONS

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SUBSIDIARY FUNCTIONS - GRAPH, LIST, MISC

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SELECTION FUNCTIONS

choose_turn(P, O, Player) :-
  (if P = set.init-_-_ then
    Player = opponent
  else (if O = set.init-_ then
    Player = proponent
  else
    option(turn_choice, TurnStrategy),
    turn_choice(TurnStrategy, P, O, Player))).

turn_choice(TurnStrategy, P-_-_, O-_, Player) :-
  (if TurnStrategy = "p" then
    % proponent priority.
    (if P \= set.init then
      Player = proponent
    else
      Player = opponent)
  else (if TurnStrategy = "o" then
    % opponent priority.
    (if O \= set.init then
      Player = opponent
    else
      Player = proponent)
  else
    % The default is "s": smallest number of sentences/justification-pairs first.
    count(P, PN),
    count(O, ON),
    (if PN =< ON then
      Player = proponent
    else
      Player = opponent))).

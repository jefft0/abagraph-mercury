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
:- import_module maybe.
:- import_module require.
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
:- pred derivation(step_tuple::in, int::in, derivation_result::out, int::out) is det.
:- pred derivation_step(step_tuple::in, step_tuple::out) is det.
:- pred proponent_step(step_tuple::in, step_tuple::out) is det.
:- pred proponent_asm(sentence::in, list(sentence)::in, pair(set(sentence), arg_graph)::in, 
          opponent_arg_graph_set::in, set(sentence)::in, set(sentence)::in, step_tuple::out) is det.
%:- pred proponent_nonasm(sentence::in, list(sentence)::in, pair(set(sentence), arg_graph)::in, 
%          opponent_arg_graph_set::in, set(sentence)::in, set(sentence)::in, step_tuple::out) is det.
:- pred opponent_step(step_tuple::in, step_tuple::out) is det.
:- pred append_element_nodup(list(T)::in, T::in, list(T)::out) is det.
:- pred append_elements_nodup(list(T)::in, list(T)::in, list(T)::out) is det.
:- pred choose_turn(proponent_state::in, opponent_arg_graph_set::in, turn::out) is det.
:- pred proponent_sentence_choice(list(sentence)::in, sentence::out, list(sentence)::out) is det.
:- pred turn_choice(turn_choice::in, proponent_state::in, opponent_arg_graph_set::in, turn::out) is det.
:- pred sentence_choice(proponent_sentence_choice::in, list(sentence)::in, sentence::out, list(sentence)::out) is det.
:- pred get_first_assumption_or_other(list(sentence)::in, sentence::out, list(sentence)::out) is det.
:- pred get_first_nonassumption_or_other(list(sentence)::in, sentence::out, list(sentence)::out) is det.
:- pred get_newest_nonassumption_or_other(list(sentence)::in, sentence::out, list(sentence)::out) is det.
:- pred find_first(pred(T)::in(pred(in) is semidet), list(T)::in, T::out, list(T)::out) is semidet. 

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
  (A = fact("a") ->
    Contrary = fact("p")
  ;
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
  (verbose ->
    print_step(0, InitTuple)
  ;
    true),
  %retractall(sols(_)),
  %assert(sols(1)),
  derivation(InitTuple, 1, Result, _),
  print_result(Result),
  %incr_sols.
  true.

initial_derivation_tuple(
    PropUnMrk,
    step_tuple(O_PropUnMrk-set.init-PropGr, % PropUnMrk-PropM-PropGr
               []-[],                     % OppUnMrk-OppM (members of each are Claim-UnMrk-Mrk-Graph)
               % TODO: Support GB. 
               D0,                        % D
               set.init)) :-              % C
               % TODO: Do we need Att?
  to_sorted_list(PropUnMrk, O_PropUnMrk),
  % Instead of findall, use the set filter.
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
  (T = step_tuple([]-PropMrk-PropG, []-OppM, D, C) ->
    Result = derivation_result(PropMrk-PropG, OppM, D, C),
    N = InN
  ;
    derivation_step(T, T1),
    (verbose ->
      print_step(InN, T1)
    ;
      true),
    OutN = InN + 1,
    derivation(T1, OutN, Result, N)).

derivation_step(step_tuple(P, O, D, C), T1) :-
  choose_turn(P, O, Turn),
  (Turn = proponent ->
    proponent_step(step_tuple(P, O, D, C), T1)
  ;
    opponent_step(step_tuple(P, O, D, C), T1)).

proponent_step(step_tuple(PropUnMrk-PropMrk-PropGr, O, D, C), T1) :-
  proponent_sentence_choice(PropUnMrk, S, PropUnMrkMinus),
  (assumption(S) ->
    proponent_asm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, T1),
    poss_print_case("1.(i)")
  ;
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
  ((\+ (member(Member1, OppUnMrk), Member1 = Contrary-_-_-_), 
    \+ (member(Member2, OppMrk),   Member2 = Contrary-_-_-_)) ->
    append_element_nodup(OppUnMrk, 
      Contrary-[Contrary]-set.init-make_singleton_set(Contrary-set.init),
      OppUnMrk1)
  ;
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

% append_element_nodup(L, E, Res)
% - Res is the result of adding E to the end of L, if E is not in L
% - otherwise, Res is L
append_element_nodup([], Element, [Element]).
append_element_nodup([H|T], Element, [HOut|Rest]) :-
  (H = Element ->
    HOut = Element,
    Rest = T
  ;
    HOut = H,
    append_element_nodup(T, Element, Rest)).

% append_elements_nodup(Es, L, Res)
% - Res is the result of adding all members of Es not already in L
%   to the end of L
append_elements_nodup([], Result, Result).
append_elements_nodup([Element|Elements], InList, Result) :-
 append_element_nodup(InList, Element, OutList),
 append_elements_nodup(Elements, OutList, Result).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SELECTION FUNCTIONS

choose_turn(P, O, Player) :-
  (P = []-_-_ ->
    Player = opponent
  ;(O = []-_ ->
    Player = proponent
  ;
    get_turn_choice(TurnStrategy),
    turn_choice(TurnStrategy, P, O, Player))).

proponent_sentence_choice(P, S, Pminus) :-
  get_proponent_sentence_choice(PropSentenceStrategy),
  sentence_choice(PropSentenceStrategy, P, S, Pminus).

turn_choice(p, P-_-_, _, Player) :-
  (P \= [] ->
    Player = proponent
  ;
    Player = opponent).
turn_choice(o, _, O-_, Player) :-
  (O \= [] ->
    Player = opponent
  ;
    Player = proponent).
turn_choice(s, P-_-_, O-_, Player) :-
  length(P, PN),
  length(O, ON),
  (PN =< ON ->
    Player = proponent
  ;
    Player = opponent).

%

sentence_choice(o, Ss, S, Ssminus) :-
  ([X|Rest] = Ss ->
    S = X, Ssminus = Rest
  ;
    unexpected($file, $pred, "Ss cannot be empty")).
sentence_choice(n, Ss, S, Ssminus) :-
  (split_last(Ss, Rest, X) ->
    S = X, Ssminus = Rest
  ;
    unexpected($file, $pred, "Ss cannot be empty")).
sentence_choice(e, Ss, S, Ssminus) :-
  get_first_assumption_or_other(Ss, S, Ssminus).
sentence_choice(p, Ss, S, Ssminus) :-
  get_first_nonassumption_or_other(Ss, S, Ssminus).
sentence_choice(pn, Ss, S, Ssminus) :-
 get_newest_nonassumption_or_other(Ss, S, Ssminus).

% helpers

get_first_assumption_or_other(Ss, A, Ssminus) :-
  (find_first(assumption, Ss, First, SsminusA) ->
    A = First, Ssminus = SsminusA
  ;
    % No assumption. Get the first member.
    ([H|Rest] = Ss ->
      A = H, Ssminus = Rest
    ;
      % We don't expect this.
      unexpected($file, $pred, "Ss cannot be empty"))).

get_first_nonassumption_or_other(Ss, A, Ssminus) :-
  (find_first((pred(X::in) is semidet :- \+ assumption(X)), Ss, First, SsminusA) ->
    A = First, Ssminus = SsminusA
  ;
    % No non-assumption. Get the first member.
    ([H|Rest] = Ss ->
      A = H, Ssminus = Rest
    ;
      % We don't expect this.
      unexpected($file, $pred, "Ss cannot be empty"))).

get_newest_nonassumption_or_other(Ss, A, Ssminus) :-
  reverse(Ss, RevSs),
  (find_first((pred(X::in) is semidet :- \+ assumption(X)), RevSs, First, RevSsminus) ->
    A = First,
    reverse(RevSsminus, Ssminus)
  ;
    % No non-assumption. Get the first member.
    ([H|Rest] = Ss ->
      A = H, Ssminus = Rest
    ;
      % We don't expect this.
      unexpected($file, $pred, "Ss cannot be empty"))).

% First the first member in L where Pred(X) and set Lminus to L without it.
% Fail if can't find any Pred(X).
find_first(Pred, L, First, Lminus) :-
  % The accumulator state is MaybeFirst-LWithoutFirst
  yes(First)-Lminus = foldl(
    func(X, MaybeFirst-LPart) = AccOut :-
      ((MaybeFirst = no, Pred(X)) ->
        % We got the first.
        AccOut = yes(X)-LPart
      ;
        % Keep accumulating.
        AccOut = MaybeFirst-append(LPart, [X])),
    L, no-[]).

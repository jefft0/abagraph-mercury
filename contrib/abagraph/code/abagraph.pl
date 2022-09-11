
% FILE:         abagraph.pl
% AUTHOR:       Robert Craven [robert.craven@imperial.ac.uk]
% LANGUAGE:     Prolog
% DATE:         11/5/2014

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRELIMINARIES

:- use_module(library(samsort),    [samsort/3]).
:- use_module(library(lists),      [delete/3,
                                    remove_dups/2,
                                    reverse/2,
                                    select/3]).
:- use_module(library(ordsets),    [list_to_ord_set/2,
                                    ord_add_element/3,
                                    ord_del_element/3,
                                    ord_member/2,
                                    ord_union/3]).
:- use_module(library(ugraphs),    [add_edges/3,
                                    add_vertices/3,
                                    reduce/2]).

:- [help].
:- [loading].
:- [options].
:- [printing].

:- dynamic
 assumption/1,
 branching/2,   % used in some of the heuristics
 contrary/2,
 filestem/1,
 generation_settings/1,
 non_assumption/1,
 none/1,
 option/2,
 proving/1,
 rule/2,
 toBeProved/1,
 user_predicate/2.

% set some options

option(derivation_type, ab).
option(fileID, '_sol_').
option(num_sols, 0).    % all solutions
option(opponent_abagraph_choice, s).
option(opponent_sentence_choice, p).
option(print_to_file, fail).
option(proponent_sentence_choice, p).
option(proponent_rule_choice, l1).
option(show_solution, true).
option(turn_choice, [p,o]).
option(verbose, fail).

:-
 source_file(X),
 (
  atom_concat(Path, 'code/printing.pl', X)
  -> atom_concat(Path, 'data/', FrameworkDir),
     set_opt(frameworkdir, FrameworkDir)
 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CONTROL: entry predicates

derive_all(S) :-
 derive(S, _),
 fail.
derive_all(_).

derive(S, Result) :-
 retractall(proving(_)),
 assert(proving(S)),
 initial_derivation_tuple([S], InitTuple),
 (
  verbose
  -> print_step(0, InitTuple)
  ;  true
 ),
 retractall(sols(_)),
 assert(sols(1)),
 derivation(InitTuple, 1, Result, _),
 print_result(Result),
 incr_sols.

initial_derivation_tuple(PropUnMrk, [O_PropUnMrk-[]-PropGr,   % PropUnMrk-PropM-PropG
                                     []-[],                   % OppUnMrk-OppM (members of each are Claim-UnMrk-Mrk-Graph)
                                     [],                      % G
                                     D0,                      % D
                                     [],                      % C
                                     []]) :-                  % Att
 list_to_ord_set(PropUnMrk, O_PropUnMrk),
 findall(A, (member(A, O_PropUnMrk),
             assumption(A)),
         D0),
 findall(V-[], member(V, O_PropUnMrk), PropGr).

incr_sols :-
 sols(N),
 retractall(sols(N)),
 N1 is N + 1,
 assert(sols(N1)).
 
script_derive(S, Strategies) :-
 set_strategies(Strategies),
 script_derive(S).
 
script_derive(S) :-
 retractall(proving(_)),
 assert(proving(S)),
 initial_derivation_tuple([S], InitTuple),
 retractall(sols(_)),
 assert(sols(1)),
 (
  derivation(InitTuple, 1, _, _)
  -> format('solution~n', [])
  ;  true
 ).

script_derive_print(S, Strategies) :-
 set_strategies(Strategies),
 script_derive_print(S).
 
script_derive_print(S) :-
 retractall(proving(_)),
 assert(proving(S)),
 initial_derivation_tuple([S], InitTuple),
 retractall(sols(_)),
 assert(sols(1)),
 (
  derivation(InitTuple, 1, Result, _)
  -> print_result(Result)
  ;  format('No solution~n', [])
 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CONTROL: basic control structure

derivation([[]-PropMrk-PropG,[]-OppM|RestResult], N, [PropMrk-PropG,OppM|RestResult], N) :-
 !.
derivation(T, InN, Result, N) :-
 derivation_step(T, T1),
 (
  verbose
  -> print_step(InN, T1)
  ;  true
 ),
 OutN is InN + 1,
 derivation(T1, OutN, Result, N).

derivation_step([P,O|RestT], T1) :-
 choose_turn(P, O, Turn),
 (
  Turn = proponent
  -> proponent_step([P,O|RestT], T1)
  ;
  Turn = opponent
  -> opponent_step([P,O|RestT], T1)
 ).

proponent_step([PropUnMrk-PropMrk-PropGr|RestT], T1) :-
 proponent_sentence_choice(PropUnMrk, S, PropUnMrkMinus),
 (
  assumption(S),
  proponent_asm(S, PropUnMrkMinus, PropMrk-PropGr, RestT, T1),
  poss_print_case('1.(i)')
  ;
  non_assumption(S),
  proponent_nonasm(S, PropUnMrkMinus, PropMrk-PropGr, RestT, T1),
  poss_print_case('1.(ii)')
 ).

opponent_step([P,OppUnMrk-OppMrk|RestT], T1) :-
 opponent_abagraph_choice(OppUnMrk, OppArg, OppUnMrkMinus),
 opponent_sentence_choice(OppArg, S, OppArgMinus),
 (
  assumption(S),
  opponent_i(S, OppArgMinus, OppUnMrkMinus-OppMrk, [P|RestT], T1)
  ;
  non_assumption(S),
  opponent_ii(S, OppArgMinus, OppUnMrkMinus-OppMrk, [P|RestT], T1),
  poss_print_case('2.(ii)')
 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CASES

%%%%%%%%%% proponent

proponent_asm(A, PropUnMrkMinus, PropMrk-PropGr, [OppUnMrk-OppMrk,G,D,C,Att], [PropUnMrkMinus-PropMrk1-PropGr,OppUnMrk1-OppMrk,G1,D,C,Att1]) :-
 contrary(A, Contrary),
 (
  (\+ member(Contrary-_-_-_, OppUnMrk), \+ member(Contrary-_-_-_, OppMrk))
  -> append_element_nodup(OppUnMrk, Contrary-[Contrary]-[]-[Contrary-[]], OppUnMrk1)
  ;  OppUnMrk1 = OppUnMrk
 ),
 ord_add_element(PropMrk, A, PropMrk1),
 ord_add_element(Att, (Contrary,A), Att1),
 gb_acyclicity_check(G, A, [Contrary], G1).

proponent_nonasm(S, PropUnMrkMinus, PropMrk-PropGr, [O,G,D,C,Att], [PropUnMrk1-PropMrk1-PropGr1,O,G1,D1,C,Att]) :-
 rule_choice(S, Body, proponent, [D,PropGr]),
 \+ (member(X, Body), member(X, C)),
 update_argument_graph(S, Body, PropMrk-PropGr, NewUnMrk, NewUnMrkAs, PropMrk1-PropGr1),
 append_elements_nodup(NewUnMrk, PropUnMrkMinus, PropUnMrk1),
 ord_add_elements(NewUnMrkAs, D, D1),
 gb_acyclicity_check(G, S, Body, G1).

%%%%%%%%%% opponent

opponent_i(A, Claim-UnMrkMinus-Marked-Graph, OMinus, [P,G,D,C,Att], T1) :-
 (
  \+ member(A, D),
  (
   member(A, C)
   -> opponent_ib(A, Claim-UnMrkMinus-Marked-Graph, OMinus, [P,G,D,C,Att], T1),
      poss_print_case('2.(ib)')
   ;  opponent_ic(A, Claim-UnMrkMinus-Marked-Graph, OMinus, [P,G,D,C,Att], T1),
      poss_print_case('2.(ic)')
  )
  ;
  opponent_ia(A, Claim-UnMrkMinus-Marked-Graph, OMinus, [P,G,D,C,Att], T1),
  poss_print_case('2.(ia)')
 ).

opponent_ia(A, Claim-UnMrkMinus-Marked-Graph, OppUnMrkMinus-OppMrk, [P,G,D,C,Att], [P,OppUnMrkMinus1-OppMrk,G,D,C,Att]) :-
 (
  gb_derivation
  -> true
  ;  \+ member(A, C)    % also sound for gb? CHECK in general
 ),
 ord_add_element(Marked, A, Marked1),
 append_element_nodup(OppUnMrkMinus, Claim-UnMrkMinus-Marked1-Graph, OppUnMrkMinus1).

opponent_ib(A, Claim-UnMrkMinus-Marked-Graph, OppUnMrkMinus-OppMrk, [P,G,D,C,Att], [P,OppUnMrkMinus-OppMrk1,G1,D,C,Att]) :-
 contrary(A, Contrary),
 gb_acyclicity_check(G, Claim, [Contrary], G1),
 ord_add_element(Marked, A, Marked1),
 ord_add_element(OppMrk, Claim-UnMrkMinus-Marked1-Graph, OppMrk1).

opponent_ic(A, Claim-UnMrkMinus-Marked-Graph, OppUnMrkMinus-OppMrk, [PropUnMrk-PropMrk-PropGr,G,D,C,Att], [PropUnMrk1-PropMrk-PropGr1,OppUnMrkMinus-OppMrk1,G1,D1,C1,Att1]) :-
 contrary(A, Contrary),
 (
  ord_member(Contrary-_, PropGr)
  -> PropUnMrk = PropUnMrk1,
     PropGr = PropGr1
  ;  append_element_nodup(PropUnMrk, Contrary, PropUnMrk1),
     add_vertices(PropGr, [Contrary], PropGr1)
 ),
 (
  assumption(Contrary)
  -> ord_add_element(D, Contrary, D1)
  ;  D1 = D
 ),
 ord_add_element(C, A, C1),
 ord_add_element(Marked, A, Marked1),
 ord_add_element(OppMrk, Claim-UnMrkMinus-Marked1-Graph, OppMrk1),
 ord_add_element(Att, (Contrary,A), Att1),
 gb_acyclicity_check(G, Claim, [Contrary], G1).

opponent_ii(S, Claim-UnMrkMinus-Marked-Graph, OppUnMrkMinus-OppMrk, [P,G,D,C,Att], [P,OppUnMrkMinus1-OppMrk1,G1,D,C,Att]) :-
 findall(Body, rule(S, Body), Bodies),
 iterate_bodies(Bodies, S, Claim-UnMrkMinus-Marked-Graph, OppUnMrkMinus-OppMrk, G, C, OppUnMrkMinus1-OppMrk1, G1).

iterate_bodies([], _, _, OppUnMrkMinus-OppMrk, G, _, OppUnMrkMinus-OppMrk, G).
iterate_bodies([Body|RestBodies], S, Claim-UnMrkMinus-Marked-Graph, InOppUnMrkMinus-InOppMrk, InG, C, OppUnMrkMinus1-OppMrk1, G1) :-
 update_argument_graph(S, Body, Marked-Graph, UnMarked, _UnMarkedAs, Marked1-Graph1),
 !,
 append_elements_nodup(UnMarked, UnMrkMinus, UnMrk1),
 (
  (\+ gb_derivation, member(A, Body), ord_member(A, C))
  -> OutOppUnMrkMinus = InOppUnMrkMinus,
     append_element_nodup(InOppMrk, Claim-UnMrk1-Marked1-Graph1, OutOppMrk)
  ;  append_element_nodup(InOppUnMrkMinus, Claim-UnMrk1-Marked1-Graph1, OutOppUnMrkMinus),
     OutOppMrk = InOppMrk
 ),
 OutG = InG,
 iterate_bodies(RestBodies, S, Claim-UnMrkMinus-Marked-Graph, OutOppUnMrkMinus-OutOppMrk, OutG, C, OppUnMrkMinus1-OppMrk1, G1).
iterate_bodies([_|RestBodies], S, Claim-UnMrkMinus-Marked-Graph, OMinus, G, C, OMinus1, G1) :-
 iterate_bodies(RestBodies, S, Claim-UnMrkMinus-Marked-Graph, OMinus, G, C, OMinus1, G1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SUBSIDIARY FUNCTIONS

% gb_acyclicity_check(G, To, FromList, G1)
% - add the list of edges from members of FromList to To, to the
%   unweighted directed graph G, to form G1; check to
%   see if the result is acyclic
gb_acyclicity_check(G, To, FromList, G1) :-
 (
  gb_derivation
  -> findall(From-To, member(From, FromList), NewEdges),
     add_edges(G, NewEdges, G1),
     acyclic(G1)
  ;  G1 = G
 ).

% update_argument_graph(S, Body, Marked-Graph, Unproved, UnprovedAs, Marked1-Graph1)
% - update graph representation of an argument with rule(S, Body)
% - check updated version for acyclicity
% - record the previously unproved sentences and assumptions from body
update_argument_graph(S, Body, Marked-Graph, UnMarked, UnMarkedAs, Marked1-Graph1) :-
 filter_marked(Body, Marked, UnMarked, UnMarkedAs),
 ord_del_element(Graph, S-[], GraphMinus),
 ord_add_element(Marked, S, Marked1),
 list_to_ord_set(Body, O_Body),
 ord_add_element(GraphMinus, S-O_Body, GraphMinus1),
 findall(B-[], (member(B, O_Body),
                \+ member(B-_, GraphMinus1)),
         BodyUnMarkedGraph),
 graph_union(GraphMinus1, BodyUnMarkedGraph, Graph1),
 acyclic(Graph1).

% filter_marked(Body, AlreadyProved, Unproved, UnprovedAs)
filter_marked([], _, [], []).
filter_marked([A|RestBody], Proved, InUnproved, InUnprovedAs) :-
 assumption(A),
 !,
 (
  ord_member(A, Proved)
  -> OutUnproved = InUnproved,
     OutUnprovedAs = InUnprovedAs
  ;  InUnproved = [A|OutUnproved],
     InUnprovedAs = [A|OutUnprovedAs]
 ),
 filter_marked(RestBody, Proved, OutUnproved, OutUnprovedAs).
filter_marked([S|RestBody], Proved, InUnproved, UnprovedAs) :-
 (
  ord_member(S, Proved)
  -> OutUnproved = InUnproved
  ;  InUnproved = [S|OutUnproved]
 ),
 filter_marked(RestBody, Proved, OutUnproved, UnprovedAs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SUBSIDIARY FUNCTIONS - GRAPH, LIST, MISC

% acyclic(G)
% - true when G is an acyclic ugraph
acyclic(G) :-
 \+ (member(V-Edges, G),
     ord_member(V, Edges)),
 reduce(G, RedG),
 \+ member([_,_|_]-_, RedG).

% this is copied from ugraphs.pl
graph_union(G0, [], G) :-
 !,
 G = G0.
graph_union([], G, G).
graph_union([V1-N1|G1], [V2-N2|G2], G) :-
 compare(C, V1, V2),
 graph_union(C, V1, N1, G1, V2, N2, G2, G).

graph_union(<, V1, N1, G1, V2, N2, G2, [V1-N1|G]) :-
 graph_union(G1, [V2-N2|G2], G).
graph_union(=, V, N1, G1, _, N2, G2, [V-N|G]) :-
 ord_union(N1, N2, N),
 graph_union(G1, G2, G).
graph_union(>, V1, N1, G1, V2, N2, G2, [V2-N2|G]) :-
 graph_union([V1-N1|G1], G2, G).

% append_element_nodup(L, E, Res)
% - Res is the result of adding E to the end of L, if E is not in L
% - otherwise, Res is L
append_element_nodup([], Element, [Element]).
append_element_nodup([Element|Rest], Element, [Element|Rest]) :-
 !.
append_element_nodup([H|T], Element, [H|Rest]) :-
 append_element_nodup(T, Element, Rest).

% append_elements_nodup(Es, L, Res)
% - Res is the result of adding all members of Es not already in L
%   to the end of L
append_elements_nodup([], Result, Result).
append_elements_nodup([Element|Elements], InList, Result) :-
 append_element_nodup(InList, Element, OutList),
 append_elements_nodup(Elements, OutList, Result).

% ord_add_elements(Es, OrdSet, OrdSetOut)
%  - add all members of list Es to OrdSet, producing OrdSetOut
ord_add_elements([], OrdSet, OrdSet).
ord_add_elements([H|T], InOrdSet, OrdSet) :-
 ord_add_element(InOrdSet, H, OutOrdSet),
 ord_add_elements(T, OutOrdSet, OrdSet).

% ord_members(Es, OrdSet)
%  - all members of list Es are in OrdSet 
ord_members([], _).
ord_members([E|Es], O_Set) :-
 ord_member(E, O_Set),
 ord_members(Es, O_Set).

% assert_retract(X)
%  - assert X and retract it on backtracking
assert_retract(X) :-
 assert(X).
assert_retract(X) :-
 retract(X),
 fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SELECTION FUNCTIONS

choose_turn([]-_-_, _, opponent) :-
 !.
choose_turn(_, []-_, proponent) :-
 !.
choose_turn(P, O, Player) :-
 option(turn_choice, TurnStrategy),
 turn_choice(TurnStrategy, P, O, Player).

proponent_sentence_choice(P, S, Pminus) :-
 option(proponent_sentence_choice, PropSentenceStrategy),
 sentence_choice(PropSentenceStrategy, P, S, Pminus),
 !.

opponent_abagraph_choice(O, JC, Ominus) :-
 option(opponent_abagraph_choice, OppJCStrategy),
 opponent_abagraph_choice(OppJCStrategy, O, JC, Ominus),
 !.

opponent_sentence_choice(Claim-Ss-Marked-OGraph, Se, Claim-Ssminus-Marked-OGraph) :-
 option(opponent_sentence_choice, OppSentenceStrategy),
 sentence_choice_backtrack(OppSentenceStrategy, Ss, Se, Ssminus).

% PropInfo here holds information about the current state of
% proponent's derivations
rule_choice(Head, Body, proponent, PropInfo) :-
 findall(B, rule(Head, B), Rules),
 option(proponent_rule_choice, PropRuleStrategy),
 sort_rule_pairs(PropRuleStrategy, PropInfo, Rules, SortedRulePairs),
 !,
 member(Body, SortedRulePairs),
 rule(Head, Body).              % added to fix Fan's first bug

% this can be optimized
turn_choice([First,Second], P, O, Player) :-
 (
  (First = p, P \= []-_-_)
  -> Player = proponent
  ;
  (First = p, Second = o)
  -> Player = opponent
  ;
  (First = o, O \= []-_)
  -> Player = opponent
  ;
  (First = o, Second = p)
  -> Player = proponent
 ).
turn_choice(s, P-_-_, O-_, Player) :-
 length(P, PN),
 length(O, ON),
 (
  (PN =< ON)
  -> Player = proponent
  ;
     Player = opponent
 ).

%

sentence_choice(o, [S|Ssminus], S, Ssminus).
sentence_choice(n, Ss, S, Ssminus) :-
 append(Ssminus, [S], Ss).
sentence_choice(e, Ss, S, Ssminus) :-
 get_first_assumption_or_other(Ss, S, Ssminus).
sentence_choice(p, Ss, S, Ssminus) :-
 get_first_nonassumption_or_other(Ss, S, Ssminus).
sentence_choice(pn, Ss, S, Ssminus) :-
 get_newest_nonassumption_or_other(Ss, S, Ssminus).
sentence_choice(be, Ss, S, Ssminus) :-
 get_smallest_branching(Ss, S, Ssminus, eager).
sentence_choice(bp, Ss, S, Ssminus) :-
 get_smallest_branching(Ss, S, Ssminus, patient).

% in the following we only need to backtrack over assumptions

sentence_choice_backtrack(o, Ss, S, Ssminus) :-
 select(S, Ss, Ssminus),
 (
  \+ assumption(S)
  -> !
  ;  true
 ).
sentence_choice_backtrack(n, Ss, S, Ssminus) :-
 reverse(Ss, RevSs),
 select(S, RevSs, Ssminus),
 (
  \+ assumption(S)
  -> !
  ;  true
 ).
sentence_choice_backtrack(e, Ss, S, Ssminus) :-
 select(S, Ss, Ssminus),
 assumption(S).
sentence_choice_backtrack(e, [S|Ssminus], S, Ssminus) :-
 !.
sentence_choice_backtrack(p, Ss, S, Ssminus) :-
 select(S, Ss, Ssminus),
 \+ assumption(S),
 !.
sentence_choice_backtrack(p, Ss, S, Ssminus) :-
 select(S, Ss, Ssminus).
sentence_choice_backtrack(pn, Ss, S, Ssminus) :-
 reverse(Ss, RevSs),
 (
  select(S, RevSs, Ssminus),
  \+ assumption(S),
  !
  ;
  select(S, RevSs, Ssminus)
 ).

/* FIX THIS LATER
sentence_choice(be, Ss, S, Ssminus) :-
 get_smallest_branching(Ss, S, Ssminus, eager).
sentence_choice(bp, Ss, S, Ssminus) :-
 get_smallest_branching(Ss, S, Ssminus, patient).
*/

% the rule for the 'smallest branching' is:
%  - if the sentence is a non-assumption, then its branching coefficient
%    is the number of rules having the sentence as their head
%  - if the sentence is an assumption, then the branching coefficient
%    is found by moving along the 'conrary' relation of the sentence,
%    until a non-assumption is found; the coefficient is then the
%    the number of rules having that non-assumption as their head
%  - we find the set of sentences having the smallest branching
%    coefficient by this definition; then for a 'patient' (bp)
%    selection function, we pick a non-assumption if possible;
%    for an 'eager' selection function, we pick an assumption
%    if possible

get_smallest_branching([S|Ss], Selected, Ssminus, Type) :-
 branching(S, N),
 get_branchings(Ss, N, [S], [B|Bs]),
 (
  (  (assumption(B), Type = eager)
   ; (\+ assumption(B), Type = patient))
  -> Selected = B
  ;  get_type(Bs, Type, B, Selected)
 ),
 delete([S|Ss], Selected, Ssminus).

get_branchings([], _, Best, Best).
get_branchings([S|Ss], BestN, BestSoFar, BestFinal) :-
 branching(S, N),
 (
  N < BestN
  -> NewBestN = N,
     NewBest = [S]
  ;
  N = BestN
  -> NewBestN = BestN,
     append(BestSoFar, [S], NewBest)
  ;
  % N > BestN
     NewBestN = BestN,
     NewBest = BestSoFar
 ),
 get_branchings(Ss, NewBestN, NewBest, BestFinal).

%get_branching_coefficient(S, N) :-
% get_contrary_terminus(S, NonAss),
% findall(B, rule(NonAss, _, B), Bs),
% length(Bs, N).

get_contrary_terminus(S, S) :-
 \+ assumption(S),
 !.
get_contrary_terminus(A, S) :-
 contrary(A, C),
 get_contrary_terminus(C, S).

get_type([], _, S, S).
get_type([S|Ss], eager, BestSoFar, Best) :-
 (
  assumption(S)
  -> Best = S
  ;  get_type(Ss, eager, BestSoFar, Best)
 ).
get_type([S|Ss], patient, BestSoFar, Best) :-
 (
  \+ assumption(S)
  -> Best = S
  ;  get_type(Ss, patient, BestSoFar, Best)
 ).

%

opponent_abagraph_choice(o, [JC|Ominus], JC, Ominus).
opponent_abagraph_choice(n, O, JC, Ominus) :-
 append(Ominus, [JC], O).
opponent_abagraph_choice(s, [Claim-Ss-Marked-Graph|RestJCs], JC, Ominus) :-
 length(Ss, L),
 get_smallest_ss(RestJCs, L, Claim-Ss-Marked-Graph, JC),
 delete([Claim-Ss-Marked-Graph|RestJCs], JC, Ominus).
opponent_abagraph_choice(l, [Claim-Ss-Marked-Graph|RestJCs], JC, Ominus) :-
 length(Ss, L),
 get_largest_ss(RestJCs, L, Claim-Ss-Marked-Graph, JC),
 delete([Claim-Ss-Marked-Graph|RestJCs], JC, Ominus).
opponent_abagraph_choice(lmb, [Claim-Ss-Marked-Graph|RestJCs], JC, Ominus) :-
 maximum_branching(Ss, MB),
 get_lowest_maximum_branching(RestJCs, MB, Claim-Ss-Marked-Graph, JC),
 delete([Claim-Ss-Marked-Graph|RestJCs], JC, Ominus).

get_smallest_ss([], _, JC, JC).
get_smallest_ss([Claim-Ss-Marked-Graph|RestJCs], BestLSoFar, BestJCSoFar, BestJC) :-
 length(Ss, L), % if L = 1, could we stop?
 (
  L < BestLSoFar
  -> NewL = L,
     NewJC = Claim-Ss-Marked-Graph
  ;  NewL = BestLSoFar,
     NewJC = BestJCSoFar
 ),
 get_smallest_ss(RestJCs, NewL, NewJC, BestJC).

get_largest_ss([], _, JC, JC).
get_largest_ss([Claim-Ss-Marked-Graph|RestJCs], BestLSoFar, BestJCSoFar, BestJC) :-
 length(Ss, L),
 (
  L > BestLSoFar
  -> NewL = L,
     NewJC = Claim-Ss-Marked-Graph
  ;  NewL = BestLSoFar,
     NewJC = BestJCSoFar
 ),
 get_largest_ss(RestJCs, NewL, NewJC, BestJC).

get_lowest_maximum_branching([], _, JC, JC).
get_lowest_maximum_branching([Claim-Ss-Marked-Graph|RestJCs], BestMBSoFar, BestJCSoFar, BestJC) :-
 maximum_branching(Ss, MB),
 (
  MB < BestMBSoFar
  -> NewMB = MB,
     NewJC = Claim-Ss-Marked-Graph
  ;  NewMB = BestMBSoFar,
     NewJC = BestJCSoFar
 ),
 get_lowest_maximum_branching(RestJCs, NewMB, NewJC, BestJC).

% helpers

get_first_assumption_or_other(Ss, A, Ssminus) :-
 select(A, Ss, Ssminus),
 assumption(A),
 !.
get_first_assumption_or_other([A|Ssminus], A, Ssminus).

get_first_nonassumption_or_other(Ss, A, Ssminus) :-
 select(A, Ss, Ssminus),
 \+ assumption(A),
 !.
get_first_nonassumption_or_other([A|Ssminus], A, Ssminus).

get_newest_nonassumption_or_other(Ss, S, Ssminus) :-
 reverse(Ss, RevSs),
 select(S, RevSs, RevSsminus),
 \+ assumption(S),
 !,
 reverse(RevSsminus, Ssminus).
get_newest_nonassumption_or_other([A|Ss], A, Ss).

maximum_branching([S|Ss], MB) :-
 branching(S, B),
 maximum_branching(Ss, B, MB).

maximum_branching([], MB, MB).
maximum_branching([S|Ss], InMB, MB) :-
 branching(S, B),
 (
  B > InMB
  -> OutMB = B
  ;  OutMB = InMB
 ),
 maximum_branching(Ss, OutMB, MB).

% rule sorting

sort_rule_pairs(s, _PropInfo, Pairs, SortedPairs) :-
 samsort(rule_sort_small_bodies, Pairs, SortedPairs).
sort_rule_pairs(l1, PropInfo, Pairs, SortedPairs) :-
 samsort(rule_sort_look_ahead_1(PropInfo), Pairs, SortedPairs).

rule_sort_small_bodies(Body1, Body2) :-
 length(Body1, L1),
 length(Body2, L2),
 L1 =< L2.

% here we minimize (Body - (D \cup JsP))
rule_sort_look_ahead_1([D,P_Graph], Body1, Body2) :-
 count_nonD_nonJsP(Body1, D, P_Graph, 0, NB1),
 count_nonD_nonJsP(Body2, D, P_Graph, 0, NB2),
 NB1 =< NB2.

count_nonD_nonJsP([], _, _, N, N).
count_nonD_nonJsP([S|Rest], D, P_Graph, N, NB) :-
 \+ member(S, D),
 \+ member(S-[_|_], P_Graph),
 !,
 N1 is N + 1,
 count_nonD_nonJsP(Rest, D, P_Graph, N1, NB).
count_nonD_nonJsP([_|Rest], D, JsP, N, NB) :-
 count_nonD_nonJsP(Rest, D, JsP, N, NB).

% BRANCHING: done on loading an ABA framework
branchings :-
 assumption(A),
 \+ branching(A, _),
 get_contrary_list(A, [A], List, Branching),
 assert_branchings(List, Branching),
 fail.
branchings :-
 non_assumption(S),
 \+ branching(S, _),
 non_assumption_branching(S, Branching),
 assert(branching(S, Branching)),
 fail.
branchings.

assert_branchings([], _).
assert_branchings([S|Rest], Branching) :-
 assert(branching(S, Branching)),
 assert_branchings(Rest, Branching).

get_contrary_list(S, List, List, Branching) :-
 branching(S, Branching),
 !.
get_contrary_list(S, List, List, Branching) :-
 non_assumption(S),
 !,
 non_assumption_branching(S, Branching).
get_contrary_list(A, InList, List, Branching) :-
 contrary(A, S),
 (
  member(S, InList)
  -> List = InList,
     Branching = 1
  ;  OutList = [S|InList],
     get_contrary_list(S, OutList, List, Branching)
 ).

% S must be a non-assumption
non_assumption_branching(S, Branching) :-
 findall(B, rule(S, B), Bs),
 length(Bs, Branching).


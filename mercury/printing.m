% Ported to Mercury from abagraph in Prolog by Robert Craven:
% http://robertcraven.org/proarg/abagraph.html

:- module printing.
:- interface.

:- import_module digraph.
:- import_module list.
:- import_module pair.
:- import_module set.
:- import_module string.

:- type sentence
   ---> fact(string)
   ;    not(sentence).

:- type proponent_state == pair(pair(list(sentence),     % PropUnMrk
                                     set(sentence)),     % PropMrk
                                     digraph(sentence)). % PropG

:- type opponent_state == pair(pair(pair(sentence,           % Claim
                                         list(sentence)),    % UnMrk
                                         set(sentence)),     % Mrk
                                         digraph(sentence)). % Graph

:- type opponent_arg_graph_set == pair(list(opponent_state), % OppUnMrk
                                       set(opponent_state)). % OppMrk

:- type step_tuple 
   ---> step_tuple(proponent_state,        % PROPONENT potential argument graph
                   opponent_arg_graph_set, % Opponent argument graph set
                   set(sentence),          % D (the proponent defences)
                   set(sentence)).         % C (the opponent culprits)

:- type opponent_step_tuple 
   ---> opponent_step_tuple(proponent_state,        % PROPONENT potential argument graph
                            set(sentence),          % D (the proponent defences)
                            set(sentence)).         % C (the opponent culprits)

:- type derivation_result 
   ---> derivation_result(pair(set(sentence), digraph(sentence)), % PropMrk-PropG
                          set(opponent_state),                    % OppMrk
                          set(sentence),                          % D (the proponent defences)
                          set(sentence)).                         % C (the opponent culprits)

:- pred poss_print_case(string::in) is det.
:- pred print_step(int::in, step_tuple::in) is det.
:- pred print_result(derivation_result::in) is det.

:- implementation.

:- import_module options.

:- pred print_step_list(list(sentence)::in) is det.
:- pred print_opponent_step_list(list(opponent_state)::in) is det.
:- pred show_result(derivation_result::in) is det.
:- pred print_opponent_graphs(list(opponent_state)::in) is det.
:- pred print_to_file(derivation_result::in) is det.
:- func sentence_to_string(sentence) = string is det.
:- func sentence_list_to_string(list(sentence)) = string is det.
:- func sentence_set_to_string(set(sentence)) = string is det.
:- func arg_graph_to_string(digraph(sentence)) = string is det.
:- func opponent_state_to_string(opponent_state) = string is det.
% puts(S). Write the string S to stdout without a newline.
:- pred puts(string::in) is det.
% format(S, PolyTypes). Write string.format(S, PolyTypes) to stdout.
:- pred format(string::in, list(poly_type)::in) is det.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRINTING: DERIVATION STEPS

poss_print_case(Case) :-
 (verbose ->
   format("\nCase %s\n", [s(Case)])
 ;
   true).

print_step(N, step_tuple(PropUnMrk-PropMrk-PropGr, OppUnMrk-_OMrk, D, C)) :-
  format("*** Step %d\n", [i(N)]),
  format("P:    %s-%s-%s\n", [s(sentence_list_to_string(PropUnMrk)),
                              s(sentence_set_to_string(PropMrk)),
                              s(arg_graph_to_string(PropGr))]),
  format("O:    [", []),
  print_opponent_step_list(OppUnMrk),
  format("G:    []\n", []),
  % TODO: Support GB. print_step_list_brackets(G),
  format("D:    [", []),
  print_step_list(to_sorted_list(D)),
  format("C:    [", []),
  print_step_list(to_sorted_list(C)).

print_step_list([]) :-
  format("]\n", []).
print_step_list([H|T]) :-
  (T = [] ->
    format("%s]\n", [s(sentence_to_string(H))])
  ;
    format("%s,\n       ", [s(sentence_to_string(H))]),
    print_step_list(T)).

print_opponent_step_list([]) :-
  format("]\n", []).
print_opponent_step_list([H|T]) :-
  (T = [] ->
    format("%s]\n", [s(opponent_state_to_string(H))])
  ;
    format("%s,\n       ", [s(opponent_state_to_string(H))]),
    print_opponent_step_list(T)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRINTING: RESULTS

show_result(derivation_result(_-PGraph, OppMrk, D, C)) :-
  format("\nPGRAPH:              %s\n", [s(arg_graph_to_string(PGraph))]),
  format("DEFENCE:             %s\n", [s(sentence_set_to_string(D))]),
  format("OGRAPHS:             [", []),
  print_opponent_graphs(to_sorted_list(OppMrk)),
  format("CULPRITS:            %s\n", [s(sentence_set_to_string(C))]).
% format('ATT:                 ~w~n', [Att]),
% format('GRAPH:               ~w~n', [G]).

print_opponent_graphs([]) :-
  format("]\n", []).
print_opponent_graphs([H|T]) :-
  (T = [] ->
    format("%s]\n", [s(opponent_state_to_string(H))])
  ;
    format("%s,\n                      ", [s(opponent_state_to_string(H))]),
    print_opponent_graphs(T)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRINTING: PRINT TO FILE

print_result(Result) :-
  option(print_to_file, Print),
  (Print = "true" ->
    print_to_file(Result)
  ; 
    true),
  option(show_solution, Show),
  (Show = "true" ->
    show_result(Result)
  ;  
    true).

print_to_file(_Result) :-
  % TODO: Implement.
  true.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRINTING: HELPERS

sentence_to_string(fact(C)) = string.format("%s", [s(C)]).
sentence_to_string(not(S)) = string.format("not(%s)", [s(sentence_to_string(S))]).

sentence_list_to_string(L) =
  string.format("[%s]", [s(join_list(",", map(sentence_to_string, L)))]).

sentence_set_to_string(S) = sentence_list_to_string(to_sorted_list(S)).

arg_graph_to_string(G) = Result :-
  NodeList = map((func(V) = string.format("%s-%s", [s(sentence_to_string(V)),
                                                    s(sentence_set_to_string(Neighbors))]) :-
                    KeySet = lookup_from(G, lookup_key(G, V)),
                    Neighbors = map(func(K) = lookup_vertex(G, K), KeySet)), 
                 to_sorted_list(vertices(G))),
  Result = string.format("[%s]", [s(join_list(",", NodeList))]).

opponent_state_to_string(Claim-UnMrk-Mrk-Graph) =
  string.format("%s-%s-%s-%s", [s(sentence_to_string(Claim)),
                                s(sentence_list_to_string(UnMrk)),
                                s(sentence_set_to_string(Mrk)),
                                s(arg_graph_to_string(Graph))]).

:- pragma foreign_proc("C",
puts(S::in),
[promise_pure],
"
fputs(S, stdout);
").

format(S::in, PolyTypes::in) :- puts(string.format(S, PolyTypes)).

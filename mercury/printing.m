:- module printing.
:- interface.

:- import_module set.
:- import_module pair.
:- import_module string.

:- type sentence
   ---> fact(string)
   ;    not(sentence).

:- type arg_graph_member == pair(sentence,        % The node.
                                 set(sentence)). % Connected nodes.

:- type arg_graph == set(arg_graph_member).

:- type opponent_state == pair(pair(pair(sentence,       % Claim
                                         set(sentence)), % UnMrk
                                         set(sentence)), % Mrk
                                         arg_graph).     % Graph

:- type opponent_arg_graph_set == pair(set(opponent_state),   % OppUnMrk
                                       set(opponent_state)).  % OppMrk

:- type step_tuple 
   ---> step_tuple(pair(pair(set(sentence), set(sentence)), arg_graph), % PROPONENT potential argument graph
                   opponent_arg_graph_set,                              % Opponent argument graph set
                   set(sentence),                                       % D (the proponent defences)
                   set(sentence)).                                      % C (the opponent culprits)

:- pred print_step(int::in, step_tuple::in) is det.

:- implementation.

:- import_module list.

:- pred print_step_list(list(sentence)::in) is det.
:- pred print_opponent_step_list(list(opponent_state)::in) is det.
:- func sentence_to_string(sentence) = string is det.
:- func sentence_set_to_string(set(sentence)) = string is det.
:- func arg_graph_to_string(arg_graph) = string is det.
% puts(S). Write the string S to stdout without a newline.
:- pred puts(string::in) is det.
% format(S, PolyTypes). Write string.format(S, PolyTypes) to stdout.
:- pred format(string::in, list(poly_type)::in) is det.

print_step(N, step_tuple(PropUnMrk-PropMrk-PropGr, OppUnMrk-_OMrk, D, C)) :-
  format("*** Step %d\n", [i(N)]),
  format("P:    %s-%s-%s\n", [s(sentence_set_to_string(PropUnMrk)),
                              s(sentence_set_to_string(PropMrk)),
                              s(arg_graph_to_string(PropGr))]),
  format("O:    [", []),
  print_opponent_step_list(to_sorted_list(OppUnMrk)),
  %format("G:    [", []),
  %print_step_list_brackets(G),
  format("D:    [", []),
  print_step_list(to_sorted_list(D)),
  format("C:    [", []),
  print_step_list(to_sorted_list(C)).

print_step_list([]) :-
  format("]\n", []).
print_step_list([H|T]) :-
  (if T = [] then
    format("%s]\n", [s(sentence_to_string(H))])
  else
    format("%s,\n       ", [s(sentence_to_string(H))]),
    print_step_list(T)).

print_opponent_step_list([]) :-
  format("]\n", []).
print_opponent_step_list([Claim-UnMrk-Mrk-Graph|T]) :-
  State = format("%s-%s-%s-%s", [s(sentence_to_string(Claim)),
                                 s(sentence_set_to_string(UnMrk)),
                                 s(sentence_set_to_string(Mrk)),
                                 s(arg_graph_to_string(Graph))]),
  (if T = [] then
    format("%s]\n", [s(State)])
  else
    format("%s,\n       ", [s(State)]),
    print_opponent_step_list(T)).

sentence_to_string(fact(C)) = string.format("fact(%s)", [s(C)]).
sentence_to_string(not(S)) = string.format("not(%s)", [s(sentence_to_string(S))]).

sentence_set_to_string(S) =
  string.format("[%s]", [s(join_list(",", map(sentence_to_string, to_sorted_list(S))))]).

arg_graph_to_string(G) = Result :-
  NodeList = map((func(H-T) = string.format("%s-%s", [s(sentence_to_string(H)),
                                                      s(sentence_set_to_string(T))])), 
                 to_sorted_list(G)),
  Result = string.format("[%s]", [s(join_list(",", NodeList))]).

:- pragma foreign_proc("C",
puts(S::in),
[promise_pure],
"
fputs(S, stdout);
").

format(S::in, PolyTypes::in) :- puts(string.format(S, PolyTypes)).

:- module printing.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.
:- import_module pair.
:- import_module string.

:- type sentence
   ---> fact(string)
   ;    not(sentence).

:- pred print_step(int::in, list(sentence)::in, list(sentence)::in) is det.
:- pred print_step_list(list(sentence)::in) is det.
:- pred print_step_list_brackets(list(sentence)::in) is det.
:- func sentence_to_string(sentence) = string is det.
% puts(S). Write the string S to stdout without a newline.
:- pred puts(string::in) is det.
% format(S, PolyTypes). Write string.format(S, PolyTypes) to stdout.
:- pred format(string::in, list(poly_type)::in) is det.

main(!IO) :-
  D = fact("a") - fact("y") - fact("z"),
  print_step(2, [snd(fst(D)), fact("b"), fact("c")], [not(fact("release"))]).

print_step(N, D, C) :-
  format("*** Step %d\n", [i(N)]),
  %format("P:    ~w\n", [P]),
  %format("O:    [", []),
  %print_step_list(OppUnMrk),
  %format("G:    [", []),
  %print_step_list_brackets(G),
  format("D:    [", []),
  print_step_list(D),
  format("C:    [", []),
  print_step_list(C).

print_step_list([]) :-
  format("]\n", []).
print_step_list([H|T]) :-
  (
  if T = [] then
    format("%s]\n", [s(sentence_to_string(H))])
  else
    format("%s,\n       ", [s(sentence_to_string(H))]),
    print_step_list(T)).

print_step_list_brackets([]) :-
  format("]\n", []).
print_step_list_brackets([H|T]) :-
  (
  if T = [] then
    format("(%s)]\n", [s(sentence_to_string(H))])
  else
    format("(%s),\n       ", [s(sentence_to_string(H))]),
    print_step_list_brackets(T)).

sentence_to_string(fact(C)) = string.format("fact(%s)", [s(C)]).
sentence_to_string(not(S)) = string.format("not(%s)", [s(sentence_to_string(S))]).

:- pragma foreign_proc("C",
puts(S::in),
[promise_pure, may_call_mercury],
"
fputs(S, stdout);
").

format(S::in, PolyTypes::in) :- puts(string.format(S, PolyTypes)).

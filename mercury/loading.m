% Ported to Mercury from abagraph in Prolog by Robert Craven:
% http://robertcraven.org/proarg/abagraph.html

:- module loading.
:- interface.

:- import_module io.
:- import_module list.
:- import_module printing.
:- import_module string.

:- pred main(io::di, io::uo) is det.

:- pred assumption(sentence::in) is semidet.
:- pred rule(sentence::in, list(sentence)::out) is semidet.
:- pred contrary(sentence::in, sentence::out) is semidet.
:- func now = string is det.

:- implementation.

:- import_module abagraph.
:- import_module solutions.

main(!IO) :-
  unsorted_solutions((pred(R::out) is nondet :- derive(fact("a"), R)), _).

assumption(fact("a")).
assumption(fact("b")).

rule(not(fact("a")), [fact("b")]).
rule(not(fact("b")), []).

contrary(fact(A), not(fact(A))).

now = "0s:310ms:0us".

%non_assumptions = list_to_set(solutions((pred(S::out) is nondet :-
%                    (
%                      rule(H, Body),
%                      member(S, [H|Body]),
%                      \+ assumption(S)
%                    ;
%                      rule(_, Body),
%                      member(A, Body),
%                      assumption(A),
%                      contrary(A, S))))).

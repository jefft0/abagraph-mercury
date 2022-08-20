% Ported to Mercury from abagraph in Prolog by Robert Craven:
% http://robertcraven.org/proarg/abagraph.html

:- module loading.
:- interface.

:- import_module list.
:- import_module printing.
:- import_module set.

:- pred assumption(sentence).
:- mode assumption(in) is semidet.
:- mode assumption(out) is multi.
:- pred rule(sentence, list(sentence)).
:- mode rule(in, out) is semidet.
:- mode rule(out, out) is multi.
:- pred contrary(sentence::in, sentence::out) is semidet.
:- func non_assumptions = set(sentence) is det.

:- implementation.

:- import_module solutions.

assumption(fact("a")).
assumption(fact("b")).

rule(not(fact("a")), [fact("b")]).
rule(not(fact("b")), []).

contrary(fact(A), not(fact(A))).

non_assumptions = list_to_set(solutions((pred(S::out) is nondet :- 
                    (
                      rule(H, Body),
                      member(S, [H|Body])
                    ;
                      assumption(A),
                      contrary(A, S)
                    ),
                    \+ assumption(S)))).

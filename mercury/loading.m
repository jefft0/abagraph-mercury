% Ported to Mercury from abagraph in Prolog by Robert Craven:
% http://robertcraven.org/proarg/abagraph.html

:- module loading.
:- interface.

:- import_module io.
:- import_module list.
:- import_module string.
:- import_module constraints.

:- type sentence
   ---> fact(string)
   ;    not(sentence)
   ;    f(var_f_constraint)
   ;    i(var_i_constraint)
   ;    s(var_s_constraint).

:- pred main(io::di, io::uo) is det.

:- pred assumption(sentence::in) is semidet.
:- pred constraint(sentence::in) is failure. % Normally semidet
:- pred rule(sentence::in, list(sentence)::out) is semidet.
:- pred contrary(sentence::in, sentence::out) is semidet.
:- pred exclusive(sentence::in, sentence::in) is failure. % Normally semidet
:- func decompiled_path = string is det.
:- func runtime_out_path = string is det.
:- func now = string is det.
:- pred is_event(sentence::in) is semidet.
% matches(S1, S2).
% Return the boolean expression for when S1 matches S2.
% Fail if no match is possible.
:- func matches(sentence, sentence) = b_constraint is semidet.
:- func sentence_to_string(sentence) = string is det.
% write_sentence(S, Fd, Id). Write sentence S to the file at Fd. Set Id to its ID.
:- pred write_sentence(sentence::in, uint64::in, int::out) is det.

:- implementation.

:- import_module abagraph.
:- import_module printing.
:- import_module solutions.

main(!IO) :-
  unsorted_solutions((pred(R::out) is nondet :- derive(fact("a"), R)), _).

assumption(fact("a")).
assumption(fact("b")).

contrary(fact(A), not(fact(A))).

constraint(_) :- fail.

rule(not(fact("a")), [fact("b")]).
rule(not(fact("b")), []).

exclusive(_, _) :- fail.

decompiled_path = "".
runtime_out_path = "".

now = "0s:310ms:0us".

is_event(fact("event")).

matches(S, S) = t.

sentence_to_string(fact(C)) = format("%s", [s(C)]).
sentence_to_string(not(S)) = format("not(%s)", [s(sentence_to_string(S))]).
sentence_to_string(f(C)) = var_f_constraint_to_string(C).
sentence_to_string(i(C)) = var_i_constraint_to_string(C).
sentence_to_string(s(C)) = var_s_constraint_to_string(C).

write_sentence(S, Fd, 0) :-
  format(Fd, "%s\n", [s(sentence_to_string(S))]).

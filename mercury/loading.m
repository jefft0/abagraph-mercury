% Ported to Mercury from abagraph in Prolog by Robert Craven:
% http://robertcraven.org/proarg/abagraph.html

:- module loading.
:- interface.

:- import_module io.
:- import_module list.
:- import_module string.

:- type sentence
   ---> fact(string)
   ;    not(sentence).

:- pred main(io::di, io::uo) is det.

:- pred assumption(sentence::in) is semidet.
:- pred constraint(sentence::in) is semidet.
:- pred rule(sentence::in, list(sentence)::out) is semidet.
:- pred contrary(sentence::in, sentence::out) is semidet.
:- func decompiled_path = string is det.
:- func runtime_out_path = string is det.
:- func now = string is det.
:- pred is_event(sentence::in) is semidet.
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

constraint(_) :- fail.

rule(not(fact("a")), [fact("b")]).
rule(not(fact("b")), []).

contrary(fact(A), not(fact(A))).

decompiled_path = "".
runtime_out_path = "".

now = "0s:310ms:0us".

is_event(fact("event")).

sentence_to_string(fact(C)) = format("%s", [s(C)]).
sentence_to_string(not(S)) = format("not(%s)", [s(sentence_to_string(S))]).

write_sentence(S, Fd, 0) :-
  format(Fd, "%s\n", [s(sentence_to_string(S))]).

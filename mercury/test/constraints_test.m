:- module constraints_test.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module constraints.
:- import_module list.
:- import_module maybe.
:- import_module string.

:- pred test1 is semidet.
:- pred test2 is semidet.
% puts(S). Write the string S to stdout without a newline.
:- pred puts(string::in) is det.
% format(S, PolyTypes). Write string.format(S, PolyTypes) to stdout.
:- pred format(string::in, list(poly_type)::in) is det.

main(!IO) :-
  (test1, test2 -> 
    format("Pass\n", [])
  ;
    format("Fail\n", [])).

test1 :-
  Cs = constraints.init,
  unify(1, i('+'(var(2), 5)), Cs, Cs1, _),
  unify(1, i(':='(20)), Cs1, Cs2, _),
  i_get(2, Cs2) = yes(15).

test2 :-
  Cs = constraints.init,
  unify(1, s('\\=='(var(2))), Cs, Cs1, _),
  unify(1, s(':='("a")), Cs1, Cs2, _),
  \+ unify(2, s(':='("a")), Cs2, _, _).

:- pragma foreign_proc("C",
puts(S::in),
[promise_pure],
"
fputs(S, stdout);
").

format(S, PolyTypes) :- puts(format(S, PolyTypes)).

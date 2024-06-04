:- module constraints_test.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module constraints.
:- import_module int.
:- import_module list.
:- import_module maybe.
:- import_module string.

:- pred run_test(pred(constraint_store)).
:- mode run_test(pred(in) is semidet) is det.

% puts(S). Write the string S to stdout without a newline.
:- pred puts(string::in) is det.
% format(S, PolyTypes). Write string.format(S, PolyTypes) to stdout.
:- pred format(string::in, list(poly_type)::in) is det.

main(!IO) :-
  % Test int \=
  run_test((pred(CS::in) is semidet :-
    unify(1, i('\\='(10)), CS, CS1, _),
    unify(1, i(':='(11)), CS1, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(10)), CS, CS1, _),
    unify(1, i('\\='(11)), CS1, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i('\\='(10)), CS, CS1, _),
    \+ unify(1, i(':='(10)), CS1, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(10)), CS, CS1, _),
    \+ unify(1, i('\\='(10)), CS1, _, _))),

  % Test int \==
  run_test((pred(CS::in) is semidet :-
    unify(1, i('\\=='(var(2))), CS, CS1, _),
    unify(1, i(':='(10)), CS1, CS2, _),
    unify(2, i(':='(11)), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(10)), CS, CS1, _),
    unify(1, i('\\=='(var(2))), CS1, CS2, _),
    unify(2, i(':='(11)), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(2, i(':='(11)), CS, CS1, _),
    unify(1, i('\\=='(var(2))), CS1, CS2, _),
    unify(1, i(':='(10)), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(10)), CS, CS1, _),
    unify(2, i(':='(11)), CS1, CS2, _),
    unify(1, i('\\=='(var(2))), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i('\\=='(var(2))), CS, CS1, _),
    unify(1, i(':='(10)), CS1, CS2, _),
    \+ unify(2, i(':='(10)), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(10)), CS, CS1, _),
    unify(1, i('\\=='(var(2))), CS1, CS2, _),
    \+ unify(2, i(':='(10)), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(10)), CS, CS1, _),
    unify(2, i(':='(10)), CS1, CS2, _),
    \+ unify(1, i('\\=='(var(2))), CS2, _, _))),

  % Test int +
  run_test((pred(CS::in) is semidet :-
    unify(1, i('+'(var(2), 5)), CS, CS1, _),
    unify(1, i(':='(20)), CS1, CS2, _),
    unify(2, i(':='(15)), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(20)), CS, CS1, _),
    unify(1, i('+'(var(2), 5)), CS1, CS2, _),
    unify(2, i(':='(15)), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(20)), CS, CS1, _),
    unify(2, i(':='(15)), CS1, CS2, _),
    unify(1, i('+'(var(2), 5)), CS2, _, _))),

  % Test int ++
  run_test((pred(CS::in) is semidet :-
    unify(1, i('++'(var(2), var(3))), CS, CS1, _),
    unify(1, i(':='(20)), CS1, CS2, _),
    unify(2, i(':='(5)), CS2, CS3, _),
    unify(3, i(':='(15)), CS3, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(20)), CS, CS1, _),
    unify(1, i('++'(var(2), var(3))), CS1, CS2, _),
    unify(2, i(':='(5)), CS2, CS3, _),
    unify(3, i(':='(15)), CS3, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(2, i(':='(5)), CS, CS1, _),
    unify(1, i('++'(var(2), var(3))), CS1, CS2, _),
    unify(1, i(':='(20)), CS2, CS3, _),
    unify(3, i(':='(15)), CS3, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(20)), CS, CS1, _),
    unify(2, i(':='(5)), CS1, CS2, _),
    unify(1, i('++'(var(2), var(3))), CS2, CS3, _),
    unify(3, i(':='(15)), CS3, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(20)), CS, CS1, _),
    unify(2, i(':='(5)), CS1, CS2, _),
    unify(3, i(':='(15)), CS2, CS3, _),
    unify(1, i('++'(var(2), var(3))), CS3, _, _))),

  % Test int -
  run_test((pred(CS::in) is semidet :-
    unify(1, i('-'(20, var(2))), CS, CS1, _),
    unify(1, i(':='(15)), CS1, CS2, _),
    unify(2, i(':='(5)), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(15)), CS, CS1, _),
    unify(1, i('-'(20, var(2))), CS1, CS2, _),
    unify(2, i(':='(5)), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(15)), CS, CS1, _),
    unify(2, i(':='(5)), CS1, CS2, _),
    unify(1, i('-'(20, var(2))), CS2, _, _))),

  % Test int --
  run_test((pred(CS::in) is semidet :-
    unify(1, i('--'(var(2), var(3))), CS, CS1, _),
    unify(1, i(':='(15)), CS1, CS2, _),
    unify(2, i(':='(20)), CS2, CS3, _),
    unify(3, i(':='(5)), CS3, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(15)), CS, CS1, _),
    unify(1, i('--'(var(2), var(3))), CS1, CS2, _),
    unify(2, i(':='(20)), CS2, CS3, _),
    unify(3, i(':='(5)), CS3, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(3, i(':='(5)), CS, CS1, _),
    unify(1, i('--'(var(2), var(3))), CS1, CS2, _),
    unify(1, i(':='(15)), CS2, CS3, _),
    unify(2, i(':='(20)), CS3, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(2, i(':='(20)), CS, CS1, _),
    unify(1, i('--'(var(2), var(3))), CS1, CS2, _),
    unify(1, i(':='(15)), CS2, CS3, _),
    unify(3, i(':='(5)), CS3, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(15)), CS, CS1, _),
    unify(2, i(':='(20)), CS1, CS2, _),
    unify(1, i('--'(var(2), var(3))), CS2, CS3, _),
    unify(3, i(':='(5)), CS3, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(15)), CS, CS1, _),
    unify(2, i(':='(20)), CS1, CS2, _),
    unify(3, i(':='(5)), CS2, CS3, _),
    unify(1, i('--'(var(2), var(3))), CS3, _, _))),

  % Test int =<
  run_test((pred(CS::in) is semidet :-
    unify(1, i('=<'(2)), CS, CS1, _),
    unify(1, i(':='(1)), CS1, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(1)), CS, CS1, _),
    unify(1, i('=<'(2)), CS1, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(2)), CS, CS1, _),
    unify(1, i('=<'(2)), CS1, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i(':='(3)), CS, CS1, _),
    \+ unify(1, i('=<'(2)), CS1, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i('=<'(5)), CS, CS1, _),
    unify(1, i('=<'(2)), CS1, CS2, _), % Tighten
    \+ unify(1, i(':='(3)), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i('=<'(2)), CS, CS1, _),
    unify(1, i('=<'(5)), CS1, CS2, _), % Don't loosen.
    \+ unify(1, i(':='(3)), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i('=<'(2)), CS, CS1, _),
    unify(2, i('+'(var(1), 10)), CS1, CS2, _), % Adds (<= (var 2) 12)
    unify(2, i(':='(11)), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, i('=<'(2)), CS, CS1, _),
    format("CS1\n%s", [s(to_string(CS1))]),
    unify(2, i('+'(var(1), 10)), CS1, CS2, _), % Adds (<= (var 2) 12)
    format("CS2\n%s", [s(to_string(CS2))]),
    \+ unify(2, i(':='(13)), CS2, _, _))),

  % Test string \=
  run_test((pred(CS::in) is semidet :-
    unify(1, s('\\='("a")), CS, CS1, _),
    unify(1, s(':='("b")), CS1, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, s(':='("a")), CS, CS1, _),
    unify(1, s('\\='("b")), CS1, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, s('\\='("a")), CS, CS1, _),
    \+ unify(1, s(':='("a")), CS1, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, s(':='("a")), CS, CS1, _),
    \+ unify(1, s('\\='("a")), CS1, _, _))),

  % Test string \==
  run_test((pred(CS::in) is semidet :-
    unify(1, s('\\=='(var(2))), CS, CS1, _),
    unify(1, s(':='("a")), CS1, CS2, _),
    unify(2, s(':='("b")), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, s(':='("a")), CS, CS1, _),
    unify(1, s('\\=='(var(2))), CS1, CS2, _),
    unify(2, s(':='("b")), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(2, s(':='("b")), CS, CS1, _),
    unify(1, s('\\=='(var(2))), CS1, CS2, _),
    unify(1, s(':='("a")), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, s(':='("a")), CS, CS1, _),
    unify(2, s(':='("b")), CS1, CS2, _),
    unify(1, s('\\=='(var(2))), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, s('\\=='(var(2))), CS, CS1, _),
    unify(1, s(':='("a")), CS1, CS2, _),
    \+ unify(2, s(':='("a")), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, s(':='("a")), CS, CS1, _),
    unify(1, s('\\=='(var(2))), CS1, CS2, _),
    \+ unify(2, s(':='("a")), CS2, _, _))),
  run_test((pred(CS::in) is semidet :-
    unify(1, s(':='("a")), CS, CS1, _),
    unify(2, s(':='("a")), CS1, CS2, _),
    \+ unify(1, s('\\=='(var(2))), CS2, _, _))).

run_test(Test) :- (Test(constraints.init) -> format("pass\n", []) ; format("FAIL\n", [])).

:- pragma foreign_proc("C",
puts(S::in),
[promise_pure],
"
fputs(S, stdout);
").

format(S, PolyTypes) :- puts(format(S, PolyTypes)).

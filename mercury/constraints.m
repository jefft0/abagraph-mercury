:- module constraints.
:- interface.

:- import_module map.
:- import_module set.

:- type variable(T) ---> var(int).

:- type f_constraint
   ---> '='(float)
   ;    '+'(variable(float), variable(float))
   ;    '-'(variable(float), variable(float)).

:- type s_constraint
   ---> '='(string).

:- type constraint
   ---> f(f_constraint)
   ;    s(s_constraint).

:- type constraints == map(int, constraint).

:- func init = constraints.
% If there is no binding for V, add one for V and the constraint and set Descs to
% a set of description strings for the bindings (only if verbose).
% If there is a binding for V, confirm the constraint and set Descs to "",
% else if the constraint is not confirmed then fail.
:- pred unify(int::in, constraint::in, constraints::in, constraints::out, set(string)::out) is semidet.

:- implementation.

:- import_module float.
:- import_module list.
:- import_module maybe.
:- import_module options.
:- import_module string.

%:- pred f_val(constraints::in, f_constraint::in, set(int)::in, set(int)::out, maybe(float)::out) is semidet.

init = map.init.

unify(V, f('='(Val)), Bs, BsOut, Descs) :-
  (search(Bs, V, C) ->
    C = f('='(BoundVal)),
    Val = BoundVal,
    BsOut = Bs,
    Descs = set.init
  ;
    % Add the binding.
    BsOut = insert(Bs, V, f('='(Val))),
    (verbose ->
      Descs = make_singleton_set(format("(var %i) = %f", [i(V), f(Val)]))
    ; 
      Descs = set.init)).
unify(V, f(var(X) - var(Y)), Bs, BsOut, Descs) :-
  (search(Bs, X, f('='(XVal))), search(Bs, Y, f('='(YVal))) ->
    Evaluated = yes(XVal - YVal)
  ;
    Evaluated = no),

  (search(Bs, V, C) ->
    C = f('='(BoundVal)),
    Evaluated = yes(Val),
    Val = BoundVal,
    BsOut = Bs,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      BsOut = insert(Bs, V, f('='(Val))),
      (verbose ->
        Descs = make_singleton_set(format("(var %i) = %f", [i(V), f(Val)]))
      ; 
        Descs = set.init)
    ;
      BsOut = insert(Bs, V, f(var(X) - var(Y))),
      Descs = set.init)).
unify(V, s('='(Val)), Bs, BsOut, Descs) :-
  (search(Bs, V, s('='(BoundVal))) ->
    Val = BoundVal,
    BsOut = Bs,
    Descs = set.init
  ;
    % Add the binding.
    BsOut = insert(Bs, V, s('='(Val))),
    (verbose ->
      Descs = make_singleton_set(format("(var %i) = %s", [i(V), s(Val)]))
    ; 
      Descs = set.init)).

%f_val(Bs, '='(Val), Checked, Checked, yes(Val)).

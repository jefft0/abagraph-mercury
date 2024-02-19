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

:- pred f_new_value(int::in, float::in, constraints::in, constraints::out, set(string)::out) is det.

init = map.init.

unify(V, f('='(Val)), Bs, BsOut, Descs) :-
  (search(Bs, V, C) ->
    C = f('='(BoundVal)),
    Val = BoundVal,
    BsOut = Bs,
    Descs = set.init
  ;
    % Add the binding.
    BsOut1 = insert(Bs, V, f('='(Val))),
    f_new_value(V, Val, BsOut1, BsOut, Descs1),
    (verbose ->
      Descs = insert(Descs1, format("(var %i) = %f", [i(V), f(Val)]))
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
      % TODO: Call f_new_value.
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

f_new_value(V, Val, Bs, BsOut, Descs) :-
  % TODO: foldl to check all.
  OtherV = 10,
  (search(Bs, OtherV, f(var(X) - var(V))), search(Bs, X, f('='(XVal))) ->
    % Replace the expression with a value.
    (unify(OtherV, f('='(XVal - Val)), delete(Bs, OtherV), BsOut1, Descs1) ->
      BsOut = BsOut1,
      Descs = Descs1
    ;
      % This shouldn't happen.
      BsOut = Bs,
      Descs = set.init)
  ;
    BsOut = Bs,
    Descs = set.init).

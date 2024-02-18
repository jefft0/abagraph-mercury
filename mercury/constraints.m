:- module constraints.
:- interface.

:- import_module map.

:- type variable(T) ---> var(int).

:- type f_constraint
   ---> '='(float).

:- type s_constraint
   ---> '='(string).

:- type constraint
   ---> f(f_constraint)
   ;    s(s_constraint).

:- type constraints == map(int, constraint).

:- func init = constraints.
:- pred unify(int::in, constraint::in, constraints::in, constraints::out, string::out) is semidet.

:- implementation.

:- import_module list.
:- import_module options.
:- import_module string.

init = map.init.

% If there is no binding for V, add one for V and the constraint and set Desc to
% a description string (only if verbose).
% If there is a binding for V, confirm the constraint and set Desc to "",
% else if the constraint is not confirmed then fail.
unify(V, f('='(Val)), Bs, BsOut, Desc) :-
  (search(Bs, V, f('='(BoundVal))) ->
    Val = BoundVal,
    BsOut = Bs,
    Desc = ""
  ;
    % Add the binding.
    BsOut = insert(Bs, V, f('='(Val))),
    (verbose ->
      Desc = format("(var %i) = %f", [i(V), f(Val)])
    ; 
      Desc = "")).
unify(V, s('='(Val)), Bs, BsOut, Desc) :-
  (search(Bs, V, s('='(BoundVal))) ->
    Val = BoundVal,
    BsOut = Bs,
    Desc = ""
  ;
    % Add the binding.
    BsOut = insert(Bs, V, s('='(Val))),
    (verbose ->
      Desc = format("(var %i) = %s", [i(V), s(Val)])
    ; 
      Desc = "")).

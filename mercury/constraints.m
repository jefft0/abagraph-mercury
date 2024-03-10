:- module constraints.
:- interface.

:- import_module map.
:- import_module set.

:- type var(T) ---> var(int).

:- type f_constraint
   ---> ':='(float)
   ;    '+'(var(float), float)
   ;    '--'(var(float), var(float))
   ;    '=<'(float).

:- type i_constraint
   ---> ':='(int)
   ;    '+'(var(int), int)
   ;    '--'(var(int), var(int))
   ;    '=<'(int).

:- type s_constraint
   ---> ':='(string).

:- type constraint
   ---> f(f_constraint)
   ;    i(i_constraint)
   ;    s(s_constraint).

% A variable is either the bound value val(X) or constraints cs.
% (We don't put the ':=' constraint in cs.)
:- type f_constraints
   ---> val(float)
   ;    cs(f_constraint).
:- type i_constraints
   ---> val(int)
   ;    cs(i_constraint).
:- type s_constraints
   ---> val(string)
   ;    cs(s_constraint).

:- type constraints ---> constraints(map(int, f_constraints), map(int, i_constraints), map(int, s_constraints)).

:- func init = constraints.

% unify(V, C, Cs, CsOut, Descs).
% If there is no binding for V, add one for V and the constraint C and set Descs to
% a set of description strings for the bindings (only if verbose).
% If there is a binding for V, confirm the constraint and set Descs to "",
% else if the constraint is not confirmed then fail.
:- pred unify(int::in, constraint::in, constraints::in, constraints::out, set(string)::out) is semidet.

:- func f_constraint_to_string(int, f_constraint) = string is det.
:- func i_constraint_to_string(int, i_constraint) = string is det.
:- func s_constraint_to_string(int, s_constraint) = string is det.

:- implementation.

:- import_module float.
:- import_module int.
:- import_module list.
:- import_module maybe.
:- import_module options.
:- import_module pair.
:- import_module string.

:- pred f_unify(int::in, f_constraint::in, map(int, f_constraints)::in, map(int, f_constraints)::out, set(string)::out) is semidet.
:- pred i_unify(int::in, i_constraint::in, map(int, i_constraints)::in, map(int, i_constraints)::out, set(string)::out) is semidet.
:- pred s_unify(int::in, s_constraint::in, map(int, s_constraints)::in, map(int, s_constraints)::out, set(string)::out) is semidet.
:- pred f_set_binding(int::in, float::in, map(int, f_constraints)::in, map(int, f_constraints)::out, set(string)::out) is det.
:- pred i_set_binding(int::in, int::in, map(int, i_constraints)::in, map(int, i_constraints)::out, set(string)::out) is det.
:- pred s_set_binding(int::in, string::in, map(int, s_constraints)::in, map(int, s_constraints)::out, set(string)::out) is det.
:- pred f_new_value(int::in, float::in, map(int, f_constraints)::in, map(int, f_constraints)::out, set(string)::out) is det.
:- pred i_new_value(int::in, int::in, map(int, i_constraints)::in, map(int, i_constraints)::out, set(string)::out) is det.

init = constraints(map.init, map.init, map.init).

% Dispatch unify to f_unify, i_unify, etc.
unify(V, f(FC), constraints(FCs, ICs, SCs), constraints(FCsOut, ICs, SCs), Descs) :- f_unify(V, FC, FCs, FCsOut, Descs).
unify(V, i(IC), constraints(FCs, ICs, SCs), constraints(FCs, ICsOut, SCs), Descs) :- i_unify(V, IC, ICs, ICsOut, Descs).
unify(V, s(SC), constraints(FCs, ICs, SCs), constraints(FCs, ICs, SCsOut), Descs) :- s_unify(V, SC, SCs, SCsOut, Descs).

f_unify(V, ':='(Val), Cs, CsOut, Descs) :-
  (search(Cs, V, C) ->
    C = val(BoundVal),
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    f_set_binding(V, Val, Cs, CsOut, Descs)).
f_unify(V, var(X) + Y, Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    Evaluated = yes(XVal + Y)
  ;
    Evaluated = no),

  (search(Cs, V, C) ->
    C = val(BoundVal),
    Evaluated = yes(Val),
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      f_set_binding(V, Val, Cs, CsOut, Descs)
    ;
      CsOut = set(Cs, V, cs(var(X) + Y)),
      Descs = set.init)).
f_unify(V, var(X) -- var(Y), Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)), search(Cs, Y, val(YVal)) ->
    Evaluated = yes(XVal - YVal)
  ;
    Evaluated = no),

  (search(Cs, V, C) ->
    C = val(BoundVal),
    Evaluated = yes(Val),
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      f_set_binding(V, Val, Cs, CsOut, Descs)
    ;
      CsOut = set(Cs, V, cs(var(X) -- var(Y))),
      Descs = set.init)).
f_unify(V, '=<'(Val), Cs, CsOut, Descs) :-
%  (search(Cs, V, ':='(BoundVal)) ->
%    BoundVal =< Val,
%    CsOut = Cs,
%    Descs = set.init
%  ;
%    % TODO: Check for another constraint.
%    % Add the binding.
%    CsOut = insert(Cs, V, '=<'(Val)),
%    (verbose ->
%      Descs = make_singleton_set(format("(var %i) <= %i", [i(V), i(Val)]))
%    ; 
%      Descs = set.init)).
  CsOut = Cs, Descs = make_singleton_set(format("(var %i) <= %f", [i(V), f(Val)])).
i_unify(V, ':='(Val), Cs, CsOut, Descs) :-
  (search(Cs, V, C) ->
    C = val(BoundVal),
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    i_set_binding(V, Val, Cs, CsOut, Descs)).
i_unify(V, var(X) + Y, Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    Evaluated = yes(XVal + Y)
  ;
    Evaluated = no),

  (search(Cs, V, C) ->
    C = val(BoundVal),
    Evaluated = yes(Val),
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      i_set_binding(V, Val, Cs, CsOut, Descs)
    ;
      CsOut = set(Cs, V, cs(var(X) + Y)),
      Descs = set.init)).
i_unify(V, var(X) -- var(Y), Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)), search(Cs, Y, val(YVal)) ->
    Evaluated = yes(XVal - YVal)
  ;
    Evaluated = no),

  (search(Cs, V, C) ->
    C = val(BoundVal),
    Evaluated = yes(Val),
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      i_set_binding(V, Val, Cs, CsOut, Descs)
    ;
      CsOut = set(Cs, V, cs(var(X) -- var(Y))),
      Descs = set.init)).
i_unify(V, '=<'(Val), Cs, CsOut, Descs) :-
%  (search(Cs, V, ':='(BoundVal)) ->
%    BoundVal =< Val,
%    CsOut = Cs,
%    Descs = set.init
%  ;
%    % TODO: Check for another constraint.
%    % Add the binding.
%    CsOut = insert(Cs, V, '=<'(Val)),
%    (verbose ->
%      Descs = make_singleton_set(format("(var %i) <= %i", [i(V), i(Val)]))
%    ; 
%      Descs = set.init)).
  CsOut = Cs, Descs = make_singleton_set(format("(var %i) <= %i", [i(V), i(Val)])).
s_unify(V, ':='(Val), Cs, CsOut, Descs) :-
  (search(Cs, V, val(BoundVal)) ->
    Val = BoundVal,
    CsOut = Cs,
    Descs = set.init
  ;
    s_set_binding(V, Val, Cs, CsOut, Descs)).

f_set_binding(V, Val, Cs, CsOut, Descs) :-
  % Set the binding as the only constraint.
  Cs1 = set(Cs, V, val(Val)),
  f_new_value(V, Val, Cs1, CsOut, Descs1),
  (verbose ->
    Descs = insert(Descs1, format("(var %i) = %f", [i(V), f(Val)]))
  ; 
    Descs = Descs1).

i_set_binding(V, Val, Cs, CsOut, Descs) :-
  % Set the binding as the only constraint.
  Cs1 = set(Cs, V, val(Val)),
  i_new_value(V, Val, Cs1, CsOut, Descs1),
  (verbose ->
    Descs = insert(Descs1, format("(var %i) = %i", [i(V), i(Val)]))
  ; 
    Descs = Descs1).

s_set_binding(V, Val, Cs, CsOut, Descs) :-
  % Set the binding as the only constraint.
  CsOut = set(Cs, V, val(Val)),
  (verbose ->
    Descs = make_singleton_set(format("(var %i) = %s", [i(V), s(Val)]))
  ; 
    Descs = set.init).

f_new_value(V, Val, Cs, CsOut, Descs) :-
  CsOut-Descs = foldl(
    (func(OtherV, CsIn-DescsIn) = Cs1-Descs1 :-
      % Try to get the value of OtherV.
      (search(CsIn, OtherV, cs(OtherC)) ->
        (OtherC = var(V) + Y1 ->
          OtherVal = yes(Val + Y1)
        ;(OtherC = var(X) -- var(V), search(CsIn, X, val(XVal)) ->
          OtherVal = yes(XVal - Val)
        ;(OtherC = var(V) -- var(Y), search(CsIn, Y, val(YVal)) ->
          OtherVal = yes(Val - YVal)
        ;
          OtherVal = no)))
      ;
        OtherVal = no),

      (OtherVal = yes(NewVal) ->
        % Replace OtherV with the evaluated value and maybe propagate.
        (f_unify(OtherV, ':='(NewVal), delete(CsIn, OtherV), Cs2, Descs2) ->
          Cs1 = Cs2,
          Descs1 = union(DescsIn, Descs2)
        ;
          % This shouldn't happen.
          Cs1 = CsIn,
          Descs1 = DescsIn)
      ;
        Cs1 = CsIn,
        Descs1 = DescsIn)),
    % Only use the map keys because f_unify can update the values.
    keys(Cs), Cs-set.init).

i_new_value(V, Val, Cs, CsOut, Descs) :-
  CsOut-Descs = foldl(
    (func(OtherV, CsIn-DescsIn) = Cs1-Descs1 :-
      % Try to get the value of OtherV.
      (search(CsIn, OtherV, cs(OtherC)) ->
        (OtherC = var(V) + Y1 ->
          OtherVal = yes(Val + Y1)
        ;(OtherC = var(X) -- var(V), search(CsIn, X, val(XVal)) ->
          OtherVal = yes(XVal - Val)
        ;(OtherC = var(V) -- var(Y), search(CsIn, Y, val(YVal)) ->
          OtherVal = yes(Val - YVal)
        ;
          OtherVal = no)))
      ;
        OtherVal = no),

      (OtherVal = yes(NewVal) ->
        % Replace OtherV with the evaluated value and maybe propagate.
        (i_unify(OtherV, ':='(NewVal), delete(CsIn, OtherV), Cs2, Descs2) ->
          Cs1 = Cs2,
          Descs1 = union(DescsIn, Descs2)
        ;
          % This shouldn't happen.
          Cs1 = CsIn,
          Descs1 = DescsIn)
      ;
        Cs1 = CsIn,
        Descs1 = DescsIn)),
    % Only use the map keys because i_unify can update the values.
    keys(Cs), Cs-set.init).

f_constraint_to_string(V, ':='(Val)) =          format("(= (var %i) %f)", [i(V), f(Val)]).
f_constraint_to_string(V, var(X1) + X2) =       format("(= (var %i) (+ (var %i) %f)", [i(V), i(X1), f(X2)]).
f_constraint_to_string(V, var(X1) -- var(X2)) = format("(= (var %i) (- (var %i) (var %i))", [i(V), i(X1), i(X2)]).
f_constraint_to_string(V, '=<'(X)) =            format("(<= (var %i) %f)", [i(V), f(X)]).
i_constraint_to_string(V, ':='(Val)) =          format("(= (var %i) %i)", [i(V), i(Val)]).
i_constraint_to_string(V, var(X1) + X2) =       format("(= (var %i) (+ (var %i) %i)", [i(V), i(X1), i(X2)]).
i_constraint_to_string(V, var(X1) -- var(X2)) = format("(= (var %i) (- (var %i) (var %i))", [i(V), i(X1), i(X2)]).
i_constraint_to_string(V, '=<'(X)) =            format("(<= (var %i) %i)", [i(V), i(X)]).
s_constraint_to_string(V, ':='(Val)) =          format("(= (var %i) %s)", [i(V), s(Val)]).

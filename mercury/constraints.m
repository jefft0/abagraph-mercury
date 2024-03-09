:- module constraints.
:- interface.

:- import_module map.
:- import_module set.

:- type variable(T) ---> var(int).

:- type f_constraint
   ---> ':='(float)
   ;    '+'(variable(float), float)
   ;    '-'(variable(float), variable(float)).

:- type i_constraint
   ---> ':='(int)
   ;    '+'(variable(int), int)
   ;    '=<'(int).

:- type s_constraint
   ---> ':='(string).

:- type constraint
   ---> f(f_constraint)
   ;    i(i_constraint)
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
:- import_module int.
:- import_module list.
:- import_module maybe.
:- import_module options.
:- import_module pair.
:- import_module string.

:- pred f_new_value(int::in, float::in, constraints::in, constraints::out, set(string)::out) is det.
:- pred i_new_value(int::in, int::in, constraints::in, constraints::out, set(string)::out) is det.

init = map.init.

unify(V, f(':='(Val)), CMap, CMapOut, Descs) :-
  (search(CMap, V, C) ->
    C = f(':='(BoundVal)),
    Val = BoundVal,
    CMapOut = CMap,
    Descs = set.init
  ;
    % Add the binding.
    CMapOut1 = insert(CMap, V, f(':='(Val))),
    f_new_value(V, Val, CMapOut1, CMapOut, Descs1),
    (verbose ->
      Descs = insert(Descs1, format("(var %i) = %f", [i(V), f(Val)]))
    ; 
      Descs = set.init)).
unify(V, f(var(X) + Y), CMap, CMapOut, Descs) :-
  (search(CMap, X, f(':='(XVal))) ->
    Evaluated = yes(XVal + Y)
  ;
    Evaluated = no),

  (search(CMap, V, C) ->
    C = f(':='(BoundVal)),
    Evaluated = yes(Val),
    Val = BoundVal,
    CMapOut = CMap,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      CMapOut = insert(CMap, V, f(':='(Val))),
      % TODO: Call f_new_value.
      (verbose ->
        Descs = make_singleton_set(format("(var %i) = %f", [i(V), f(Val)]))
      ; 
        Descs = set.init)
    ;
      CMapOut = insert(CMap, V, f(var(X) + Y)),
      Descs = set.init)).
unify(V, f(var(X) - var(Y)), CMap, CMapOut, Descs) :-
  (search(CMap, X, f(':='(XVal))), search(CMap, Y, f(':='(YVal))) ->
    Evaluated = yes(XVal - YVal)
  ;
    Evaluated = no),

  (search(CMap, V, C) ->
    C = f(':='(BoundVal)),
    Evaluated = yes(Val),
    Val = BoundVal,
    CMapOut = CMap,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      CMapOut = insert(CMap, V, f(':='(Val))),
      % TODO: Call f_new_value.
      (verbose ->
        Descs = make_singleton_set(format("(var %i) = %f", [i(V), f(Val)]))
      ; 
        Descs = set.init)
    ;
      CMapOut = insert(CMap, V, f(var(X) - var(Y))),
      Descs = set.init)).
unify(V, i(':='(Val)), CMap, CMapOut, Descs) :-
  (search(CMap, V, i(':='(BoundVal))) ->
    Val = BoundVal,
    CMapOut = CMap,
    Descs = set.init
  ;
    % Add the binding.
    CMapOut1 = insert(CMap, V, i(':='(Val))),
    i_new_value(V, Val, CMapOut1, CMapOut, Descs1),
    (verbose ->
      Descs = insert(Descs1, format("(var %i) = %i", [i(V), i(Val)]))
    ; 
      Descs = set.init)).
unify(V, i(var(X) + Y), CMap, CMapOut, Descs) :-
  (search(CMap, X, i(':='(XVal))) ->
    Evaluated = yes(XVal + Y)
  ;
    Evaluated = no),

  (search(CMap, V, C) ->
    C = i(':='(BoundVal)),
    Evaluated = yes(Val),
    Val = BoundVal,
    CMapOut = CMap,
    Descs = set.init
  ;
    % Add the binding.
    (Evaluated = yes(Val) ->
      CMapOut = insert(CMap, V, i(':='(Val))),
      % TODO: Call i_new_value.
      (verbose ->
        Descs = make_singleton_set(format("(var %i) = %i", [i(V), i(Val)]))
      ; 
        Descs = set.init)
    ;
      CMapOut = insert(CMap, V, i(var(X) + Y)),
      Descs = set.init)).
unify(V, i('=<'(Val)), CMap, CMapOut, Descs) :-
%  (search(CMap, V, i(':='(BoundVal))) ->
%    BoundVal =< Val,
%    CMapOut = CMap,
%    Descs = set.init
%  ;
%    % TODO: Check for another constraint.
%    % Add the binding.
%    CMapOut = insert(CMap, V, i('=<'(Val))),
%    (verbose ->
%      Descs = make_singleton_set(format("(var %i) <= %i", [i(V), i(Val)]))
%    ; 
%      Descs = set.init)).
  CMapOut = CMap, Descs = make_singleton_set(format("(var %i) <= %i", [i(V), i(Val)])).
unify(V, s(':='(Val)), CMap, CMapOut, Descs) :-
  (search(CMap, V, s(':='(BoundVal))) ->
    Val = BoundVal,
    CMapOut = CMap,
    Descs = set.init
  ;
    % Add the binding.
    CMapOut = insert(CMap, V, s(':='(Val))),
    (verbose ->
      Descs = make_singleton_set(format("(var %i) = %s", [i(V), s(Val)]))
    ; 
      Descs = set.init)).

f_new_value(V, Val, CMap, CMapOut, Descs) :-
  CMapOut-Descs = foldl(
    (func(OtherV, C, CMapIn-DescsIn) = CMap1-Descs1 :-
      % Try to get the value of OtherV.
      (C = f(var(V) + Y1) ->
        OtherVal = yes(Val + Y1)
      ;(C = f(var(X) - var(V)), search(CMapIn, X, f(':='(XVal))) ->
        OtherVal = yes(XVal - Val)
      ;(C = f(var(V) - var(Y)), search(CMapIn, Y, f(':='(YVal))) ->
        OtherVal = yes(Val - YVal)
      ;
        % TODO: Check other expressions.
        OtherVal = no))),

      (OtherVal = yes(F) ->
        % Replace OtherV with evaluated value.
        (unify(OtherV, f(':='(F)), delete(CMapIn, OtherV), CMap2, Descs2) ->
          CMap1 = CMap2,
          Descs1 = union(DescsIn, Descs2)
        ;
          % This shouldn't happen.
          CMap1 = CMapIn,
          Descs1 = DescsIn)
      ;
        CMap1 = CMapIn,
        Descs1 = DescsIn)),
    CMap, CMap-set.init).

i_new_value(V, Val, CMap, CMapOut, Descs) :-
  CMapOut-Descs = foldl(
    (func(OtherV, C, CMapIn-DescsIn) = CMap1-Descs1 :-
      % Try to get the value of OtherV.
      (C = i(var(V) + Y1) ->
        OtherVal = yes(Val + Y1)
      ;
        % TODO: Check other expressions.
        OtherVal = no),

      (OtherVal = yes(I) ->
        % Replace OtherV with evaluated value.
        (unify(OtherV, i(':='(I)), delete(CMapIn, OtherV), CMap2, Descs2) ->
          CMap1 = CMap2,
          Descs1 = union(DescsIn, Descs2)
        ;
          % This shouldn't happen.
          CMap1 = CMapIn,
          Descs1 = DescsIn)
      ;
        CMap1 = CMapIn,
        Descs1 = DescsIn)),
    CMap, CMap-set.init).

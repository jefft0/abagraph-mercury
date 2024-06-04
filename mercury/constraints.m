% Naming convention for variables:
% CS for the top-level constraint_store which has all types of constraints (float, int, etc.)
% Cs for a particular type of constraints, e.g. s_constraints
% CSet for the set of constraints cs (not val(C)) of a particular type, e.g. set(s_constraint)
% C for an individual constriant, e.g. s_constraint

:- module constraints.
:- interface.

:- import_module map.
:- import_module maybe.
:- import_module set.

:- type var(T) ---> var(int).

:- type n_constraint(T)
   ---> ':='(T)
   ;    '\\='(T)
   ;    '\\=='(var(T))
   ;    '+'(var(T), T)
   ;    '++'(var(T), var(T))
   ;    '-'(T, var(T)) % NOTE: We don't have '-'(var(T), T) because it's the same as '+'(var(T), -T)
   ;    '--'(var(T), var(T))
   ;    '>='(T)
   ;    '=<'(T).

:- type f_constraint == n_constraint(float).
:- type i_constraint == n_constraint(int).

:- type s_constraint
   ---> ':='(string)
   ;    '\\='(string)
   ;    '\\=='(var(string)).

:- type constraint
   ---> f(n_constraint(float))
   ;    i(n_constraint(int))
   ;    s(s_constraint).

% A variable is either the bound value val(X) or constraints cs.
% (We don't put the ':=' constraint in cs.)
:- type n_constraints(T)
   ---> val(T)
   ;    cs(set(n_constraint(T))).
:- type s_constraints
   ---> val(string)
   ;    cs(set(s_constraint)).

:- type constraint_store ---> constraint_store(map(int, n_constraints(float)), map(int, n_constraints(int)), map(int, s_constraints)).

% Return a new constraint_store.
:- func init = constraint_store.

% unify(V, C, CS, CSOut, Descs).
% If there is no binding for V, add one for V and the constraint C and set Descs to
% a set of description strings for the bindings (only if verbose).
% If there is a binding for V, confirm the constraint and set Descs to "",
% else if the constraint is not confirmed then fail.
:- pred unify(int::in, constraint::in, constraint_store::in, constraint_store::out, set(string)::out) is semidet.
% f_get(V, Cs) = Val.
% Return yes(Val) where Val is the bound value of V, or no if not found.
:- func f_get(int, constraint_store) = maybe(float).
:- func i_get(int, constraint_store) = maybe(int).
:- func s_get(int, constraint_store) = maybe(string).
% Return a string representation of the constraint_store, indented (so that you can prefix a label). Example:
%   int
%   (= (var 2) 10)
%   string
%   (<> (var 1) (var 2))
%   (<> (var 2) (var 1))
:- func to_string(constraint_store) = string is det.

:- func f_constraint_to_string(int, n_constraint(float)) = string is det.
:- func i_constraint_to_string(int, n_constraint(int)) = string is det.
:- func s_constraint_to_string(int, s_constraint) = string is det.

:- implementation.

:- import_module bool.
:- import_module list.
:- import_module number.
:- import_module pair.
:- import_module string.

:- pred n_unify(int::in, n_constraint(T)::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, set(string)::out) is semidet <= number(T).
:- pred s_unify(int::in, s_constraint::in, map(int, s_constraints)::in, map(int, s_constraints)::out, set(string)::out) is semidet.
% n_set_value(V, Val, Cs, CsOut, Descs).
% If Cs already has a val for V then confirm it. Otherwise set val(Val). If Cs has constraints, call n_set_value to evaluate them.
:- pred n_set_value(int::in, T::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, set(string)::out) is semidet <= number(T).
% n_new_value(Val, C, Cs, CsOut, Descs).
% The variable with constraint C has a new value Val. Confirm a boolean constraint C with Val or
% maybe get a new value for another variable in the arithmetic expression C.
:- pred n_new_value(T::in, n_constraint(T)::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, set(string)::out) is semidet <= number(T).
% n_add_transformable_constraint(V, C, Cs, CsOut, AddTransformed).
% If the constraints for V already has C, then set AddTransformed no and do nothing.
% If the constraints for V already has a val, then set AddTransformed yes and do nothing.
% Otherwise, set AddTransformed yes and add C to the constraints for V.
% If AddTransformed is yes, then you should add the transformed constraint(s) to the other variable(s).
:- pred n_add_transformable_constraint(int::in, n_constraint(T)::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, bool::out) is det.
:- pred s_add_transformable_constraint(int::in, s_constraint::in, map(int, s_constraints)::in, map(int, s_constraints)::out, bool::out) is det.
:- func n_constraint_to_string(int, n_constraint(T)) = string is det <= number(T).
:- pred s_new_value(string::in, s_constraint::in, map(int, s_constraints)::in, map(int, s_constraints)::out, set(string)::out) is semidet.
:- func n_to_string(map(int, n_constraints(T))) = string is det <= number(T).
:- func s_to_string(map(int, s_constraints)) = string is det.
:- pred verbose is det.

init = constraint_store(map.init, map.init, map.init).

% Dispatch unify to n_unify, s_unify, etc.
unify(V, f(FC), constraint_store(FCs, ICs, SCs), constraint_store(FCsOut, ICs, SCs), Descs) :- n_unify(V, FC, FCs, FCsOut, Descs).
unify(V, i(IC), constraint_store(FCs, ICs, SCs), constraint_store(FCs, ICsOut, SCs), Descs) :- n_unify(V, IC, ICs, ICsOut, Descs).
unify(V, s(SC), constraint_store(FCs, ICs, SCs), constraint_store(FCs, ICs, SCsOut), Descs) :- s_unify(V, SC, SCs, SCsOut, Descs).

f_get(V, constraint_store(Cs, _, _)) = Val :-
  (search(Cs, V, val(Val1)) ->
    Val = yes(Val1)
  ;
    Val = no).
i_get(V, constraint_store(_, Cs, _)) = Val :-
  (search(Cs, V, val(Val1)) ->
    Val = yes(Val1)
  ;
    Val = no).
s_get(V, constraint_store(_, _, Cs)) = Val :-
  (search(Cs, V, val(Val1)) ->
    Val = yes(Val1)
  ;
    Val = no).

n_unify(V, ':='(Val), Cs, CsOut, Descs) :- n_set_value(V, Val, Cs, CsOut, Descs).
n_unify(V, '\\='(X), Cs, CsOut, Descs) :-
  C = '\\='(X),
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = val(BoundVal) ->
      % Just confirm the constraint with the existing value.
      BoundVal \= X,
      CsOut = Cs,
      Descs = set.init
    ;
      ValOrCSet = cs(CSet),
      (member(C, CSet) ->
        % We already added the constraint. Do nothing. This also prevents loops.
        CsOut = Cs,
        Descs = set.init
      ;
        CsOut = set(Cs, V, cs(insert(CSet, C))),
        (verbose ->
          Descs = make_singleton_set(n_constraint_to_string(V, C))
        ; 
          Descs = set.init)))
  ;  
    % Create the entry for V.
    CsOut = set(Cs, V, cs(make_singleton_set(C))),
    (verbose ->
      Descs = make_singleton_set(n_constraint_to_string(V, C))
    ; 
      Descs = set.init)).
n_unify(V, '\\=='(var(X)), Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    % We already know the value. Treat this like the simpler \= .
    n_unify(V, '\\='(XVal), Cs, CsOut, Descs)
  ;
    n_add_transformable_constraint(V, '\\=='(var(X)), Cs, CsOut1, AddTransformed),
    (AddTransformed = yes ->
      n_unify(X, '\\=='(var(V)), CsOut1, CsOut, Descs)
    ;
      CsOut = CsOut1,
      Descs = set.init)).
n_unify(V, var(X) + Y, Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    % We already know the value. Treat this like assignment.
    n_set_value(V, XVal + Y, Cs, CsOut, Descs)
  ;
    n_add_transformable_constraint(V, var(X) + Y, Cs, CsOut1, AddTransformed),
    (AddTransformed = yes ->
      n_unify(X, var(V) + (-Y), CsOut1, CsOut2, Descs1),

      % Add or tighten boolean constraints.
      (search(CsOut2, X, cs(XCSet)) ->
        foldl(
          (pred(XC::in, CsIn-DescsIn::in, CsOut3-Descs3::out) is semidet :-
            % TODO: Check for XC = '>='(XVal)
            (XC = '=<'(XVal) ->
              % We have var(V) - Y = var(X) and also var(X) =< XVal, so add
              % var(V) - Y =< XVal -> var(V) =< XVal + Y.
              n_unify(V, '=<'(XVal + Y), CsIn, CsOut3, Descs2),
              Descs3 = union(DescsIn, Descs2)
            ;
              CsOut3 = CsIn,
              Descs3 = DescsIn)),
          XCSet, CsOut2-Descs1, CsOut-Descs)
      ;
        CsOut = CsOut2,
        Descs = Descs1)
    ;
      CsOut = CsOut1,
      Descs = set.init)).
n_unify(V, var(X) ++ var(Y), Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    (search(Cs, Y, val(YVal)) ->
      % We already know both values. Treat this like assignment.
      n_set_value(V, XVal + YVal, Cs, CsOut, Descs)
    ;
      % We already know one of the values. Treat this like the simpler + .
      n_unify(V, '+'(var(Y), XVal), Cs, CsOut, Descs))
  ;
    (search(Cs, Y, val(YVal)) ->
      % We already know one of the values. Treat this like the simpler + .
      n_unify(V, '+'(var(X), YVal), Cs, CsOut, Descs)
    ;
      n_add_transformable_constraint(V, var(X) ++ var(Y), Cs, CsOut1, AddTransformed),
      (AddTransformed = yes ->
        n_unify(X, var(V) -- var(Y), CsOut1, CsOut2, Descs1),
        n_unify(Y, var(V) -- var(X), CsOut2, CsOut, Descs2),
        Descs = union(Descs1, Descs2)
      ;
        CsOut = CsOut1,
        Descs = set.init))).
n_unify(V, X - var(Y), Cs, CsOut, Descs) :-
  (search(Cs, Y, val(YVal)) ->
    % We already know the value. Treat this like assignment.
    n_set_value(V, X - YVal, Cs, CsOut, Descs)
  ;
    n_add_transformable_constraint(V, X - var(Y), Cs, CsOut1, AddTransformed),
    (AddTransformed = yes ->
      n_unify(Y, X - var(V), CsOut1, CsOut2, Descs1),

      % Add or tighten boolean constraints.
      (search(CsOut2, Y, cs(YCSet)) ->
        foldl(
          (pred(YC::in, CsIn-DescsIn::in, CsOut3-Descs3::out) is semidet :-
            % TODO: Check for YC = '>='(YVal)
            (YC = '=<'(YVal) ->
              % We have X - var(V) = var(Y) and also var(Y) =< YVal, so add
              % X - var(V) =< YVal -> -var(V) =< YVal - X -> var(V) >= X - YVal.
              n_unify(V, '>='(X - YVal), CsIn, CsOut3, Descs2),
              Descs3 = union(DescsIn, Descs2)
            ;
              CsOut3 = CsIn,
              Descs3 = DescsIn)),
          YCSet, CsOut2-Descs1, CsOut-Descs)
      ;
        CsOut = CsOut2,
        Descs = Descs1)
    ;
      CsOut = CsOut1,
      Descs = set.init)).
n_unify(V, var(X) -- var(Y), Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    (search(Cs, Y, val(YVal)) ->
      % We already know both values. Treat this like assignment.
      n_set_value(V, XVal - YVal, Cs, CsOut, Descs)
    ;
      % We already know one of the values. Treat this like the simpler - .
      n_unify(V, '-'(XVal, var(Y)), Cs, CsOut, Descs))
  ;
    (search(Cs, Y, val(YVal)) ->
      % We already know one of the values. Treat this like the simpler + .
      n_unify(V, '+'(var(X), -YVal), Cs, CsOut, Descs)
    ;
      n_add_transformable_constraint(V, var(X) -- var(Y), Cs, CsOut1, AddTransformed),
      (AddTransformed = yes ->
        n_unify(X, var(V) ++ var(Y), CsOut1, CsOut2, Descs1),
        n_unify(Y, var(X) -- var(V), CsOut2, CsOut, Descs2),
        Descs = union(Descs1, Descs2)
      ;
        CsOut = CsOut1,
        Descs = set.init))).
n_unify(V, '>='(X), Cs, CsOut, Descs) :-
  C = '>='(X),
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = val(BoundVal) ->
      % Just confirm the constraint with the existing value.
      BoundVal >= X,
      CsOut = Cs,
      Descs = set.init
    ;
      ValOrCSet = cs(CSet),
      (member(C, CSet) ->
        % We already added the constraint. Do nothing. This also prevents loops.
        CsOut = Cs,
        Descs = set.init
      ;
        % Search for other boolean constraints and confirm or tighten.
        foldl(
          (pred(OtherC::in, CSetIn-AddCIn-CSetChangedIn::in, CSetOut1-AddCOut1-CSetChangedOut1::out) is semidet :-
            (AddCIn = no ->
              % We have discarded C in favor of another. Do nothing.
              CSetOut1 = CSetIn,
              AddCOut1 = AddCIn,
              CSetChangedOut1 = CSetChangedIn
            ;
              (OtherC = '>='(OtherX) ->
                (OtherX >= X ->
                  % V >= OtherX is already tighter than V >= X, so discard C.
                  CSetOut1 = CSetIn,
                  AddCOut1 = no,
                  CSetChangedOut1 = CSetChangedIn
                ;
                  % Discard OtherC in favor of the tighter new C.
                  CSetOut1 = delete(CSetIn, OtherC),
                  AddCOut1 = AddCIn,
                  CSetChangedOut1 = yes))
              ;
                % Ignore OtherC.
                CSetOut1 = CSetIn,
                AddCOut1 = AddCIn,
                CSetChangedOut1 = CSetChangedIn)),
          CSet, pair.(CSet-yes)-no, pair.(CSet1-AddC)-CSetChanged),

        (AddC = yes ->
          % TODO: Search for math constraints and add a related boolean constraint.
          CsOut = set(Cs, V, cs(insert(CSet1, C))),
          (verbose ->
            Descs = make_singleton_set(n_constraint_to_string(V, C))
          ; 
            Descs = set.init)
        ;
          (CSetChanged = yes ->
            % Update with the new CSet modified by the search.
            CsOut = set(Cs, V, cs(CSet1))
          ;
            CsOut = Cs),
          Descs = set.init)))
  ;  
    % Create the entry for V.
    CsOut = set(Cs, V, cs(make_singleton_set(C))),
    (verbose ->
      Descs = make_singleton_set(n_constraint_to_string(V, C))
    ; 
      Descs = set.init)).
n_unify(V, '=<'(X), Cs, CsOut, Descs) :-
  C = '=<'(X),
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = val(BoundVal) ->
      % Just confirm the constraint with the existing value.
      BoundVal =< X,
      CsOut = Cs,
      Descs = set.init
    ;
      ValOrCSet = cs(CSet),
      (member(C, CSet) ->
        % We already added the constraint. Do nothing. This also prevents loops.
        CsOut = Cs,
        Descs = set.init
      ;
        % Search for other boolean constraints and confirm or tighten.
        foldl(
          (pred(OtherC::in, CSetIn-AddCIn-CSetChangedIn::in, CSetOut1-AddCOut1-CSetChangedOut1::out) is semidet :-
            (AddCIn = no ->
              % We have discarded C in favor of another. Do nothing.
              CSetOut1 = CSetIn,
              AddCOut1 = AddCIn,
              CSetChangedOut1 = CSetChangedIn
            ;
              (OtherC = '=<'(OtherX) ->
                (OtherX =< X ->
                  % V =< OtherX is already tighter than V =< X, so discard C.
                  CSetOut1 = CSetIn,
                  AddCOut1 = no,
                  CSetChangedOut1 = CSetChangedIn
                ;
                  % Discard OtherC in favor of the tighter new C.
                  CSetOut1 = delete(CSetIn, OtherC),
                  AddCOut1 = AddCIn,
                  CSetChangedOut1 = yes))
              ;
                % Ignore OtherC.
                CSetOut1 = CSetIn,
                AddCOut1 = AddCIn,
                CSetChangedOut1 = CSetChangedIn)),
          CSet, pair.(CSet-yes)-no, pair.(CSet1-AddC)-CSetChanged),

        (AddC = yes ->
          % TODO: Search for math constraints and add a related boolean constraint.
          CsOut = set(Cs, V, cs(insert(CSet1, C))),
          (verbose ->
            Descs = make_singleton_set(n_constraint_to_string(V, C))
          ; 
            Descs = set.init)
        ;
          (CSetChanged = yes ->
            % Update with the new CSet modified by the search.
            CsOut = set(Cs, V, cs(CSet1))
          ;
            CsOut = Cs),
          Descs = set.init)))
  ;  
    % Create the entry for V.
    CsOut = set(Cs, V, cs(make_singleton_set(C))),
    (verbose ->
      Descs = make_singleton_set(n_constraint_to_string(V, C))
    ; 
      Descs = set.init)).

s_unify(V, ':='(Val), Cs, CsOut, Descs) :-
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = val(BoundVal) ->
      % Just confirm the existing value.
      Val = BoundVal,
      CsOut = Cs,
      Descs = set.init
    ;
      % Save the constraints.
      ValOrCSet = cs(CSet),
      % Set the binding as the only constraint.
      Cs1 = set(Cs, V, val(Val)),

      (verbose ->
        Descs1 = make_singleton_set(s_constraint_to_string(V, ':='(Val)))
      ; 
        Descs1 = set.init),
      % Possibly evaluate all the constraints.
      foldl(
        (pred(C::in, CsIn-DescsIn::in, CsOut1-DescsOut1::out) is semidet :-
          s_new_value(Val, C, CsIn, CsOut1, Descs2),
          DescsOut1 = union(DescsIn, Descs2)),
        CSet, Cs1-Descs1, CsOut-Descs))
  ;  
    % Create the entry for V.
    CsOut = set(Cs, V, val(Val)),
    (verbose ->
      Descs = make_singleton_set(s_constraint_to_string(V, ':='(Val)))
    ; 
      Descs = set.init)).
s_unify(V, '\\='(X), Cs, CsOut, Descs) :-
  C = '\\='(X),
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = val(BoundVal) ->
      % Just confirm the constraint with the existing value.
      BoundVal \= X,
      CsOut = Cs,
      Descs = set.init
    ;
      ValOrCSet = cs(CSet),
      (member(C, CSet) ->
        % We already added the constraint. Do nothing. This also prevents loops.
        CsOut = Cs,
        Descs = set.init
      ;
        CsOut = set(Cs, V, cs(insert(CSet, C))),
        (verbose ->
          Descs = make_singleton_set(s_constraint_to_string(V, C))
        ; 
          Descs = set.init)))
  ;  
    % Create the entry for V.
    CsOut = set(Cs, V, cs(make_singleton_set(C))),
    (verbose ->
      Descs = make_singleton_set(s_constraint_to_string(V, C))
    ; 
      Descs = set.init)).
s_unify(V, '\\=='(var(X)), Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    % We already know the value. Treat this like the simpler \= .
    s_unify(V, '\\='(XVal), Cs, CsOut, Descs)
  ;
    s_add_transformable_constraint(V, '\\=='(var(X)), Cs, CsOut1, AddTransformed),
    (AddTransformed = yes ->
      s_unify(X, '\\=='(var(V)), CsOut1, CsOut, Descs)
    ;
      CsOut = CsOut1,
      Descs = set.init)).

n_set_value(V, Val, Cs, CsOut, Descs) :-
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = val(BoundVal) ->
      % Just confirm the existing value.
      Val == BoundVal,
      CsOut = Cs,
      Descs = set.init
    ;
      % Save the constraints.
      ValOrCSet = cs(CSet),
      % Set the binding as the only constraint.
      Cs1 = set(Cs, V, val(Val)),

      (verbose ->
        Descs1 = make_singleton_set(n_constraint_to_string(V, ':='(Val)))
      ; 
        Descs1 = set.init),
      % Possibly evaluate all the constraints.
      foldl(
        (pred(C::in, CsIn-DescsIn::in, CsOut1-DescsOut1::out) is semidet :-
          n_new_value(Val, C, CsIn, CsOut1, Descs2),
          DescsOut1 = union(DescsIn, Descs2)),
        CSet, Cs1-Descs1, CsOut-Descs))
  ;  
    % Create the entry for V.
    CsOut = set(Cs, V, val(Val)),
    (verbose ->
      Descs = make_singleton_set(n_constraint_to_string(V, ':='(Val)))
    ; 
      Descs = set.init)).

n_new_value(Val, var(X) + Y, CsIn, CsOut, Descs) :-
  % We have Val = X + Y. Set X to Val - Y.
  n_set_value(X, Val - Y, CsIn, CsOut, Descs).
n_new_value(Val, var(X) ++ var(Y), CsIn, CsOut, Descs) :-
  (search(CsIn, X, val(XVal)) ->
    % We have Val = X + Y and XVal. Set Y to Val - XVal.
    n_set_value(Y, Val - XVal, CsIn, CsOut, Descs)
  ;(search(CsIn, Y, val(YVal)) ->
    % We have Val = X + Y and YVal. Set X to Val - YVal.
    n_set_value(X, Val - YVal, CsIn, CsOut, Descs)
  ;
    CsOut = CsIn, Descs = set.init)).
n_new_value(Val, X - var(Y), CsIn, CsOut, Descs) :-
  % We have Val = X - Y. Set Y to X - Val.
  n_set_value(Y, X - Val, CsIn, CsOut, Descs).
n_new_value(Val, var(X) -- var(Y), CsIn, CsOut, Descs) :-
  (search(CsIn, X, val(XVal)) ->
    % We have Val = X - Y and XVal. Set Y to XVal - Val.
    n_set_value(Y, XVal - Val, CsIn, CsOut, Descs)
  ;(search(CsIn, Y, val(YVal)) ->
    % We have Val = X - Y and YVal. Set X to Val + YVal.
    n_set_value(X, Val + YVal, CsIn, CsOut, Descs)
  ;
    CsOut = CsIn, Descs = set.init)).
% Boolean constraints.
n_new_value(Val, '\\='(X), CsIn, CsIn, set.init) :- Val \= X.
n_new_value(Val, '\\=='(var(X)), CsIn, CsIn, set.init) :-
  (search(CsIn, X, val(XVal)) ->
    Val \= XVal
  ;
    true).
n_new_value(Val, '>='(X), CsIn, CsIn, set.init) :- Val >= X.
n_new_value(Val, '=<'(X), CsIn, CsIn, set.init) :- Val =< X.
% Ignore. (Shouldn't happen.)
n_new_value(_Val, ':='(_), CsIn, CsIn, set.init).

n_add_transformable_constraint(V, C, Cs, CsOut, AddTransformed) :-
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = cs(CSet) ->
      (member(C, CSet) ->
        % We already added the constraint. Do nothing. This also prevents loops.
        CsOut = Cs,
        AddTransformed = no
      ;
        CsOut = set(Cs, V, cs(insert(CSet, C))),
        AddTransformed = yes)
    ;
      % This is already val(X).
      CsOut = Cs,
      AddTransformed = yes)
  ;
    % New variable.
    CsOut = set(Cs, V, cs(make_singleton_set(C))),
    AddTransformed = yes).
s_add_transformable_constraint(V, C, Cs, CsOut, AddTransformed) :-
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = cs(CSet) ->
      (member(C, CSet) ->
        % We already added the constraint. Do nothing. This also prevents loops.
        CsOut = Cs,
        AddTransformed = no
      ;
        CsOut = set(Cs, V, cs(insert(CSet, C))),
        AddTransformed = yes)
    ;
      % This is already val(X).
      CsOut = Cs,
      AddTransformed = yes)
  ;
    % New variable.
    CsOut = set(Cs, V, cs(make_singleton_set(C))),
    AddTransformed = yes).

% Boolean constraints.
s_new_value(Val, '\\='(X), CsIn, CsIn, set.init) :- Val \= X.
s_new_value(Val, '\\=='(var(X)), CsIn, CsIn, set.init) :-
  (search(CsIn, X, val(XVal)) ->
    Val \= XVal
  ;
    true).
% Ignore. (Shouldn't happen.)
s_new_value(_Val, ':='(_), CsIn, CsIn, set.init).

n_constraint_to_string(V, ':='(Val)) =          format("(= (var %i) %s)", [i(V), s(to_string(Val))]).
n_constraint_to_string(V, '\\='(X)) =           format("(<> (var %i) %s)", [i(V), s(to_string(X))]).
n_constraint_to_string(V, '\\=='(var(X))) =     format("(<> (var %i) (var %i))", [i(V), i(X)]).
n_constraint_to_string(V, var(X1) + X2) =       format("(= (var %i) (+ (var %i) %s)", [i(V), i(X1), s(to_string(X2))]).
n_constraint_to_string(V, var(X1) ++ var(X2)) = format("(= (var %i) (+ (var %i) (var %i))", [i(V), i(X1), i(X2)]).
n_constraint_to_string(V, X1 - var(X2)) =       format("(= (var %i) (- %s (var %i))", [i(V), s(to_string(X1)), i(X2)]).
n_constraint_to_string(V, var(X1) -- var(X2)) = format("(= (var %i) (- (var %i) (var %i))", [i(V), i(X1), i(X2)]).
n_constraint_to_string(V, '>='(X)) =            format("(>= (var %i) %s)", [i(V), s(to_string(X))]).
n_constraint_to_string(V, '=<'(X)) =            format("(<= (var %i) %s)", [i(V), s(to_string(X))]).

f_constraint_to_string(V, C) = n_constraint_to_string(V, C).
i_constraint_to_string(V, C) = n_constraint_to_string(V, C).
s_constraint_to_string(V, ':='(Val)) =          format("(= (var %i) %s)", [i(V), s(Val)]).
s_constraint_to_string(V, '\\='(X)) =           format("(<> (var %i) %s)", [i(V), s(X)]).
s_constraint_to_string(V, '\\=='(var(X))) =     format("(<> (var %i) (var %i))", [i(V), i(X)]).

to_string(constraint_store(FCs, ICs, SCs)) = F ++ I ++ S :-
  (count(FCs) = 0 -> F = "" ; F = "  float\n" ++ n_to_string(FCs)),
  (count(ICs) = 0 -> I = "" ; I = "  int\n" ++ n_to_string(ICs)),
  (count(SCs) = 0 -> S = "" ; S = "  string\n" ++ s_to_string(SCs)).
n_to_string(Cs) =
  foldl(func(V, ValOrCSet, ResultIn) = ResultOut :-
      (ValOrCSet = val(Val) ->
        ResultOut = ResultIn ++ format("  %s\n", [s(n_constraint_to_string(V, ':='(Val)))])
      ;
        (ValOrCSet = cs(CSet) ->
          ResultOut = foldl(func(C, RIn) = RIn ++ format("  %s\n", [s(n_constraint_to_string(V, C))]),
                            CSet, ResultIn)
        ;
          ResultOut = ResultIn)),
    Cs, "").
s_to_string(Cs) =
  foldl(func(V, ValOrCSet, ResultIn) = ResultOut :-
      (ValOrCSet = val(Val) ->
        ResultOut = ResultIn ++ format("  %s\n", [s(s_constraint_to_string(V, ':='(Val)))])
      ;
        (ValOrCSet = cs(CSet) ->
          ResultOut = foldl(func(C, RIn) = RIn ++ format("  %s\n", [s(s_constraint_to_string(V, C))]),
                            CSet, ResultIn)
        ;
          ResultOut = ResultIn)),
    Cs, "").

verbose.

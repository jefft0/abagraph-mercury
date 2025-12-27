% Naming convention for variables:
% CS for the top-level constraint_store which has all types of constraints (float, int, etc.)
% Cs for a particular type of constraints, e.g. s_constraints
% CSet for the set of constraints cs (not val(C)) of a particular type, e.g. set(s_constraint)
% C for an individual constriant, e.g. s_constraint

:- module constraints.
:- interface.

:- import_module list.
:- import_module map.
:- import_module maybe.
:- import_module set.

:- type var(T) ---> var(int).

:- type n_constraint(T)
   ---> ':='(T)
   ;    '+'(var(T), T)
   ;    '++'(var(T), var(T))
   ;    '-'(T, var(T)) % NOTE: We don't have '-'(var(T), T) because it's the same as '+'(var(T), -T)
   ;    '--'(var(T), var(T))
   ;    '>='(T)
   ;    '=<'(T).

:- type f_constraint == n_constraint(float).
:- type i_constraint == n_constraint(int).

:- type s_constraint
   ---> ':='(string).

:- type nb_constraint(T)
   ---> '='(int, T)
   ;    '=='(int, int).

:- type sb_constraint
   ---> '='(int, string)
   ;    '=='(int, int).

:- type b_constraint
   ---> t
   ;    f
   ;    and(b_constraint, b_constraint)
   ;    or(b_constraint, b_constraint)
   ;    not(b_constraint)
   ;    f(nb_constraint(float))
   ;    i(nb_constraint(int))
   ;    s(sb_constraint).

:- type constraint
   ---> f(n_constraint(float))
   ;    i(n_constraint(int))
   ;    s(s_constraint).

% Syntactic sugar for unifying sentences.
% E.g. unify(1, f('>='(2.0)), ...) can be written as var_f_unify(X >= 2.0, ...) where X = var(1).
:- type var_n_constraint(T)
   ---> var(T) := T
   ;    var(T) \= T
   ;    var(T) \== var(T)
   ;    var(T) >= T
   ;    var(T) =< T
   ;    var(T) = n_constraint(T).

:- type var_f_constraint == var_n_constraint(float).
:- type var_i_constraint == var_n_constraint(int).

:- type var_s_constraint
   ---> var(string) := string
   ;    var(string) \= string
   ;    var(string) \== var(string).

% A variable is either the bound value val(X) or constraints cs.
% (We don't put the ':=' constraint in cs.)
:- type n_constraints(T)
   ---> val(T)
   ;    cs(set(n_constraint(T))).
:- type s_constraints
   ---> val(string)
   ;    cs(set(s_constraint)).

:- type constraint_store ---> constraint_store(map(int, n_constraints(float)),
                                               map(int, n_constraints(int)),
                                               map(int, s_constraints),
                                               set(b_constraint)).

% Return a new constraint_store.
:- func init = constraint_store.

% unify(V, C, CS, CSOut, Descs).
% If there is no binding for V, add one for V and the constraint C and set Descs to
% a list of description strings for the bindings (only if verbose).
% If there is a binding for V, confirm the constraint and set Descs to [],
% else if the constraint is not confirmed then fail.
:- pred unify(int::in, constraint::in, constraint_store::in, constraint_store::out, list(string)::out) is semidet.
% b_unify(C, CS, CSOut, Descs).
% Add the boolean constraint expression C, reducing it if possible with variable bindings from CS.
% If some of the constraints are passed to unify, return its Descs.
:- pred b_unify(b_constraint::in, constraint_store::in, constraint_store::out, list(string)::out) is semidet.
:- pred new_var(var(T)::out) is det.
% f_get(V, Cs) = Val.
% Return yes(Val) where Val is the bound value of V, or no if not found.
:- func f_get(int, constraint_store) = maybe(float).
:- func i_get(int, constraint_store) = maybe(int).
:- func s_get(int, constraint_store) = maybe(string).
% Syntactic sugar.
:- pred var_f_unify(var_f_constraint::in, constraint_store::in, constraint_store::out, list(string)::out) is semidet.
:- pred var_i_unify(var_i_constraint::in, constraint_store::in, constraint_store::out, list(string)::out) is semidet.
:- pred var_s_unify(var_s_constraint::in, constraint_store::in, constraint_store::out, list(string)::out) is semidet.
% Return a string representation of the constraint_store, indented (so that you can prefix a label). Example:
%   int
%   (= (var 2) 10)
:- func to_string(constraint_store) = string is det.
:- func b_constraint_to_string(b_constraint) = string is det.

:- func f_constraint_to_string(int, n_constraint(float)) = string is det.
:- func i_constraint_to_string(int, n_constraint(int)) = string is det.
:- func s_constraint_to_string(int, s_constraint) = string is det.

:- func var_f_constraint_to_string(var_f_constraint) = string is det.
:- func var_i_constraint_to_string(var_i_constraint) = string is det.
:- func var_s_constraint_to_string(var_s_constraint) = string is det.

% A helper function to return a binary constraint expression for the conditions
% when two var(string) lists match. Fail if cannot match.
:- func var_string_list_matches(list(var(string)), list(var(string))) = b_constraint is semidet.

:- implementation.

:- import_module bool.
:- import_module number.
:- import_module pair.
:- import_module string.

:- pred n_unify(int::in, n_constraint(T)::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, list(string)::out) is semidet <= number(T).
:- pred s_unify(int::in, s_constraint::in, map(int, s_constraints)::in, map(int, s_constraints)::out, list(string)::out) is semidet.
% b_reduce(C, CS).
% Reduce the boolean constraint expression C, using variable bindings from CS if possible.
:- func b_reduce(b_constraint, constraint_store) = b_constraint is det.
:- func nb_reduce(nb_constraint(T), map(int, n_constraints(T))) = b_constraint is det <= number(T).
% n_set_value(V, Val, Cs, CsOut, Descs).
% If Cs already has a val for V then confirm it. Otherwise set val(Val). If Cs has constraints, call n_set_value to evaluate them.
:- pred n_set_value(int::in, T::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, list(string)::out) is semidet <= number(T).
% n_new_value(Val, C, Cs, CsOut, Descs).
% The variable with constraint C has a new value Val. Confirm a boolean constraint C with Val or
% maybe get a new value for another variable in the arithmetic expression C.
:- pred n_new_value(T::in, n_constraint(T)::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, list(string)::out) is semidet <= number(T).
% n_add_transformable_constraint(V, C, Cs, CsOut, AddTransformed).
% If the constraints for V already has C, then set AddTransformed no and do nothing.
% If the constraints for V already has a val, then set AddTransformed yes and do nothing.
% Otherwise, set AddTransformed yes and add C to the constraints for V.
% If AddTransformed is yes, then you should add the transformed constraint(s) to the other variable(s).
:- pred n_add_transformable_constraint(int::in, n_constraint(T)::in, map(int, n_constraints(T))::in, map(int, n_constraints(T))::out, bool::out) is det.
:- pred s_add_transformable_constraint(int::in, s_constraint::in, map(int, s_constraints)::in, map(int, s_constraints)::out, bool::out) is det.
:- func n_constraint_to_string(int, n_constraint(T)) = string is det <= number(T).
:- func var_n_constraint_to_string(var_n_constraint(T)) = string is det <= number(T).
:- pred s_new_value(string::in, s_constraint::in, map(int, s_constraints)::in, map(int, s_constraints)::out, list(string)::out) is semidet.
:- func n_to_string(map(int, n_constraints(T))) = string is det <= number(T).
:- func s_to_string(map(int, s_constraints)) = string is det.
:- pred next_var_int(int::out) is det.
:- pred verbose is det.

init = constraint_store(map.init, map.init, map.init, set.init).

% Dispatch unify to n_unify, s_unify, etc.
unify(V, f(FC), constraint_store(FCs, ICs, SCs, BCs), CSOut, Descs) :-
  n_unify(V, FC, FCs, FCsOut, Descs1),
  % Use the new values to possibly reduce each boolean expression.
  foldl(
    (pred(C::in, CSIn-DescsIn::in, CSOut1-remove_dups(append(DescsIn, DescsOut1))::out) is semidet :- b_unify(C, CSIn, CSOut1, DescsOut1)),
    BCs, constraint_store(FCsOut, ICs, SCs, set.init)-Descs1, CSOut-Descs).
unify(V, i(IC), constraint_store(FCs, ICs, SCs, BCs), CSOut, Descs) :-
  n_unify(V, IC, ICs, ICsOut, Descs1),
  % Use the new values to possibly reduce each boolean expression.
  foldl(
    (pred(C::in, CSIn-DescsIn::in, CSOut1-remove_dups(append(DescsIn, DescsOut1))::out) is semidet :- b_unify(C, CSIn, CSOut1, DescsOut1)),
    BCs, constraint_store(FCs, ICsOut, SCs, set.init)-Descs1, CSOut-Descs).
unify(V, s(SC), constraint_store(FCs, ICs, SCs, BCs), CSOut, Descs) :-
  s_unify(V, SC, SCs, SCsOut, Descs1),
  % Use the new values to possibly reduce each boolean expression.
  foldl(
    (pred(C::in, CSIn-DescsIn::in, CSOut1-remove_dups(append(DescsIn, DescsOut1))::out) is semidet :- b_unify(C, CSIn, CSOut1, DescsOut1)),
    BCs, constraint_store(FCs, ICs, SCsOut, set.init)-Descs1, CSOut-Descs).

n_unify(V, ':='(Val), Cs, CsOut, Descs) :- n_set_value(V, Val, Cs, CsOut, Descs).
n_unify(V, var(X) + Y, Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    % We already know the value. Treat this like assignment.
    n_unify(V, ':='(XVal + Y), Cs, CsOut, Descs)
  ;
    n_add_transformable_constraint(V, var(X) + Y, Cs, CsOut1, AddTransformed),
    (AddTransformed = yes ->
      n_unify(X, var(V) + (-Y), CsOut1, CsOut2, Descs1),

      % Add or tighten boolean constraints.
      (search(CsOut2, X, cs(XCSet)) ->
        foldl(
          (pred(XC::in, CsIn-DescsIn::in, CsOut3-Descs3::out) is semidet :-
            (XC = '>='(XVal) ->
              % We have var(V) - Y = var(X) and also var(X) >= XVal, so add
              % var(V) - Y >= XVal -> var(V) >= XVal + Y.
              n_unify(V, '>='(XVal + Y), CsIn, CsOut3, Descs2),
              Descs3 = remove_dups(append(DescsIn, Descs2))
            ;(XC = '=<'(XVal) ->
              % We have var(V) - Y = var(X) and also var(X) =< XVal, so add
              % var(V) - Y =< XVal -> var(V) =< XVal + Y.
              n_unify(V, '=<'(XVal + Y), CsIn, CsOut3, Descs2),
              Descs3 = remove_dups(append(DescsIn, Descs2))
            ;
              CsOut3 = CsIn,
              Descs3 = DescsIn))),
          XCSet, CsOut2-Descs1, CsOut-Descs)
      ;
        CsOut = CsOut2,
        Descs = Descs1)
    ;
      CsOut = CsOut1,
      Descs = [])).
n_unify(V, var(X) ++ var(Y), Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    (search(Cs, Y, val(YVal)) ->
      % We already know both values. Treat this like assignment.
      n_unify(V, ':='(XVal + YVal), Cs, CsOut, Descs)
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
        Descs = remove_dups(append(Descs1, Descs2))
      ;
        CsOut = CsOut1,
        Descs = []))).
n_unify(V, X - var(Y), Cs, CsOut, Descs) :-
  (search(Cs, Y, val(YVal)) ->
    % We already know the value. Treat this like assignment.
    n_unify(V, ':='(X - YVal), Cs, CsOut, Descs)
  ;
    n_add_transformable_constraint(V, X - var(Y), Cs, CsOut1, AddTransformed),
    (AddTransformed = yes ->
      n_unify(Y, X - var(V), CsOut1, CsOut2, Descs1),

      % Add or tighten boolean constraints.
      (search(CsOut2, Y, cs(YCSet)) ->
        foldl(
          (pred(YC::in, CsIn-DescsIn::in, CsOut3-Descs3::out) is semidet :-
            (YC = '>='(YVal) ->
              % We have X - var(V) = var(Y) and also var(Y) >= YVal, so add
              % X - var(V) >= YVal -> -var(V) >= YVal - X -> var(V) =< X - YVal.
              n_unify(V, '=<'(X - YVal), CsIn, CsOut3, Descs2),
              Descs3 = remove_dups(append(DescsIn, Descs2))
            ;(YC = '=<'(YVal) ->
              % We have X - var(V) = var(Y) and also var(Y) =< YVal, so add
              % X - var(V) =< YVal -> -var(V) =< YVal - X -> var(V) >= X - YVal.
              n_unify(V, '>='(X - YVal), CsIn, CsOut3, Descs2),
              Descs3 = remove_dups(append(DescsIn, Descs2))
            ;
              CsOut3 = CsIn,
              Descs3 = DescsIn))),
          YCSet, CsOut2-Descs1, CsOut-Descs)
      ;
        CsOut = CsOut2,
        Descs = Descs1)
    ;
      CsOut = CsOut1,
      Descs = [])).
n_unify(V, var(X) -- var(Y), Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    (search(Cs, Y, val(YVal)) ->
      % We already know both values. Treat this like assignment.
      n_unify(V, ':='(XVal - YVal), Cs, CsOut, Descs)
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
        Descs = remove_dups(append(Descs1, Descs2))
      ;
        CsOut = CsOut1,
        Descs = []))).
n_unify(V, '>='(X), Cs, CsOut, Descs) :-
  C = '>='(X),
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = val(BoundVal) ->
      % Just confirm the constraint with the existing value.
      BoundVal >= X,
      CsOut = Cs,
      Descs = []
    ;
      ValOrCSet = cs(CSet),
      (member(C, CSet) ->
        % We already added the constraint. Do nothing. This also prevents loops.
        CsOut = Cs,
        Descs = []
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
            Descs = [n_constraint_to_string(V, C)]
          ; 
            Descs = [])
        ;
          (CSetChanged = yes ->
            % Update with the new CSet modified by the search.
            CsOut = set(Cs, V, cs(CSet1))
          ;
            CsOut = Cs),
          Descs = [])))
  ;  
    % Create the entry for V.
    CsOut = set(Cs, V, cs(make_singleton_set(C))),
    (verbose ->
      Descs = [n_constraint_to_string(V, C)]
    ; 
      Descs = [])).
n_unify(V, '=<'(X), Cs, CsOut, Descs) :-
  C = '=<'(X),
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = val(BoundVal) ->
      % Just confirm the constraint with the existing value.
      BoundVal =< X,
      CsOut = Cs,
      Descs = []
    ;
      ValOrCSet = cs(CSet),
      (member(C, CSet) ->
        % We already added the constraint. Do nothing. This also prevents loops.
        CsOut = Cs,
        Descs = []
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
            Descs = [n_constraint_to_string(V, C)]
          ; 
            Descs = [])
        ;
          (CSetChanged = yes ->
            % Update with the new CSet modified by the search.
            CsOut = set(Cs, V, cs(CSet1))
          ;
            CsOut = Cs),
          Descs = [])))
  ;  
    % Create the entry for V.
    CsOut = set(Cs, V, cs(make_singleton_set(C))),
    (verbose ->
      Descs = [n_constraint_to_string(V, C)]
    ; 
      Descs = [])).

s_unify(V, ':='(Val), Cs, CsOut, Descs) :-
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = val(BoundVal) ->
      % Just confirm the existing value.
      Val = BoundVal,
      CsOut = Cs,
      Descs = []
    ;
      % Save the constraints.
      ValOrCSet = cs(CSet),
      % Set the binding as the only constraint.
      Cs1 = set(Cs, V, val(Val)),

      (verbose ->
        Descs1 = [s_constraint_to_string(V, ':='(Val))]
      ; 
        Descs1 = []),
      % Possibly evaluate all the constraints.
      foldl(
        (pred(C::in, CsIn-DescsIn::in, CsOut1-DescsOut1::out) is semidet :-
          s_new_value(Val, C, CsIn, CsOut1, Descs2),
          DescsOut1 = remove_dups(append(DescsIn, Descs2))),
        CSet, Cs1-Descs1, CsOut-Descs))
  ;  
    % Create the entry for V.
    CsOut = set(Cs, V, val(Val)),
    (verbose ->
      Descs = [s_constraint_to_string(V, ':='(Val))]
    ; 
      Descs = [])).

b_unify(C, CS, CSOut, Descs) :-
  constraint_store(FCs, ICs, SCs, BCs) = CS,
  C1 = b_reduce(C, CS),
  (C1 = f ->
    fail
  ;
    (C1 = t -> 
      CSOut = CS,
      Descs = []
    ;
      (C1 = f(V = X) ->
        unify(V, f(':='(X)), CS, CSOut, Descs)
      ;
        (C1 = i(V = X) ->
          unify(V, i(':='(X)), CS, CSOut, Descs)
        ;
          (C1 = s(V = X) ->
            unify(V, s(':='(X)), CS, CSOut, Descs)
          ;
            (C1 = not(NotC1) ->
              % Can't add not(C). Already have C.
              \+ member(NotC1, BCs)
            ;
              % Can't add C. Already have not(C).
              \+ member(not(C1), BCs)),
            (C1 = and(X, Y) ->
              % Add X and Y separately.
              b_unify(X, CS, CS1, Descs1),
              b_unify(Y, CS1, CSOut, Descs2),
              Descs = remove_dups(append(Descs1, Descs2))
            ;
              CSOut = constraint_store(FCs, ICs, SCs, insert(BCs, C1)),
              Descs = [])))))).

b_reduce(t, _) = t.
b_reduce(f, _) = f.
b_reduce(and(X, Y), CS) = Out :-
  X1 = b_reduce(X, CS),
  Y1 = b_reduce(Y, CS),
  (X1 = t -> Out = Y1
  ; (X1 = f -> Out = f
  ; (Y1 = t -> Out = X1
  ; (Y1 = f -> Out = f
  ; Out = and(X1, Y1))))).
b_reduce(or(X, Y), CS) = Out :-
  X1 = b_reduce(X, CS),
  Y1 = b_reduce(Y, CS),
  (X1 = t -> Out = t
  ; (X1 = f -> Out = Y1
  ; (Y1 = t -> Out = t
  ; (Y1 = f -> Out = X1
  ; Out = or(X1, Y1))))).
b_reduce(not(X), CS) = Out :-
  X1 = b_reduce(X, CS),
  (X1 = t -> Out = f
  ; (X1 = f -> Out = t
  ; Out = not(X1))).
b_reduce(f(C), constraint_store(FCs, _, _, _)) = nb_reduce(C, FCs).
b_reduce(i(C), constraint_store(_, ICs, _, _)) = nb_reduce(C, ICs).
b_reduce(s(C), CS) = Out :-
  C = (X = YVal),
  CS = constraint_store(_, _, SCs, _),
  (search(SCs, X, val(XVal)) ->
    (XVal = YVal -> Out = t ; Out = f)
  ;
    Out = s(C))
;
  C = (X == Y),
  CS = constraint_store(_, _, SCs, _),
  (search(SCs, X, val(XVal)) ->
    % Use the simpler form. This will check if Y has a value.
    Out = b_reduce(s(Y = XVal), CS)
  ;(search(SCs, Y, val(YVal)) ->
    % Use the simpler form. This will check if X has a value.
    Out = b_reduce(s(X = YVal), CS)
  ;(X == Y ->
    Out = t
  ;
    Out = s(C)))).

nb_reduce(C, Cs) = Out :-
  C = (X = YVal),
  (search(Cs, X, val(XVal)) ->
    (XVal == YVal -> Out = t ; Out = f)
  ;
    Out = to_b_constraint(C))
;
  C = (X == Y),
  (search(Cs, X, val(XVal)) ->
    % Use the simpler form. This will check if Y has a value.
    Out = nb_reduce(Y = XVal, Cs)
  ;(search(Cs, Y, val(YVal)) ->
    % Use the simpler form. This will check if X has a value.
    Out = nb_reduce(X = YVal, Cs)
  ;(X == Y ->
    Out = t
  ;
    Out = to_b_constraint(C)))).

new_var(var(V)) :- next_var_int(V).

f_get(V, constraint_store(Cs, _, _, _)) = Val :-
  (search(Cs, V, val(Val1)) ->
    Val = yes(Val1)
  ;
    Val = no).
i_get(V, constraint_store(_, Cs, _, _)) = Val :-
  (search(Cs, V, val(Val1)) ->
    Val = yes(Val1)
  ;
    Val = no).
s_get(V, constraint_store(_, _, Cs, _)) = Val :-
  (search(Cs, V, val(Val1)) ->
    Val = yes(Val1)
  ;
    Val = no).

var_f_unify(var(V) := Val, CS, CSOut, Descs) :-  unify(V, f(':='(Val)), CS, CSOut, Descs).
var_f_unify(var(V) \= Val, CS, CSOut, Descs) :-  b_unify(not(f(V = Val)), CS, CSOut, Descs).
var_f_unify(var(V) \== var(Val), CS, CSOut, Descs) :- b_unify(not(f(V == Val)), CS, CSOut, Descs).
var_f_unify(var(V) >= Val, CS, CSOut, Descs) :-  unify(V, f('>='(Val)), CS, CSOut, Descs).
var_f_unify(var(V) =< Val, CS, CSOut, Descs) :-  unify(V, f('=<'(Val)), CS, CSOut, Descs).
var_f_unify(var(V) = C, CS, CSOut, Descs) :-     unify(V, f(C), CS, CSOut, Descs).
var_i_unify(var(V) := Val, CS, CSOut, Descs) :-  unify(V, i(':='(Val)), CS, CSOut, Descs).
var_i_unify(var(V) \= Val, CS, CSOut, Descs) :-  b_unify(not(i(V = Val)), CS, CSOut, Descs).
var_i_unify(var(V) \== var(Val), CS, CSOut, Descs) :- b_unify(not(i(V == Val)), CS, CSOut, Descs).
var_i_unify(var(V) >= Val, CS, CSOut, Descs) :-  unify(V, i('>='(Val)), CS, CSOut, Descs).
var_i_unify(var(V) =< Val, CS, CSOut, Descs) :-  unify(V, i('=<'(Val)), CS, CSOut, Descs).
var_i_unify(var(V) = C, CS, CSOut, Descs) :-     unify(V, i(C), CS, CSOut, Descs).
var_s_unify(var(V) := Val, CS, CSOut, Descs) :-  unify(V, s(':='(Val)), CS, CSOut, Descs).
var_s_unify(var(V) \= Val, CS, CSOut, Descs) :-  b_unify(not(s(V = Val)), CS, CSOut, Descs).
var_s_unify(var(V) \== var(Val), CS, CSOut, Descs) :- b_unify(not(s(V == Val)), CS, CSOut, Descs).

n_set_value(V, Val, Cs, CsOut, Descs) :-
  (search(Cs, V, ValOrCSet) ->
    (ValOrCSet = val(BoundVal) ->
      % Just confirm the existing value.
      Val == BoundVal,
      CsOut = Cs,
      Descs = []
    ;
      % Save the constraints.
      ValOrCSet = cs(CSet),
      % Set the binding as the only constraint.
      Cs1 = set(Cs, V, val(Val)),

      (verbose ->
        Descs1 = [n_constraint_to_string(V, ':='(Val))]
      ; 
        Descs1 = []),
      % Possibly evaluate all the constraints.
      foldl(
        (pred(C::in, CsIn-DescsIn::in, CsOut1-DescsOut1::out) is semidet :-
          n_new_value(Val, C, CsIn, CsOut1, Descs2),
          DescsOut1 = remove_dups(append(DescsIn, Descs2))),
        CSet, Cs1-Descs1, CsOut-Descs))
  ;  
    % Create the entry for V.
    CsOut = set(Cs, V, val(Val)),
    (verbose ->
      Descs = [n_constraint_to_string(V, ':='(Val))]
    ; 
      Descs = [])).

n_new_value(Val, var(X) + Y, Cs, CsOut, Descs) :-
  % We have Val = X + Y. Set X to Val - Y.
  n_set_value(X, Val - Y, Cs, CsOut, Descs).
n_new_value(Val, var(X) ++ var(Y), Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    % We have Val = X + Y and XVal. Set Y to Val - XVal.
    n_set_value(Y, Val - XVal, Cs, CsOut, Descs)
  ;(search(Cs, Y, val(YVal)) ->
    % We have Val = X + Y and YVal. Set X to Val - YVal.
    n_set_value(X, Val - YVal, Cs, CsOut, Descs)
  ;
    CsOut = Cs, Descs = [])).
n_new_value(Val, X - var(Y), Cs, CsOut, Descs) :-
  % We have Val = X - Y. Set Y to X - Val.
  n_set_value(Y, X - Val, Cs, CsOut, Descs).
n_new_value(Val, var(X) -- var(Y), Cs, CsOut, Descs) :-
  (search(Cs, X, val(XVal)) ->
    % We have Val = X - Y and XVal. Set Y to XVal - Val.
    n_set_value(Y, XVal - Val, Cs, CsOut, Descs)
  ;(search(Cs, Y, val(YVal)) ->
    % We have Val = X - Y and YVal. Set X to Val + YVal.
    n_set_value(X, Val + YVal, Cs, CsOut, Descs)
  ;
    CsOut = Cs, Descs = [])).
% Boolean constraints.
n_new_value(Val, '>='(X), Cs, Cs, []) :- Val >= X.
n_new_value(Val, '=<'(X), Cs, Cs, []) :- Val =< X.
% Ignore. (Shouldn't happen.)
n_new_value(_Val, ':='(_), Cs, Cs, []).

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

% Ignore. (Shouldn't happen.)
s_new_value(_Val, ':='(_), Cs, Cs, []).

f_constraint_to_string(V, C) = n_constraint_to_string(V, C).
i_constraint_to_string(V, C) = n_constraint_to_string(V, C).

n_constraint_to_string(V, ':='(Val)) =          format("(:= (var %i) %s)", [i(V), s(to_string(Val))]).
n_constraint_to_string(V, var(X1) + X2) =       format("(= (var %i) (+ (var %i) %s)", [i(V), i(X1), s(to_string(X2))]).
n_constraint_to_string(V, var(X1) ++ var(X2)) = format("(= (var %i) (+ (var %i) (var %i))", [i(V), i(X1), i(X2)]).
n_constraint_to_string(V, X1 - var(X2)) =       format("(= (var %i) (- %s (var %i))", [i(V), s(to_string(X1)), i(X2)]).
n_constraint_to_string(V, var(X1) -- var(X2)) = format("(= (var %i) (- (var %i) (var %i))", [i(V), i(X1), i(X2)]).
n_constraint_to_string(V, '>='(X)) =            format("(>= (var %i) %s)", [i(V), s(to_string(X))]).
n_constraint_to_string(V, '=<'(X)) =            format("(<= (var %i) %s)", [i(V), s(to_string(X))]).

b_constraint_to_string(t) =         format("t", []). % NOTE: We don't expect to ever print this.
b_constraint_to_string(f) =         format("f", []). % NOTE: We don't expect to ever print this.
b_constraint_to_string(f(X = Y)) =  format("(= (var %i) %s)", [i(X), s(to_string(Y))]).
b_constraint_to_string(f(X == Y)) = format("(f= (var %i) (var %i))", [i(X), i(Y)]).
b_constraint_to_string(i(X = Y)) =  format("(= (var %i) %s)", [i(X), s(to_string(Y))]).
b_constraint_to_string(i(X == Y)) = format("(i= (var %i) (var %i))", [i(X), i(Y)]).
b_constraint_to_string(s(X = Y)) =  format("(= (var %i) %s)", [i(X), s(Y)]).
b_constraint_to_string(s(X == Y)) = format("(s= (var %i) (var %i))", [i(X), i(Y)]).
b_constraint_to_string(and(X, Y)) = format("(and %s %s)", [s(b_constraint_to_string(X)), s(b_constraint_to_string(Y))]).
b_constraint_to_string(or(X, Y)) =  format("(or %s %s)", [s(b_constraint_to_string(X)), s(b_constraint_to_string(Y))]).
b_constraint_to_string(not(X)) =    format("(not %s)", [s(b_constraint_to_string(X))]).

s_constraint_to_string(V, ':='(Val)) =      format("(:= (var %i) %s)", [i(V), s(Val)]).

var_f_constraint_to_string(C) = var_n_constraint_to_string(C).
var_i_constraint_to_string(C) = var_n_constraint_to_string(C).

var_n_constraint_to_string(var(V) := Val) =       format("(:= (var %i) %s)", [i(V), s(to_string(Val))]).
var_n_constraint_to_string(var(V) \= Val) =       format("(<> (var %i) %s)", [i(V), s(to_string(Val))]).
var_n_constraint_to_string(var(V) \== var(Val)) = format("(<> (var %i) (var %i))", [i(V), i(Val)]).
var_n_constraint_to_string(var(V) >= Val) =       format("(>= (var %i) %s)", [i(V), s(to_string(Val))]).
var_n_constraint_to_string(var(V) =< Val) =       format("(<= (var %i) %s)", [i(V), s(to_string(Val))]).
var_n_constraint_to_string(var(V) = C) =          n_constraint_to_string(V, C).

var_s_constraint_to_string(var(V) := Val) =       format("(:= (var %i) %s)", [i(V), s(Val)]).
var_s_constraint_to_string(var(V) \= Val) =       format("(<> (var %i) %s)", [i(V), s(Val)]).
var_s_constraint_to_string(var(V) \== var(Val)) = format("(<> (var %i) (var %i))", [i(V), i(Val)]).

to_string(constraint_store(FCs, ICs, SCs, BCs)) = F ++ I ++ S ++ B :-
  (is_empty(FCs) -> F = "" ; F = "  float\n" ++ n_to_string(FCs)),
  (is_empty(ICs) -> I = "" ; I = "  int\n" ++ n_to_string(ICs)),
  (is_empty(SCs) -> S = "" ; S = "  string\n" ++ s_to_string(SCs)),
  (is_empty(BCs) -> B = ""
  ;
    B = "  bool expr\n" ++ foldl(func(C, ResultIn) = ResultIn ++ format("  %s\n", [s(b_constraint_to_string(C))]),
                            BCs, "")).
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

var_string_list_matches(XList, YList) = C :-
  length(XList) == length(YList),
  (XList = [] ->
    C = t
  ;
    XList = [var(X1)|RestX],
    YList = [var(Y1)|RestY],
    foldl(pred(var(XIn)::in, CIn-[var(YIn)|RestYIn]::in, and(CIn, s(XIn == YIn))-RestYIn::out) is semidet,
               RestX, s(X1 == Y1)-RestY, C-_)).

:- pragma no_inline(next_var_int/1).
:- pragma foreign_proc("C",
next_var_int(Int::out),
[promise_pure],
"
static long long int integer = 99;
Int = ++integer;
").

verbose.

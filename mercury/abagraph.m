:- module abagraph.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module printing.
:- import_module pair.
:- import_module list.
:- import_module set.

main(!IO) :-
  D = fact("a") - fact("y") - fact("z"),
  print_step(2,
    tuple(list_to_set([snd(fst(D)), fact("b"), fact("c")]), 
          list_to_set([not(fact("release"))]))).

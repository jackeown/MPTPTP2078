%------------------------------------------------------------------------------
% File     : MPT0194+2.007 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 007 of t113_enumset1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   5 unit)
%            Number of atoms       :    5 (   5 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   0 constant; 4-7 arity)
%            Number of variables   :   22 (   0 sgn;  22   !;   0   ?)
%            Maximal term depth    :    2 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(l123_enumset1,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) )).

fof(t112_enumset1,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) )).

fof(t74_enumset1,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) )).

fof(t79_enumset1,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) )).

fof(t113_enumset1,conjecture,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) )).

%------------------------------------------------------------------------------

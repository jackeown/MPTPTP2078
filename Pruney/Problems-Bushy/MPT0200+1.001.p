%------------------------------------------------------------------------------
% File     : MPT0200+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : enumset1__t125_enumset1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    3 (   3 unit)
%            Number of atoms       :    3 (   3 equality)
%            Maximal formula depth :    5 (   5 average)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    1 (   0 constant; 4-4 arity)
%            Number of variables   :   12 (   0 sgn;  12   !;   0   ?)
%            Maximal term depth    :    2 (   2 average)
% SPC      : FOF_THM_RFO_PEQ

% Comments : 
%------------------------------------------------------------------------------
fof(t108_enumset1,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) )).

fof(t119_enumset1,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) )).

fof(t125_enumset1,conjecture,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT0180+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : enumset1__t96_enumset1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    3 (   3 unit)
%            Number of atoms       :    3 (   3 equality)
%            Maximal formula depth :    3 (   2 average)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   0 constant; 1-8 arity)
%            Number of variables   :    4 (   0 sgn;   4   !;   0   ?)
%            Maximal term depth    :    2 (   2 average)
% SPC      : FOF_THM_RFO_PEQ

% Comments : 
%------------------------------------------------------------------------------
fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(t95_enumset1,axiom,(
    ! [A,B] : k6_enumset1(A,A,A,A,A,A,A,B) = k2_tarski(A,B) )).

fof(t96_enumset1,conjecture,(
    ! [A] : k6_enumset1(A,A,A,A,A,A,A,A) = k1_tarski(A) )).

%------------------------------------------------------------------------------

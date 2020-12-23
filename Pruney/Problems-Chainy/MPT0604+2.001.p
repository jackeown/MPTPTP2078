%------------------------------------------------------------------------------
% File     : MPT0604+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t208_relat_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    3 (   3 unit)
%            Number of atoms       :    3 (   3 equality)
%            Maximal formula depth :    3 (   2 average)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :    4 (   0 sgn;   4   !;   0   ?)
%            Maximal term depth    :    4 (   3 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(t32_relat_1,axiom,(
    ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) )).

fof(t208_relat_1,conjecture,(
    ! [A] : k3_relat_1(k1_tarski(k4_tarski(A,A))) = k1_tarski(A) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT0215+2.025 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 025 of t8_zfmisc_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   2 unit)
%            Number of atoms       :    8 (   7 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :    4 (   0   ~;   1   |;   0   &)
%                                         (   2 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   0 constant; 1-4 arity)
%            Number of variables   :   10 (   0 sgn;  10   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) )).

fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(t77_enumset1,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) )).

fof(t8_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => A = B ) )).

%------------------------------------------------------------------------------

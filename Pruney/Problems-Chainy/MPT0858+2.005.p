%------------------------------------------------------------------------------
% File     : MPT0858+2.005 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 005 of t14_mcart_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    6 (   2 unit)
%            Number of atoms       :   15 (   8 equality)
%            Maximal formula depth :    8 (   5 average)
%            Number of connectives :    9 (   0   ~;   1   |;   3   &)
%                                         (   2 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    6 (   0 constant; 1-3 arity)
%            Number of variables   :   16 (   0 sgn;  16   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
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

fof(t70_enumset1,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) )).

fof(t10_mcart_1,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) )).

fof(t13_mcart_1,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) )).

fof(t14_mcart_1,conjecture,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
     => ( k1_mcart_1(A) = B
        & k2_mcart_1(A) = C ) ) )).

%------------------------------------------------------------------------------

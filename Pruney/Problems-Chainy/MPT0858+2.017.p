%------------------------------------------------------------------------------
% File     : MPT0858+2.017 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 017 of t14_mcart_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   1 unit)
%            Number of atoms       :   10 (   5 equality)
%            Maximal formula depth :    6 (   5 average)
%            Number of connectives :    6 (   0   ~;   0   |;   3   &)
%                                         (   0 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    5 (   0 constant; 1-4 arity)
%            Number of variables   :   10 (   0 sgn;  10   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t82_enumset1,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) )).

fof(t12_mcart_1,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
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

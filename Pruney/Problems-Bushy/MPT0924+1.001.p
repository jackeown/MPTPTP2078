%------------------------------------------------------------------------------
% File     : MPT0924+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : mcart_1__t84_mcart_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    6 (   3 unit)
%            Number of atoms       :   15 (   3 equality)
%            Maximal formula depth :   13 (   7 average)
%            Number of connectives :    9 (   0   ~;   0   |;   6   &)
%                                         (   3 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    6 (   0 constant; 2-4 arity)
%            Number of variables   :   29 (   0 sgn;  29   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d3_mcart_1,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) )).

fof(d4_mcart_1,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) )).

fof(t106_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) )).

fof(t54_mcart_1,axiom,(
    ! [A,B,C,D] : k3_zfmisc_1(k2_zfmisc_1(A,B),C,D) = k4_zfmisc_1(A,B,C,D) )).

fof(t73_mcart_1,axiom,(
    ! [A,B,C,D,E,F] :
      ( r2_hidden(k3_mcart_1(A,B,C),k3_zfmisc_1(D,E,F))
    <=> ( r2_hidden(A,D)
        & r2_hidden(B,E)
        & r2_hidden(C,F) ) ) )).

fof(t84_mcart_1,conjecture,(
    ! [A,B,C,D,E,F,G,H] :
      ( r2_hidden(k4_mcart_1(A,B,C,D),k4_zfmisc_1(E,F,G,H))
    <=> ( r2_hidden(A,E)
        & r2_hidden(B,F)
        & r2_hidden(C,G)
        & r2_hidden(D,H) ) ) )).

%------------------------------------------------------------------------------

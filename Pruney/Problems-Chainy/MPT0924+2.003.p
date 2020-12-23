%------------------------------------------------------------------------------
% File     : MPT0924+2.003 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 003 of t84_mcart_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    9 (   4 unit)
%            Number of atoms       :   30 (   7 equality)
%            Maximal formula depth :   13 (   8 average)
%            Number of connectives :   25 (   4   ~;   0   |;  13   &)
%                                         (   5 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :   10 (   0 constant; 1-4 arity)
%            Number of variables   :   41 (   0 sgn;  38   !;   3   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) )).

fof(d2_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) )).

fof(t136_zfmisc_1,axiom,(
    ! [A] :
    ? [B] :
      ( r2_hidden(A,B)
      & ! [C,D] :
          ( ( r2_hidden(C,B)
            & r1_tarski(D,C) )
         => r2_hidden(D,B) )
      & ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(k1_zfmisc_1(C),B) )
      & ! [C] :
          ~ ( r1_tarski(C,B)
            & ~ r2_tarski(C,B)
            & ~ r2_hidden(C,B) ) ) )).

fof(d3_mcart_1,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) )).

fof(d3_zfmisc_1,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) )).

fof(d4_mcart_1,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) )).

fof(d4_zfmisc_1,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) )).

fof(t10_mcart_1,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) )).

fof(t84_mcart_1,conjecture,(
    ! [A,B,C,D,E,F,G,H] :
      ( r2_hidden(k4_mcart_1(A,B,C,D),k4_zfmisc_1(E,F,G,H))
    <=> ( r2_hidden(A,E)
        & r2_hidden(B,F)
        & r2_hidden(C,G)
        & r2_hidden(D,H) ) ) )).

%------------------------------------------------------------------------------

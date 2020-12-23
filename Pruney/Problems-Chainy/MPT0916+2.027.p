%------------------------------------------------------------------------------
% File     : MPT0916+2.027 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 027 of t76_mcart_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   2 unit)
%            Number of atoms       :   32 (   7 equality)
%            Maximal formula depth :   15 (   8 average)
%            Number of connectives :   33 (   9   ~;   0   |;  15   &)
%                                         (   1 <=>;   8  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 2-2 arity)
%            Number of functors    :    9 (   1 constant; 0-4 arity)
%            Number of variables   :   28 (   0 sgn;  27   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t3_xboole_0,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) )).

fof(t64_xboole_1,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) )).

fof(t65_xboole_1,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(d3_zfmisc_1,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) )).

fof(t10_mcart_1,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) )).

fof(t50_mcart_1,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) )).

fof(t76_mcart_1,conjecture,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(A))
     => ! [E] :
          ( m1_subset_1(E,k1_zfmisc_1(B))
         => ! [F] :
              ( m1_subset_1(F,k1_zfmisc_1(C))
             => ! [G] :
                  ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                 => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                   => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                      & r2_hidden(k6_mcart_1(A,B,C,G),E)
                      & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT0927+2.008 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 008 of t87_mcart_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   3 unit)
%            Number of atoms       :   30 (  10 equality)
%            Maximal formula depth :   19 (   8 average)
%            Number of connectives :   29 (   7   ~;   0   |;  12   &)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :   11 (   1 constant; 0-5 arity)
%            Number of variables   :   30 (   0 sgn;  30   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t2_xboole_1,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) )).

fof(l3_subset_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) )).

fof(t7_ordinal1,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) )).

fof(d3_zfmisc_1,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) )).

fof(d4_zfmisc_1,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) )).

fof(t10_mcart_1,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) )).

fof(t61_mcart_1,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ( k8_mcart_1(A,B,C,D,E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k9_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k10_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(E))
                & k11_mcart_1(A,B,C,D,E) = k2_mcart_1(E) ) ) ) )).

fof(t87_mcart_1,conjecture,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k1_zfmisc_1(A))
     => ! [F] :
          ( m1_subset_1(F,k1_zfmisc_1(B))
         => ! [G] :
              ( m1_subset_1(G,k1_zfmisc_1(C))
             => ! [H] :
                  ( m1_subset_1(H,k1_zfmisc_1(D))
                 => ! [I] :
                      ( m1_subset_1(I,k4_zfmisc_1(A,B,C,D))
                     => ( r2_hidden(I,k4_zfmisc_1(E,F,G,H))
                       => ( r2_hidden(k8_mcart_1(A,B,C,D,I),E)
                          & r2_hidden(k9_mcart_1(A,B,C,D,I),F)
                          & r2_hidden(k10_mcart_1(A,B,C,D,I),G)
                          & r2_hidden(k11_mcart_1(A,B,C,D,I),H) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

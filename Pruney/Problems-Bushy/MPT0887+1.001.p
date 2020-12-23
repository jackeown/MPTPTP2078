%------------------------------------------------------------------------------
% File     : MPT0887+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : mcart_1__t47_mcart_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    7 (   0 unit)
%            Number of atoms       :   38 (  25 equality)
%            Maximal formula depth :   18 (  13 average)
%            Number of connectives :   51 (  20   ~;   0   |;  16   &)
%                                         (   3 <=>;  12  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    6 (   1 constant; 0-4 arity)
%            Number of variables   :   43 (   0 sgn;  39   !;   4   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d5_mcart_1,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ! [E] :
                  ( m1_subset_1(E,A)
                 => ( E = k5_mcart_1(A,B,C,D)
                  <=> ! [F,G,H] :
                        ( D = k3_mcart_1(F,G,H)
                       => E = F ) ) ) ) ) )).

fof(d6_mcart_1,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ! [E] :
                  ( m1_subset_1(E,B)
                 => ( E = k6_mcart_1(A,B,C,D)
                  <=> ! [F,G,H] :
                        ( D = k3_mcart_1(F,G,H)
                       => E = G ) ) ) ) ) )).

fof(d7_mcart_1,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ! [E] :
                  ( m1_subset_1(E,C)
                 => ( E = k7_mcart_1(A,B,C,D)
                  <=> ! [F,G,H] :
                        ( D = k3_mcart_1(F,G,H)
                       => E = H ) ) ) ) ) )).

fof(dt_k5_mcart_1,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) )).

fof(dt_k6_mcart_1,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) )).

fof(dt_k7_mcart_1,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) )).

fof(t47_mcart_1,conjecture,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ? [E,F,G] :
                ( D = k3_mcart_1(E,F,G)
                & ~ ( k5_mcart_1(A,B,C,D) = E
                    & k6_mcart_1(A,B,C,D) = F
                    & k7_mcart_1(A,B,C,D) = G ) ) ) ) )).

%------------------------------------------------------------------------------

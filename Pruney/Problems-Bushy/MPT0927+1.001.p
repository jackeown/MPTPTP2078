%------------------------------------------------------------------------------
% File     : MPT0927+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : mcart_1__t87_mcart_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   15 (   3 unit)
%            Number of atoms       :   53 (  20 equality)
%            Maximal formula depth :   27 (   8 average)
%            Number of connectives :   55 (  17   ~;   1   |;  23   &)
%                                         (   1 <=>;  13  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    8 (   2 constant; 0-5 arity)
%            Number of variables   :   55 (   0 sgn;  52   !;   3   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

fof(dt_k10_mcart_1,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k10_mcart_1(A,B,C,D,E),C) ) )).

fof(dt_k11_mcart_1,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k11_mcart_1(A,B,C,D,E),D) ) )).

fof(dt_k8_mcart_1,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k8_mcart_1(A,B,C,D,E),A) ) )).

fof(dt_k9_mcart_1,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) )).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(existence_m1_subset_1,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t55_mcart_1,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) )).

fof(t5_subset,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(t86_mcart_1,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & E != k1_xboole_0
        & F != k1_xboole_0
        & G != k1_xboole_0
        & H != k1_xboole_0
        & ? [I] :
            ( m1_subset_1(I,k4_zfmisc_1(A,B,C,D))
            & ? [J] :
                ( m1_subset_1(J,k4_zfmisc_1(E,F,G,H))
                & I = J
                & ~ ( k8_mcart_1(A,B,C,D,I) = k8_mcart_1(E,F,G,H,J)
                    & k9_mcart_1(A,B,C,D,I) = k9_mcart_1(E,F,G,H,J)
                    & k10_mcart_1(A,B,C,D,I) = k10_mcart_1(E,F,G,H,J)
                    & k11_mcart_1(A,B,C,D,I) = k11_mcart_1(E,F,G,H,J) ) ) ) ) )).

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

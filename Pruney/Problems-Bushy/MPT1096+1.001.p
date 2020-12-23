%------------------------------------------------------------------------------
% File     : MPT1096+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : finset_1__t31_finset_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   14 (   3 unit)
%            Number of atoms       :   55 (  11 equality)
%            Maximal formula depth :   17 (   6 average)
%            Number of connectives :   56 (  15   ~;   3   |;  19   &)
%                                         (   7 <=>;  12  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    8 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :   42 (   1 sgn;  42   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) )).

fof(d1_tarski,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) )).

fof(d3_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) )).

fof(d9_ordinal1,axiom,(
    ! [A] :
      ( v6_ordinal1(A)
    <=> ! [B,C] :
          ( ( r2_hidden(B,A)
            & r2_hidden(C,A) )
         => r3_xboole_0(B,C) ) ) )).

fof(d9_xboole_0,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) )).

fof(reflexivity_r3_xboole_0,axiom,(
    ! [A,B] : r3_xboole_0(A,A) )).

fof(s2_finset_1__e6_54__finset_1,axiom,(
    ! [A] :
      ( ( v1_finset_1(A)
        & ~ ( k1_xboole_0 != k1_xboole_0
            & ! [B] :
                ~ ( r2_hidden(B,k1_xboole_0)
                  & ! [C] :
                      ( r2_hidden(C,k1_xboole_0)
                     => r1_tarski(C,B) ) ) )
        & ! [D,E] :
            ( ( r2_hidden(D,A)
              & r1_tarski(E,A)
              & ~ ( E != k1_xboole_0
                  & ! [F] :
                      ~ ( r2_hidden(F,E)
                        & ! [G] :
                            ( r2_hidden(G,E)
                           => r1_tarski(G,F) ) ) ) )
           => ~ ( k2_xboole_0(E,k1_tarski(D)) != k1_xboole_0
                & ! [H] :
                    ~ ( r2_hidden(H,k2_xboole_0(E,k1_tarski(D)))
                      & ! [I] :
                          ( r2_hidden(I,k2_xboole_0(E,k1_tarski(D)))
                         => r1_tarski(I,H) ) ) ) ) )
     => ~ ( A != k1_xboole_0
          & ! [J] :
              ~ ( r2_hidden(J,A)
                & ! [K] :
                    ( r2_hidden(K,A)
                   => r1_tarski(K,J) ) ) ) ) )).

fof(t1_boole,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A )).

fof(t1_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(t4_subset,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t31_finset_1,conjecture,(
    ! [A] :
      ~ ( v1_finset_1(A)
        & A != k1_xboole_0
        & v6_ordinal1(A)
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C] :
                  ( r2_hidden(C,A)
                 => r1_tarski(C,B) ) ) ) )).

%------------------------------------------------------------------------------

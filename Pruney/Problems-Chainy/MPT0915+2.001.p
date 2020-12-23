%------------------------------------------------------------------------------
% File     : MPT0915+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t75_mcart_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    2 (   0 unit)
%            Number of atoms       :   19 (  16 equality)
%            Maximal formula depth :   22 (  18 average)
%            Number of connectives :   30 (  13   ~;   0   |;  16   &)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    7 (   1 constant; 0-4 arity)
%            Number of variables   :   12 (   0 sgn;  10   !;   2   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
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

fof(t75_mcart_1,conjecture,(
    ! [A,B,C,D,E,F] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & E != k1_xboole_0
        & F != k1_xboole_0
        & ? [G] :
            ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
            & ? [H] :
                ( m1_subset_1(H,k3_zfmisc_1(D,E,F))
                & G = H
                & ~ ( k5_mcart_1(A,B,C,G) = k5_mcart_1(D,E,F,H)
                    & k6_mcart_1(A,B,C,G) = k6_mcart_1(D,E,F,H)
                    & k7_mcart_1(A,B,C,G) = k7_mcart_1(D,E,F,H) ) ) ) ) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT0379+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t61_subset_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   12 (   3 unit)
%            Number of atoms       :   46 (  11 equality)
%            Maximal formula depth :   18 (   8 average)
%            Number of connectives :   45 (  11   ~;   0   |;   7   &)
%                                         (   8 <=>;  19  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    6 (   1 constant; 0-7 arity)
%            Number of variables   :   52 (   0 sgn;  52   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) )).

fof(t8_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) )).

fof(t57_enumset1,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) )).

fof(t60_enumset1,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) )).

fof(d1_zfmisc_1,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) )).

fof(t38_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) )).

fof(d2_subset_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) )).

fof(d3_enumset1,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) )).

fof(fc1_subset_1,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) )).

fof(l3_subset_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) )).

fof(t59_subset_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( m1_subset_1(C,A)
         => ! [D] :
              ( m1_subset_1(D,A)
             => ! [E] :
                  ( m1_subset_1(E,A)
                 => ! [F] :
                      ( m1_subset_1(F,A)
                     => ( A != k1_xboole_0
                       => m1_subset_1(k3_enumset1(B,C,D,E,F),k1_zfmisc_1(A)) ) ) ) ) ) ) )).

fof(t61_subset_1,conjecture,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( m1_subset_1(C,A)
         => ! [D] :
              ( m1_subset_1(D,A)
             => ! [E] :
                  ( m1_subset_1(E,A)
                 => ! [F] :
                      ( m1_subset_1(F,A)
                     => ! [G] :
                          ( m1_subset_1(G,A)
                         => ! [H] :
                              ( m1_subset_1(H,A)
                             => ( A != k1_xboole_0
                               => m1_subset_1(k5_enumset1(B,C,D,E,F,G,H),k1_zfmisc_1(A)) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

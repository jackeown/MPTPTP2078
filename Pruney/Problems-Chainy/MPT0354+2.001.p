%------------------------------------------------------------------------------
% File     : MPT0354+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t33_subset_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   15 (   6 unit)
%            Number of atoms       :   33 (  11 equality)
%            Maximal formula depth :    6 (   5 average)
%            Number of connectives :   20 (   2   ~;   0   |;   4   &)
%                                         (   4 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    9 (   0 constant; 1-3 arity)
%            Number of variables   :   36 (   0 sgn;  36   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) )).

fof(t36_xboole_1,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) )).

fof(t48_xboole_1,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) )).

fof(t52_xboole_1,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) )).

fof(commutativity_k2_tarski,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) )).

fof(d1_zfmisc_1,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) )).

fof(l51_zfmisc_1,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) )).

fof(commutativity_k4_subset_1,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) )).

fof(d2_subset_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) )).

fof(d5_subset_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) )).

fof(fc1_subset_1,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) )).

fof(involutiveness_k3_subset_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) )).

fof(redefinition_k4_subset_1,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) )).

fof(redefinition_k7_subset_1,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) )).

fof(t33_subset_1,conjecture,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT1098+2.006 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 006 of t33_finset_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    6 (   1 unit)
%            Number of atoms       :   19 (   4 equality)
%            Maximal formula depth :   14 (   7 average)
%            Number of connectives :   17 (   4   ~;   0   |;  11   &)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 2-2 arity)
%            Number of variables   :   19 (   0 sgn;  19   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) )).

fof(t10_xboole_1,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) )).

fof(t12_xboole_1,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) )).

fof(t120_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) )).

fof(t32_finset_1,axiom,(
    ! [A,B,C] :
      ~ ( v1_finset_1(A)
        & r1_tarski(A,k2_zfmisc_1(B,C))
        & ! [D,E] :
            ~ ( v1_finset_1(D)
              & r1_tarski(D,B)
              & v1_finset_1(E)
              & r1_tarski(E,C)
              & r1_tarski(A,k2_zfmisc_1(D,E)) ) ) )).

fof(t33_finset_1,conjecture,(
    ! [A,B,C] :
      ~ ( v1_finset_1(A)
        & r1_tarski(A,k2_zfmisc_1(B,C))
        & ! [D] :
            ~ ( v1_finset_1(D)
              & r1_tarski(D,B)
              & r1_tarski(A,k2_zfmisc_1(D,C)) ) ) )).

%------------------------------------------------------------------------------

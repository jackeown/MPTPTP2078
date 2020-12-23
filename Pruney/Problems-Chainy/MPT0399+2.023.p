%------------------------------------------------------------------------------
% File     : MPT0399+2.023 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 023 of t21_setfam_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    9 (   2 unit)
%            Number of atoms       :   19 (   3 equality)
%            Maximal formula depth :   10 (   4 average)
%            Number of connectives :   16 (   6   ~;   0   |;   5   &)
%                                         (   2 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   1 constant; 0-1 arity)
%            Number of variables   :   16 (   0 sgn;  16   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) )).

fof(t7_xboole_0,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) )).

fof(l49_zfmisc_1,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) )).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 )).

fof(d2_setfam_1,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) )).

fof(t18_setfam_1,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(t5_subset,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) )).

fof(t21_setfam_1,conjecture,(
    ! [A] :
      ( r1_setfam_1(A,k1_xboole_0)
     => A = k1_xboole_0 ) )).

%------------------------------------------------------------------------------

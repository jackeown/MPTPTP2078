%------------------------------------------------------------------------------
% File     : MPT0381+2.023 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 023 of t63_subset_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   10 (   5 unit)
%            Number of atoms       :   20 (   6 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :   16 (   6   ~;   0   |;   2   &)
%                                         (   3 <=>;   5  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    7 (   1 constant; 0-5 arity)
%            Number of variables   :   21 (   0 sgn;  20   !;   1   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : v1_xboole_0(A) )).

fof(t7_xboole_0,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) )).

fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(t70_enumset1,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) )).

fof(t71_enumset1,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) )).

fof(t72_enumset1,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) )).

fof(d2_subset_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) )).

fof(t55_subset_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) )).

fof(t63_subset_1,conjecture,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) )).

%------------------------------------------------------------------------------

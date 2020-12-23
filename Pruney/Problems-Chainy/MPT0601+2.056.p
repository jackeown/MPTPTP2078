%------------------------------------------------------------------------------
% File     : MPT0601+2.056 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 056 of t205_relat_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   10 (   5 unit)
%            Number of atoms       :   19 (   9 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   14 (   5   ~;   0   |;   2   &)
%                                         (   5 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :   11 (   1 constant; 0-3 arity)
%            Number of variables   :   22 (   0 sgn;  21   !;   1   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t7_xboole_0,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) )).

fof(t100_xboole_1,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) )).

fof(t4_boole,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 )).

fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(t70_enumset1,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) )).

fof(t64_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) )).

fof(t12_setfam_1,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) )).

fof(d4_relat_1,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) )).

fof(t204_relat_1,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) )).

fof(t205_relat_1,conjecture,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) )).

%------------------------------------------------------------------------------

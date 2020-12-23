%------------------------------------------------------------------------------
% File     : MPT0550+2.023 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 023 of t152_relat_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    7 (   1 unit)
%            Number of atoms       :   18 (   9 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   13 (   2   ~;   1   |;   3   &)
%                                         (   0 <=>;   7  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    6 (   1 constant; 0-2 arity)
%            Number of variables   :   11 (   0 sgn;  11   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(dt_k6_relat_1,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) )).

fof(dt_k7_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) )).

fof(t148_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) )).

fof(t64_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) )).

fof(t71_relat_1,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) )).

fof(t91_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) )).

fof(t152_relat_1,conjecture,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) )).

%------------------------------------------------------------------------------

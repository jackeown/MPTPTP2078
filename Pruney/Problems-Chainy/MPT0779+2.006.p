%------------------------------------------------------------------------------
% File     : MPT0779+2.006 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 006 of t28_wellord1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   13 (   6 equality)
%            Maximal formula depth :    9 (   5 average)
%            Number of connectives :    8 (   0   ~;   0   |;   3   &)
%                                         (   0 <=>;   5  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    6 (   0 constant; 1-2 arity)
%            Number of variables   :   12 (   0 sgn;  11   !;   1   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t90_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) )).

fof(t98_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) )).

fof(s3_funct_1__e1_27_1__funct_1,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = B
      & ! [D] :
          ( r2_hidden(D,B)
         => k1_funct_1(C,D) = o_1_0_funct_1(A) ) ) )).

fof(t26_wellord1,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) )).

fof(t28_wellord1,conjecture,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(k2_wellord1(B,A),A) = k2_wellord1(B,A) ) )).

%------------------------------------------------------------------------------

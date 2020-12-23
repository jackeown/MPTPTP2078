%------------------------------------------------------------------------------
% File     : MPT1094+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t29_finset_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   12 (   1 unit)
%            Number of atoms       :   29 (   6 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :   17 (   0   ~;   0   |;   6   &)
%                                         (   1 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    8 (   0 constant; 1-2 arity)
%            Number of variables   :   20 (   0 sgn;  20   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t145_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) )).

fof(t146_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) )).

fof(t22_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) )).

fof(t90_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) )).

fof(dt_k7_funct_3,axiom,(
    ! [A,B] :
      ( v1_relat_1(k7_funct_3(A,B))
      & v1_funct_1(k7_funct_3(A,B)) ) )).

fof(fc10_finset_1,axiom,(
    ! [A,B] :
      ( v1_finset_1(B)
     => v1_finset_1(k3_xboole_0(A,B)) ) )).

fof(fc13_finset_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k9_relat_1(A,B)) ) )).

fof(fc14_finset_1,axiom,(
    ! [A,B] :
      ( ( v1_finset_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k2_zfmisc_1(A,B)) ) )).

fof(redefinition_k9_funct_3,axiom,(
    ! [A,B] : k9_funct_3(A,B) = k7_funct_3(A,B) )).

fof(t100_funct_3,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => k9_relat_1(k9_funct_3(k1_relat_1(A),k2_relat_1(A)),A) = k1_relat_1(A) ) )).

fof(t15_finset_1,axiom,(
    ! [A,B] :
      ( v1_finset_1(A)
     => v1_finset_1(k3_xboole_0(A,B)) ) )).

fof(t29_finset_1,conjecture,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_finset_1(k1_relat_1(A))
      <=> v1_finset_1(A) ) ) )).

%------------------------------------------------------------------------------

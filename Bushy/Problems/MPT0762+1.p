%------------------------------------------------------------------------------
% File     : MPT0762+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : wellord1__t8_wellord1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   14 (   6 unit)
%            Number of atoms       :   38 (   2 equality)
%            Maximal formula depth :    9 (   4 average)
%            Number of connectives :   24 (   0   ~;   0   |;   8   &)
%                                         (   8 <=>;   8  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   15 (   1 propositional; 0-2 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :   13 (   1 sgn;  13   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t8_wellord1,conjecture,(
    ! [A] :
      ( v1_relat_1(A)
     => ( r2_wellord1(A,k3_relat_1(A))
      <=> v2_wellord1(A) ) ) )).

fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) )).

fof(d12_relat_2,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v4_relat_2(A)
      <=> r4_relat_2(A,k3_relat_1(A)) ) ) )).

fof(d14_relat_2,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> r6_relat_2(A,k3_relat_1(A)) ) ) )).

fof(d16_relat_2,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v8_relat_2(A)
      <=> r8_relat_2(A,k3_relat_1(A)) ) ) )).

fof(d4_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) )).

fof(d5_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r2_wellord1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B)
            & r1_wellord1(A,B) ) ) ) )).

fof(d9_relat_2,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> r1_relat_2(A,k3_relat_1(A)) ) ) )).

fof(dt_k1_relat_1,axiom,(
    $true )).

fof(dt_k2_relat_1,axiom,(
    $true )).

fof(dt_k2_xboole_0,axiom,(
    $true )).

fof(dt_k3_relat_1,axiom,(
    $true )).

fof(idempotence_k2_xboole_0,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A )).

fof(t5_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_wellord1(A)
      <=> r1_wellord1(A,k3_relat_1(A)) ) ) )).

%------------------------------------------------------------------------------

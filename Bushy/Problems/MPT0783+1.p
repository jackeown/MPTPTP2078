%------------------------------------------------------------------------------
% File     : MPT0783+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : wellord1__t32_wellord1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   12 (   4 unit)
%            Number of atoms       :   31 (   2 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   19 (   0   ~;   0   |;   4   &)
%                                         (   1 <=>;  14  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    9 (   1 propositional; 0-2 arity)
%            Number of functors    :    2 (   0 constant; 2-2 arity)
%            Number of variables   :   19 (   1 sgn;  19   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t32_wellord1,conjecture,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => v2_wellord1(k2_wellord1(B,A)) ) ) )).

fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) )).

fof(d4_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) )).

fof(dt_k2_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) )).

fof(dt_k2_zfmisc_1,axiom,(
    $true )).

fof(dt_k3_xboole_0,axiom,(
    $true )).

fof(idempotence_k3_xboole_0,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A )).

fof(t22_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v1_relat_2(B)
       => v1_relat_2(k2_wellord1(B,A)) ) ) )).

fof(t23_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v6_relat_2(B)
       => v6_relat_2(k2_wellord1(B,A)) ) ) )).

fof(t24_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v8_relat_2(B)
       => v8_relat_2(k2_wellord1(B,A)) ) ) )).

fof(t25_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_2(B)
       => v4_relat_2(k2_wellord1(B,A)) ) ) )).

fof(t31_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v1_wellord1(B)
       => v1_wellord1(k2_wellord1(B,A)) ) ) )).

%------------------------------------------------------------------------------

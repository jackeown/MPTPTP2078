%------------------------------------------------------------------------------
% File     : MPT0790+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : wellord1__t40_wellord1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   21 (  14 unit)
%            Number of atoms       :   31 (   8 equality)
%            Maximal formula depth :    6 (   3 average)
%            Number of connectives :   10 (   0   ~;   0   |;   1   &)
%                                         (   1 <=>;   8  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   1 propositional; 0-2 arity)
%            Number of functors    :    9 (   0 constant; 1-2 arity)
%            Number of variables   :   23 (   2 sgn;  22   !;   1   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t40_wellord1,conjecture,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => k3_relat_1(k2_wellord1(B,k1_wellord1(B,A))) = k1_wellord1(B,A) ) ) )).

fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) )).

fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) )).

fof(d6_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) )).

fof(d6_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) )).

fof(dt_k1_relat_1,axiom,(
    $true )).

fof(dt_k1_wellord1,axiom,(
    $true )).

fof(dt_k1_zfmisc_1,axiom,(
    $true )).

fof(dt_k2_relat_1,axiom,(
    $true )).

fof(dt_k2_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) )).

fof(dt_k2_xboole_0,axiom,(
    $true )).

fof(dt_k2_zfmisc_1,axiom,(
    $true )).

fof(dt_k3_relat_1,axiom,(
    $true )).

fof(dt_k3_xboole_0,axiom,(
    $true )).

fof(dt_m1_subset_1,axiom,(
    $true )).

fof(existence_m1_subset_1,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) )).

fof(idempotence_k2_xboole_0,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A )).

fof(idempotence_k3_xboole_0,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A )).

fof(t13_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_wellord1(B,A),k3_relat_1(B)) ) )).

fof(t39_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ( v2_wellord1(B)
          & r1_tarski(A,k3_relat_1(B)) )
       => k3_relat_1(k2_wellord1(B,A)) = A ) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

%------------------------------------------------------------------------------

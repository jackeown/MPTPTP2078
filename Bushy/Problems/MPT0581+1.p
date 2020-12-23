%------------------------------------------------------------------------------
% File     : MPT0581+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : relat_1__t185_relat_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    6 (   3 unit)
%            Number of atoms       :   12 (   6 equality)
%            Maximal formula depth :    9 (   4 average)
%            Number of connectives :    6 (   0   ~;   0   |;   1   &)
%                                         (   0 <=>;   5  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   1 propositional; 0-2 arity)
%            Number of functors    :    2 (   0 constant; 2-2 arity)
%            Number of variables   :   13 (   1 sgn;  13   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t185_relat_1,conjecture,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C,D] :
              ( ( k7_relat_1(A,C) = k7_relat_1(B,C)
                & k7_relat_1(A,D) = k7_relat_1(B,D) )
             => k7_relat_1(A,k2_xboole_0(C,D)) = k7_relat_1(B,k2_xboole_0(C,D)) ) ) ) )).

fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) )).

fof(dt_k2_xboole_0,axiom,(
    $true )).

fof(dt_k7_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) )).

fof(idempotence_k2_xboole_0,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A )).

fof(t107_relat_1,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) )).

%------------------------------------------------------------------------------

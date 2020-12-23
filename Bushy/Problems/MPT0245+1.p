%------------------------------------------------------------------------------
% File     : MPT0245+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : zfmisc_1__t40_zfmisc_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   13 (   7 unit)
%            Number of atoms       :   22 (   5 equality)
%            Maximal formula depth :    7 (   3 average)
%            Number of connectives :   13 (   4   ~;   2   |;   3   &)
%                                         (   0 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   1 propositional; 0-2 arity)
%            Number of functors    :    4 (   2 constant; 0-2 arity)
%            Number of variables   :   15 (   0 sgn;  15   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t40_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r2_hidden(C,A)
        | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) )).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(dt_k1_xboole_0,axiom,(
    $true )).

fof(t3_boole,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A )).

fof(t4_boole,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 )).

fof(t8_boole,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) )).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) )).

fof(dt_k1_tarski,axiom,(
    $true )).

fof(dt_k4_xboole_0,axiom,(
    $true )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(l2_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r2_hidden(C,A)
        | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) )).

%------------------------------------------------------------------------------

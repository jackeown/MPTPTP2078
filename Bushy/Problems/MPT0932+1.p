%------------------------------------------------------------------------------
% File     : MPT0932+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : mcart_1__t93_mcart_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   22 (  10 unit)
%            Number of atoms       :   46 (  10 equality)
%            Maximal formula depth :    9 (   4 average)
%            Number of connectives :   30 (   6   ~;   1   |;   9   &)
%                                         (   3 <=>;  11  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   1 propositional; 0-2 arity)
%            Number of functors    :    9 (   2 constant; 0-2 arity)
%            Number of variables   :   30 (   0 sgn;  27   !;   3   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t93_mcart_1,conjecture,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r2_hidden(B,A)
         => r2_hidden(k2_mcart_1(B),k11_relat_1(A,k1_mcart_1(B))) ) ) )).

fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) )).

fof(d16_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) )).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

fof(dt_k11_relat_1,axiom,(
    $true )).

fof(dt_k1_mcart_1,axiom,(
    $true )).

fof(dt_k1_tarski,axiom,(
    $true )).

fof(dt_k1_xboole_0,axiom,(
    $true )).

fof(dt_k2_mcart_1,axiom,(
    $true )).

fof(dt_k9_relat_1,axiom,(
    $true )).

fof(dt_m1_subset_1,axiom,(
    $true )).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(existence_m1_subset_1,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) )).

fof(fraenkel_a_2_0_mcart_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(B)
        & v1_relat_1(B) )
     => ( r2_hidden(A,a_2_0_mcart_1(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,B)
            & A = k2_mcart_1(D)
            & k1_mcart_1(D) = C ) ) ) )).

fof(fraenkel_a_2_1_mcart_1,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,a_2_1_mcart_1(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,B)
            & A = k2_mcart_1(D)
            & k1_mcart_1(D) = k1_mcart_1(C) ) ) ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t2_tarski,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(t8_boole,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) )).

fof(t92_mcart_1,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ! [B] : k11_relat_1(A,B) = a_2_0_mcart_1(A,B) ) )).

%------------------------------------------------------------------------------

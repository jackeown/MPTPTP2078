%------------------------------------------------------------------------------
% File     : MPT0735+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : ordinal1__t23_ordinal1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 1076 ( 304 unit)
%            Number of atoms       : 3134 ( 890 equality)
%            Maximal formula depth :   26 (   6 average)
%            Number of connectives : 2473 ( 415   ~;  30   |; 774   &)
%                                         ( 185 <=>;1069  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   32 (   1 propositional; 0-2 arity)
%            Number of functors    :   65 (   3 constant; 0-10 arity)
%            Number of variables   : 2905 (   7 sgn;2847   !;  58   ?)
%            Maximal term depth    :    5 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
include('Axioms/MPT001+2.ax').
include('Axioms/MPT002+2.ax').
include('Axioms/MPT003+2.ax').
include('Axioms/MPT004+2.ax').
include('Axioms/MPT005+2.ax').
include('Axioms/MPT006+2.ax').
include('Axioms/MPT007+2.ax').
include('Axioms/MPT008+2.ax').
%------------------------------------------------------------------------------
fof(cc1_ordinal1,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) )).

fof(cc2_ordinal1,axiom,(
    ! [A] :
      ( ( v1_ordinal1(A)
        & v2_ordinal1(A) )
     => v3_ordinal1(A) ) )).

fof(d1_ordinal1,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) )).

fof(d2_ordinal1,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) )).

fof(d3_ordinal1,axiom,(
    ! [A] :
      ( v2_ordinal1(A)
    <=> ! [B,C] :
          ~ ( r2_hidden(B,A)
            & r2_hidden(C,A)
            & ~ r2_hidden(B,C)
            & B != C
            & ~ r2_hidden(C,B) ) ) )).

fof(dt_k1_ordinal1,axiom,(
    $true )).

fof(dt_o_2_0_ordinal1,axiom,(
    ! [A,B] :
      ( ( v1_ordinal1(A)
        & v3_ordinal1(B) )
     => m1_subset_1(o_2_0_ordinal1(A,B),k6_subset_1(B,A)) ) )).

fof(fc14_funct_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => v4_funct_1(k1_tarski(A)) ) )).

fof(fc1_ordinal1,axiom,(
    ! [A] : ~ v1_xboole_0(k1_ordinal1(A)) )).

fof(rc1_ordinal1,axiom,(
    ? [A] : v3_ordinal1(A) )).

fof(t10_ordinal1,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) )).

fof(t12_ordinal1,axiom,(
    ! [A,B] :
      ( k1_ordinal1(A) = k1_ordinal1(B)
     => A = B ) )).

fof(t13_ordinal1,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) )).

fof(t14_ordinal1,axiom,(
    ! [A] : A != k1_ordinal1(A) )).

fof(t19_ordinal1,axiom,(
    ! [A,B,C] :
      ( v1_ordinal1(C)
     => ( ( r2_hidden(A,B)
          & r2_hidden(B,C) )
       => r2_hidden(A,C) ) ) )).

fof(t21_ordinal1,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) )).

fof(t22_ordinal1,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ! [C] :
              ( v3_ordinal1(C)
             => ( ( r1_tarski(A,B)
                  & r2_hidden(B,C) )
               => r2_hidden(A,C) ) ) ) ) )).

fof(t23_ordinal1,conjecture,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) )).

fof(t3_ordinal1,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,A) ) )).

fof(t4_ordinal1,axiom,(
    ! [A,B,C,D] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,D)
        & r2_hidden(D,A) ) )).

fof(t5_ordinal1,axiom,(
    ! [A,B,C,D,E] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,D)
        & r2_hidden(D,E)
        & r2_hidden(E,A) ) )).

fof(t6_ordinal1,axiom,(
    ! [A,B,C,D,E,F] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,D)
        & r2_hidden(D,E)
        & r2_hidden(E,F)
        & r2_hidden(F,A) ) )).

fof(t7_ordinal1,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) )).

%------------------------------------------------------------------------------

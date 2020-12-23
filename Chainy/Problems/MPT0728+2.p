%------------------------------------------------------------------------------
% File     : MPT0728+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : ordinal1__t10_ordinal1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 1063 ( 302 unit)
%            Number of atoms       : 3092 ( 885 equality)
%            Maximal formula depth :   26 (   6 average)
%            Number of connectives : 2439 ( 410   ~;  29   |; 765   &)
%                                         ( 182 <=>;1053  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   29 (   1 propositional; 0-2 arity)
%            Number of functors    :   64 (   3 constant; 0-10 arity)
%            Number of variables   : 2880 (   7 sgn;2823   !;  57   ?)
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
fof(d1_ordinal1,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) )).

fof(dt_k1_ordinal1,axiom,(
    $true )).

fof(fc14_funct_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => v4_funct_1(k1_tarski(A)) ) )).

fof(fc1_ordinal1,axiom,(
    ! [A] : ~ v1_xboole_0(k1_ordinal1(A)) )).

fof(t10_ordinal1,conjecture,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) )).

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

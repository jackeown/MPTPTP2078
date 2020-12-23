%------------------------------------------------------------------------------
% File     : MPT1089+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : finset_1__t17_finset_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 1720 ( 373 unit)
%            Number of atoms       : 6502 (1554 equality)
%            Maximal formula depth :   27 (   7 average)
%            Number of connectives : 5714 ( 932   ~; 106   |;2153   &)
%                                         ( 320 <=>;2203  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   64 (   1 propositional; 0-4 arity)
%            Number of functors    :  124 (   3 constant; 0-10 arity)
%            Number of variables   : 5226 (   9 sgn;5034   !; 192   ?)
%            Maximal term depth    :    6 (   1 average)
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
include('Axioms/MPT009+2.ax').
include('Axioms/MPT010+2.ax').
include('Axioms/MPT011+2.ax').
include('Axioms/MPT012+2.ax').
include('Axioms/MPT013+2.ax').
include('Axioms/MPT014+2.ax').
%------------------------------------------------------------------------------
fof(cc1_finset_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_finset_1(A) ) )).

fof(cc2_finset_1,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_finset_1(B) ) ) )).

fof(cc2_ordinal2,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => v3_ordinal1(B) ) ) )).

fof(fc10_finset_1,axiom,(
    ! [A,B] :
      ( v1_finset_1(B)
     => v1_finset_1(k3_xboole_0(A,B)) ) )).

fof(fc11_finset_1,axiom,(
    ! [A,B] :
      ( v1_finset_1(A)
     => v1_finset_1(k3_xboole_0(A,B)) ) )).

fof(fc12_finset_1,axiom,(
    ! [A,B] :
      ( v1_finset_1(A)
     => v1_finset_1(k4_xboole_0(A,B)) ) )).

fof(fc13_finset_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k9_relat_1(A,B)) ) )).

fof(fc9_finset_1,axiom,(
    ! [A,B] :
      ( ( v1_finset_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k2_xboole_0(A,B)) ) )).

fof(rc1_finset_1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_finset_1(A) ) )).

fof(t13_finset_1,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) )).

fof(t14_finset_1,axiom,(
    ! [A,B] :
      ( ( v1_finset_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k2_xboole_0(A,B)) ) )).

fof(t15_finset_1,axiom,(
    ! [A,B] :
      ( v1_finset_1(A)
     => v1_finset_1(k3_xboole_0(A,B)) ) )).

fof(t16_finset_1,axiom,(
    ! [A,B] :
      ( v1_finset_1(A)
     => v1_finset_1(k6_subset_1(A,B)) ) )).

fof(t17_finset_1,conjecture,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_finset_1(A)
       => v1_finset_1(k9_relat_1(B,A)) ) ) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT1914+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow_6__t12_yellow_6.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 3837 ( 452 unit)
%            Number of atoms       : 22540 (2635 equality)
%            Maximal formula depth :   35 (   8 average)
%            Number of connectives : 22178 (3475   ~; 158   |;9836   &)
%                                         ( 833 <=>;7876  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  264 (   1 propositional; 0-6 arity)
%            Number of functors    :  346 (   9 constant; 0-10 arity)
%            Number of variables   : 11241 (   9 sgn;10694   !; 547   ?)
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
include('Axioms/MPT015+2.ax').
include('Axioms/MPT016+2.ax').
include('Axioms/MPT017+2.ax').
include('Axioms/MPT018+2.ax').
include('Axioms/MPT019+2.ax').
include('Axioms/MPT020+2.ax').
include('Axioms/MPT021+2.ax').
include('Axioms/MPT022+2.ax').
include('Axioms/MPT023+2.ax').
include('Axioms/MPT024+2.ax').
include('Axioms/MPT025+2.ax').
include('Axioms/MPT026+2.ax').
include('Axioms/MPT027+2.ax').
include('Axioms/MPT028+2.ax').
include('Axioms/MPT029+2.ax').
%------------------------------------------------------------------------------
fof(cc1_card_1,axiom,(
    ! [A] :
      ( v1_card_1(A)
     => v3_ordinal1(A) ) )).

fof(cc1_card_3,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_card_3(A) ) ) )).

fof(cc1_classes2,axiom,(
    ! [A] :
      ( v2_classes1(A)
     => v1_classes1(A) ) )).

fof(cc1_yellow_3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_struct_0(A)
       => v1_yellow_3(A) ) ) )).

fof(cc2_card_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_card_1(A) ) )).

fof(cc2_classes2,axiom,(
    ! [A] :
      ( v1_classes2(A)
     => ( v1_ordinal1(A)
        & v2_classes1(A) ) ) )).

fof(cc2_yellow_3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ~ v1_yellow_3(A)
       => ~ v2_struct_0(A) ) ) )).

fof(cc3_card_1,axiom,(
    ! [A] :
      ( v7_ordinal1(A)
     => v1_card_1(A) ) )).

fof(cc3_card_3,axiom,(
    ! [A] :
      ( v3_card_3(A)
     => ( v4_funct_1(A)
        & v2_card_3(A) ) ) )).

fof(cc3_classes2,axiom,(
    ! [A] :
      ( ( v1_ordinal1(A)
        & v2_classes1(A) )
     => v1_classes2(A) ) )).

fof(cc4_card_3,axiom,(
    ! [A] :
      ( ( ~ v1_finset_1(A)
        & v1_card_1(A) )
     => ( v4_ordinal1(A)
        & v1_card_1(A) ) ) )).

fof(cc5_card_1,axiom,(
    ! [A] :
      ( v7_ordinal1(A)
     => v1_finset_1(A) ) )).

fof(cc5_card_3,axiom,(
    ! [A] :
      ( v5_card_3(A)
     => ( ~ v1_finset_1(A)
        & v4_card_3(A) ) ) )).

fof(cc5_pboole,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A) )
         => ( ~ v1_xboole_0(B)
            & v1_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A) ) ) ) )).

fof(cc6_card_1,axiom,(
    ! [A] :
      ( ( v3_ordinal1(A)
        & v1_finset_1(A) )
     => v7_ordinal1(A) ) )).

fof(cc6_card_3,axiom,(
    ! [A] :
      ( ( ~ v1_finset_1(A)
        & v4_card_3(A) )
     => v5_card_3(A) ) )).

fof(cc7_card_1,axiom,(
    ! [A] :
      ( v3_card_1(A,k1_xboole_0)
     => v1_xboole_0(A) ) )).

fof(cc7_card_3,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => v4_card_3(A) ) )).

fof(cc8_card_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v3_card_1(A,k1_xboole_0) ) )).

fof(cc8_card_3,axiom,(
    ! [A] :
      ( v4_card_3(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v4_card_3(B) ) ) )).

fof(cc9_card_3,axiom,(
    ! [A] :
      ( v2_card_3(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v2_card_3(B) ) ) )).

fof(d1_classes1,axiom,(
    ! [A] :
      ( v1_classes1(A)
    <=> ! [B,C] :
          ( ( r2_hidden(B,A)
            & r1_tarski(C,B) )
         => r2_hidden(C,A) ) ) )).

fof(d4_card_3,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => k3_card_3(A) = k3_tarski(k2_relat_1(A)) ) )).

fof(dt_k10_pralg_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v2_pralg_1(B)
        & m1_subset_1(C,A) )
     => l1_struct_0(k10_pralg_1(A,B,C)) ) )).

fof(dt_k1_card_1,axiom,(
    ! [A] : v1_card_1(k1_card_1(A)) )).

fof(dt_k3_card_3,axiom,(
    $true )).

fof(fc10_card_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_finset_1(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_finset_1(k2_zfmisc_1(A,B)) ) )).

fof(fc11_card_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_finset_1(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_finset_1(k2_zfmisc_1(B,A)) ) )).

fof(fc14_card_1,axiom,(
    ! [A,B] :
      ( ( v1_card_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B)
        & v3_card_1(B,A) )
     => v3_card_1(k1_relat_1(B),A) ) )).

fof(fc1_card_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k1_card_1(A))
        & v1_card_1(k1_card_1(A)) ) ) )).

fof(fc2_card_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v1_xboole_0(k1_card_1(A))
        & v1_card_1(k1_card_1(A)) ) ) )).

fof(fc4_card_3,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => v4_funct_1(k4_card_3(A)) ) )).

fof(fc6_card_1,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => ( v1_finset_1(k1_card_1(A))
        & v1_card_1(k1_card_1(A)) ) ) )).

fof(fc7_card_3,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => v3_card_3(k4_card_3(A)) ) )).

fof(fc8_card_1,axiom,(
    ! [A] :
      ( ~ v1_finset_1(A)
     => ( ~ v1_finset_1(k1_card_1(A))
        & v1_card_1(k1_card_1(A)) ) ) )).

fof(fc9_card_1,axiom,(
    ! [A] :
      ( ~ v1_finset_1(A)
     => ~ v1_finset_1(k1_zfmisc_1(A)) ) )).

fof(fc9_yellow_3,axiom,(
    ! [A] :
      ( ( ~ v1_yellow_3(A)
        & l1_orders_2(A) )
     => ~ v1_xboole_0(u1_orders_2(A)) ) )).

fof(projectivity_k1_card_1,axiom,(
    ! [A] : k1_card_1(k1_card_1(A)) = k1_card_1(A) )).

fof(rc1_card_1,axiom,(
    ? [A] : v1_card_1(A) )).

fof(rc1_card_3,axiom,(
    ? [A] :
      ( v1_relat_1(A)
      & v1_funct_1(A)
      & v1_card_3(A) ) )).

fof(rc1_classes2,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_classes2(A) ) )).

fof(rc1_pboole,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A) ) )).

fof(rc2_card_1,axiom,(
    ? [A] :
      ( v1_ordinal1(A)
      & v2_ordinal1(A)
      & v3_ordinal1(A)
      & v1_finset_1(A)
      & v1_card_1(A) ) )).

fof(rc2_classes2,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_classes2(A) )
     => ? [B] :
          ( m1_subset_1(B,A)
          & ~ v1_xboole_0(B) ) ) )).

fof(rc3_card_1,axiom,(
    ? [A] : ~ v1_finset_1(A) )).

fof(rc3_card_3,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v4_funct_1(A)
      & v2_card_3(A) ) )).

fof(rc4_card_1,axiom,(
    ! [A] :
      ( ~ v1_finset_1(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_finset_1(B) ) ) )).

fof(rc4_card_3,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v3_card_3(A) ) )).

fof(rc5_card_1,axiom,(
    ! [A] :
      ( v1_card_1(A)
     => ? [B] : v3_card_1(B,A) ) )).

fof(rc5_card_3,axiom,(
    ? [A] : v5_card_3(A) )).

fof(rc6_card_1,axiom,(
    ! [A] :
      ( v1_card_1(A)
     => ? [B] :
          ( v1_relat_1(B)
          & v1_funct_1(B)
          & v3_card_1(B,A) ) ) )).

fof(rc6_card_3,axiom,(
    ? [A] :
      ( v1_relat_1(A)
      & v1_funct_1(A)
      & ~ v1_finset_1(A) ) )).

fof(rc7_pboole,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ? [C] :
          ( v1_relat_1(C)
          & v4_relat_1(C,B)
          & v5_relat_1(C,A)
          & v1_funct_1(C)
          & v1_partfun1(C,B) ) ) )).

fof(redefinition_k10_pralg_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v2_pralg_1(B)
        & m1_subset_1(C,A) )
     => k10_pralg_1(A,B,C) = k1_funct_1(B,C) ) )).

fof(t10_funct_6,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => r1_tarski(k4_card_3(A),k1_funct_2(k1_relat_1(A),k3_card_3(A))) ) )).

fof(t12_yellow_6,conjecture,(
    ! [A] :
      ( l1_orders_2(A)
     => u1_struct_0(A) = u1_struct_0(k7_lattice3(A)) ) )).

fof(t1_classes2,axiom,(
    ! [A,B] :
      ( ( v1_classes1(A)
        & r2_hidden(B,A) )
     => ( ~ r2_tarski(B,A)
        & r2_hidden(k1_card_1(B),k1_card_1(A)) ) ) )).

fof(t2_classes1,axiom,(
    ! [A] :
      ( v2_classes1(A)
    <=> ( v1_classes1(A)
        & ! [B] :
            ( r2_hidden(B,A)
           => r2_hidden(k9_setfam_1(B),A) )
        & ! [B] :
            ( ( r1_tarski(B,A)
              & r2_hidden(k1_card_1(B),k1_card_1(A)) )
           => r2_hidden(B,A) ) ) ) )).

fof(t5_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_classes2(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( r2_hidden(k1_relat_1(B),A)
              & r1_tarski(k2_relat_1(B),A) )
           => r2_hidden(k4_card_3(B),A) ) ) ) )).

fof(t65_classes2,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(B)
        & v1_classes2(B) )
     => ( r2_hidden(A,B)
       => ( r2_hidden(k9_setfam_1(A),B)
          & r2_hidden(k3_tarski(A),B)
          & r2_hidden(k1_setfam_1(A),B) ) ) ) )).

fof(t67_classes2,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(C)
        & v1_classes2(C) )
     => ( ( r2_hidden(A,C)
          & r2_hidden(B,C) )
       => ( r2_hidden(k2_zfmisc_1(A,B),C)
          & r2_hidden(k1_funct_2(A,B),C) ) ) ) )).

fof(t80_card_2,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => r1_ordinal1(k1_card_1(k2_relat_1(A)),k1_card_1(k1_relat_1(A))) ) )).

fof(t9_yellow_6,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A)
            & v2_pralg_1(B) )
         => ! [C] :
              ( m1_subset_1(C,A)
             => k1_funct_1(k12_pralg_1(A,B),C) = u1_struct_0(k10_pralg_1(A,B,C)) ) ) ) )).

%------------------------------------------------------------------------------

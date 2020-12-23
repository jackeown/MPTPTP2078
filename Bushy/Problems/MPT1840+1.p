%------------------------------------------------------------------------------
% File     : MPT1840+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : tex_2__t4_tex_2.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   57 (  11 unit)
%            Number of atoms       :  151 (   4 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :  128 (  34   ~;   1   |;  52   &)
%                                         (   0 <=>;  41  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   18 (   1 propositional; 0-2 arity)
%            Number of functors    :    3 (   2 constant; 0-1 arity)
%            Number of variables   :   58 (   0 sgn;  42   !;  16   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t4_tex_2,conjecture,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( ( u1_struct_0(A) = u1_struct_0(B)
              & v7_struct_0(A) )
           => v7_struct_0(B) ) ) ) )).

fof(existence_m1_subset_1,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) )).

fof(dt_m1_subset_1,axiom,(
    $true )).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(cc6_funct_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & ~ v3_funct_1(A) )
     => ( ~ v1_zfmisc_1(A)
        & v1_relat_1(A)
        & v1_funct_1(A) ) ) )).

fof(cc9_funct_1,axiom,(
    ! [A] :
      ( v4_funct_1(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ( v1_relat_1(B)
            & v1_funct_1(B) ) ) ) )).

fof(rc2_funct_1,axiom,(
    ? [A] :
      ( v1_relat_1(A)
      & v1_funct_1(A)
      & v2_funct_1(A) ) )).

fof(rc2_relat_1,axiom,(
    ? [A] :
      ( v1_relat_1(A)
      & v2_relat_1(A) ) )).

fof(rc3_funct_1,axiom,(
    ? [A] :
      ( v1_relat_1(A)
      & v2_relat_1(A)
      & v1_funct_1(A) ) )).

fof(rc4_funct_1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_relat_1(A)
      & v2_relat_1(A)
      & v1_funct_1(A) ) )).

fof(rc5_funct_1,axiom,(
    ? [A] :
      ( v1_relat_1(A)
      & v1_funct_1(A)
      & ~ v3_funct_1(A) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) )).

fof(dt_k1_xboole_0,axiom,(
    $true )).

fof(cc2_funct_1,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) )).

fof(cc3_relat_1,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A) )
     => ( v1_relat_1(A)
        & v3_relat_1(A) ) ) )).

fof(cc4_funct_1,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v3_funct_1(A) ) ) )).

fof(cc4_relat_1,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A) )
     => ( v1_relat_1(A)
        & v2_relat_1(A) ) ) )).

fof(cc7_funct_1,axiom,(
    ! [A] :
      ( ( v1_zfmisc_1(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v3_funct_1(A) ) ) )).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) )).

fof(rc1_funct_1,axiom,(
    ? [A] :
      ( v1_relat_1(A)
      & v1_funct_1(A) ) )).

fof(rc1_relat_1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_relat_1(A) ) )).

fof(rc7_funct_1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v4_funct_1(A) ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

fof(cc1_funct_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) )).

fof(cc1_relat_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) )).

fof(cc1_zfmisc_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) )).

fof(cc2_realset1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) )).

fof(cc4_realset1,axiom,(
    ! [A] :
      ( ~ v1_finset_1(A)
     => ~ v1_zfmisc_1(A) ) )).

fof(cc8_funct_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v4_funct_1(A) ) )).

fof(rc1_realset1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_zfmisc_1(A) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : v1_xboole_0(A) )).

fof(rc2_realset1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & ~ v1_zfmisc_1(A) ) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ v1_xboole_0(A) )).

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

fof(cc1_realset1,axiom,(
    ! [A] :
      ( ~ v1_zfmisc_1(A)
     => ~ v1_xboole_0(A) ) )).

fof(cc1_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v2_struct_0(A)
       => v7_struct_0(A) ) ) )).

fof(cc3_realset1,axiom,(
    ! [A] :
      ( v1_zfmisc_1(A)
     => v1_finset_1(A) ) )).

fof(cc4_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v2_struct_0(A)
       => ( v2_struct_0(A)
          & v8_struct_0(A) ) ) ) )).

fof(cc5_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( ~ v8_struct_0(A)
       => ( ~ v2_struct_0(A)
          & ~ v8_struct_0(A) ) ) ) )).

fof(cc7_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( ~ v8_struct_0(A)
       => ~ v7_struct_0(A) ) ) )).

fof(fc1_struct_0,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) )).

fof(fc2_struct_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) )).

fof(fc8_struct_0,axiom,(
    ! [A] :
      ( ( v8_struct_0(A)
        & l1_struct_0(A) )
     => v1_finset_1(u1_struct_0(A)) ) )).

fof(fc9_struct_0,axiom,(
    ! [A] :
      ( ( ~ v8_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_finset_1(u1_struct_0(A)) ) )).

fof(rc10_struct_0,axiom,(
    ? [A] :
      ( l1_struct_0(A)
      & ~ v2_struct_0(A)
      & ~ v7_struct_0(A) ) )).

fof(rc9_struct_0,axiom,(
    ? [A] :
      ( l1_struct_0(A)
      & ~ v2_struct_0(A)
      & v7_struct_0(A) ) )).

fof(existence_l1_struct_0,axiom,(
    ? [A] : l1_struct_0(A) )).

fof(dt_l1_struct_0,axiom,(
    $true )).

fof(dt_u1_struct_0,axiom,(
    $true )).

fof(cc2_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( ~ v7_struct_0(A)
       => ~ v2_struct_0(A) ) ) )).

fof(cc6_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v7_struct_0(A)
       => v8_struct_0(A) ) ) )).

fof(fc6_struct_0,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) )).

fof(fc7_struct_0,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) )).

%------------------------------------------------------------------------------

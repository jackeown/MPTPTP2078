%------------------------------------------------------------------------------
% File     : MPT1782+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : tmap_1__t97_tmap_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   14 (   0 unit)
%            Number of atoms       :   75 (   5 equality)
%            Maximal formula depth :   15 (   8 average)
%            Number of connectives :   72 (  11   ~;   0   |;  38   &)
%                                         (   1 <=>;  22  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   13 (   0 propositional; 1-4 arity)
%            Number of functors    :   10 (   0 constant; 1-6 arity)
%            Number of variables   :   47 (   0 sgn;  47   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d4_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k3_struct_0(A) = k6_partfun1(u1_struct_0(A)) ) )).

fof(d7_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => k4_tmap_1(A,B) = k2_tmap_1(A,A,k3_struct_0(A),B) ) ) )).

fof(dt_k3_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v1_funct_1(k3_struct_0(A))
        & v1_funct_2(k3_struct_0(A),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k3_struct_0(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) )).

fof(dt_k4_relset_1,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) )).

fof(dt_k6_partfun1,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) )).

fof(dt_l1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) )).

fof(fc2_struct_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) )).

fof(fc8_funct_2,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v1_xboole_0(B)
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & v1_funct_2(E,B,C)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k5_relat_1(D,E))
        & v1_funct_2(k5_relat_1(D,E),A,C) ) ) )).

fof(redefinition_k1_partfun1,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) )).

fof(redefinition_k4_relset_1,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) )).

fof(redefinition_r2_relset_1,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) )).

fof(t23_funct_2,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
        & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) )).

fof(t69_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(B),u1_struct_0(C))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(C)))) )
                         => r2_funct_2(u1_struct_0(D),u1_struct_0(C),k2_tmap_1(A,C,k1_partfun1(u1_struct_0(A),u1_struct_0(B),u1_struct_0(B),u1_struct_0(C),E,F),D),k1_partfun1(u1_struct_0(D),u1_struct_0(B),u1_struct_0(B),u1_struct_0(C),k2_tmap_1(A,B,E,D),F)) ) ) ) ) ) ) )).

fof(t97_tmap_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                 => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,D,C),k1_partfun1(u1_struct_0(C),u1_struct_0(A),u1_struct_0(A),u1_struct_0(B),k4_tmap_1(A,C),D)) ) ) ) ) )).

%------------------------------------------------------------------------------

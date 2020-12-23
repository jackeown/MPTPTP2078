%------------------------------------------------------------------------------
% File     : MPT1834+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : tmap_1__t150_tmap_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   12 (   0 unit)
%            Number of atoms       :  147 (   2 equality)
%            Maximal formula depth :   23 (  12 average)
%            Number of connectives :  161 (  26   ~;   0   |;  93   &)
%                                         (   4 <=>;  38  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   14 (   0 propositional; 1-4 arity)
%            Number of functors    :    6 (   0 constant; 1-6 arity)
%            Number of variables   :   46 (   0 sgn;  46   !;   0   ?)
%            Maximal term depth    :    5 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(commutativity_k1_tsep_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => k1_tsep_1(A,B,C) = k1_tsep_1(A,C,B) ) )).

fof(dt_k10_tmap_1,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A)
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
        & v1_funct_1(F)
        & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
     => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
        & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) )).

fof(dt_l1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) )).

fof(dt_m1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) )).

fof(redefinition_r2_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) )).

fof(symmetry_r1_tsep_1,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) )).

fof(symmetry_r3_tsep_1,axiom,(
    ! [A,B,C] :
      ( ( l1_pre_topc(A)
        & m1_pre_topc(B,A)
        & m1_pre_topc(C,A) )
     => ( r3_tsep_1(A,B,C)
       => r3_tsep_1(A,C,B) ) ) )).

fof(t135_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r3_tsep_1(A,B,C)
              <=> ( r1_tsep_1(B,C)
                  & ! [D] :
                      ( ( ~ v2_struct_0(D)
                        & v2_pre_topc(D)
                        & l1_pre_topc(D) )
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) )
                         => ( ( v1_funct_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E))
                              & v1_funct_2(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),u1_struct_0(B),u1_struct_0(D))
                              & v5_pre_topc(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),B,D)
                              & m1_subset_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(D))))
                              & v1_funct_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E))
                              & v1_funct_2(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),u1_struct_0(C),u1_struct_0(D))
                              & v5_pre_topc(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),C,D)
                              & m1_subset_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                           => ( v1_funct_1(E)
                              & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                              & v5_pre_topc(E,k1_tsep_1(A,B,C),D)
                              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) ) ) ) ) ) ) ) ) ) )).

fof(t138_tmap_1,axiom,(
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
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B),E,k10_tmap_1(A,B,C,D,k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E))) ) ) ) ) ) )).

fof(t145_tmap_1,axiom,(
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
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( r1_tsep_1(C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & v5_pre_topc(E,C,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                              & v5_pre_topc(F,D,B)
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                           => ( r4_tsep_1(A,C,D)
                             => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),k1_tsep_1(A,C,D),B)
                                & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) )).

fof(t85_tsep_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ( r1_tsep_1(B,C)
                  & r4_tsep_1(A,B,C) )
              <=> r3_tsep_1(A,B,C) ) ) ) ) )).

fof(t150_tmap_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r3_tsep_1(A,B,C)
              <=> ( r1_tsep_1(B,C)
                  & ! [D] :
                      ( ( ~ v2_struct_0(D)
                        & v2_pre_topc(D)
                        & l1_pre_topc(D) )
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(B),u1_struct_0(D))
                            & v5_pre_topc(E,B,D)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(D)))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(D))
                                & v5_pre_topc(F,C,D)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                             => ( v1_funct_1(k10_tmap_1(A,D,B,C,E,F))
                                & v1_funct_2(k10_tmap_1(A,D,B,C,E,F),u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                                & v5_pre_topc(k10_tmap_1(A,D,B,C,E,F),k1_tsep_1(A,B,C),D)
                                & m1_subset_1(k10_tmap_1(A,D,B,C,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) ) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

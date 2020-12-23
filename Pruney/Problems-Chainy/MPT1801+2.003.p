%------------------------------------------------------------------------------
% File     : MPT1801+2.003 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 003 of t117_tmap_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   0 unit)
%            Number of atoms       :   42 (   6 equality)
%            Maximal formula depth :   11 (   6 average)
%            Number of connectives :   40 (   6   ~;   0   |;  17   &)
%                                         (   1 <=>;  16  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-6 arity)
%            Number of functors    :   11 (   0 constant; 1-2 arity)
%            Number of variables   :   16 (   0 sgn;  16   !;   0   ?)
%            Maximal term depth    :    5 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(dt_l1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) )).

fof(d10_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_tmap_1(A,B) = k6_partfun1(u1_struct_0(A)) ) ) )).

fof(d12_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) )
             => ( C = k9_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => r1_funct_2(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,D)),C,k7_tmap_1(A,D)) ) ) ) ) ) ) )).

fof(d4_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k3_struct_0(A) = k6_partfun1(u1_struct_0(A)) ) )).

fof(dt_k9_tmap_1,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k9_tmap_1(A,B))
        & v1_funct_2(k9_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
        & m1_subset_1(k9_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) ) ) )).

fof(t104_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) )).

fof(t1_tsep_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) )).

fof(t117_tmap_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => r1_funct_2(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)),u1_struct_0(A),u1_struct_0(A),k9_tmap_1(A,B),k3_struct_0(A)) ) ) )).

%------------------------------------------------------------------------------

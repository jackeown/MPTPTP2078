%------------------------------------------------------------------------------
% File     : MPT1370+2.003 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 003 of t25_compts_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   11 (   2 unit)
%            Number of atoms       :   53 (   4 equality)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :   44 (   2   ~;   0   |;  18   &)
%                                         (   2 <=>;  22  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   14 (   0 propositional; 1-3 arity)
%            Number of functors    :    7 (   0 constant; 1-4 arity)
%            Number of variables   :   24 (   0 sgn;  24   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d4_subset_1,axiom,(
    ! [A] : k2_subset_1(A) = A )).

fof(dt_k2_subset_1,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(dt_k7_relset_1,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) )).

fof(d3_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) )).

fof(dt_l1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) )).

fof(t10_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> v2_compts_1(k2_struct_0(A),A) ) ) )).

fof(t16_compts_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) )).

fof(t18_compts_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) )).

fof(t24_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & l1_pre_topc(C) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(C)))) )
                 => ( ( v5_pre_topc(D,A,C)
                      & k2_relset_1(u1_struct_0(A),u1_struct_0(C),D) = k2_struct_0(C)
                      & v2_compts_1(B,A) )
                   => v2_compts_1(k7_relset_1(u1_struct_0(A),u1_struct_0(C),D,B),C) ) ) ) ) ) )).

fof(t25_compts_1,conjecture,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( v1_compts_1(A)
                  & v8_pre_topc(B)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v5_pre_topc(C,A,B) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( v4_pre_topc(D,A)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),B) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

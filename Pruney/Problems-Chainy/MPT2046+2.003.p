%------------------------------------------------------------------------------
% File     : MPT2046+2.003 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 003 of t5_yellow19
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   26 (   0 equality)
%            Maximal formula depth :   10 (   8 average)
%            Number of connectives :   25 (   3   ~;   0   |;   9   &)
%                                         (   2 <=>;  11  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    8 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :   12 (   0 sgn;  12   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t5_connsp_2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) )).

fof(d5_waybel_7,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( r2_waybel_7(A,B,C)
        <=> ! [D] :
              ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(D,A)
                  & r2_hidden(C,D) )
               => r2_hidden(D,B) ) ) ) ) )).

fof(t3_yellow19,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r2_hidden(C,k1_yellow19(A,B))
            <=> m1_connsp_2(C,A,B) ) ) ) )).

fof(t5_yellow19,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_waybel_7(A,k1_yellow19(A,B),B) ) ) )).

%------------------------------------------------------------------------------

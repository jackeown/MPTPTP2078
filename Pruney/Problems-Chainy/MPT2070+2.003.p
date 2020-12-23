%------------------------------------------------------------------------------
% File     : MPT2070+2.003 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 003 of t30_yellow19
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   54 (   0 equality)
%            Maximal formula depth :   15 (  14 average)
%            Number of connectives :   58 (   8   ~;   0   |;  28   &)
%                                         (   4 <=>;  18  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   13 (   0 propositional; 1-3 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :   16 (   0 sgn;  14   !;   2   ?)
%            Maximal term depth    :    5 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t27_yellow19,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ? [D] :
                    ( ~ v1_xboole_0(D)
                    & v1_subset_1(D,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
                    & v2_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))
                    & r2_hidden(B,D)
                    & r1_waybel_7(A,D,C) ) ) ) ) ) )).

fof(t28_yellow19,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ? [D] :
                    ( ~ v1_xboole_0(D)
                    & v2_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v3_waybel_7(D,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))
                    & r2_hidden(B,D)
                    & r2_waybel_7(A,D,C) ) ) ) ) ) )).

fof(t29_yellow19,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & v1_subset_1(C,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
                  & v2_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                  & v13_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
               => ( r2_hidden(B,C)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_waybel_7(A,C,D)
                       => r2_hidden(D,B) ) ) ) ) ) ) ) )).

fof(t30_yellow19,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & v2_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                  & v13_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                  & v3_waybel_7(C,k3_yellow_1(k2_struct_0(A)))
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
               => ( r2_hidden(B,C)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_waybel_7(A,C,D)
                       => r2_hidden(D,B) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT1984+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t33_waybel_7
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    7 (   0 unit)
%            Number of atoms       :   63 (   0 equality)
%            Maximal formula depth :   16 (   9 average)
%            Number of connectives :   71 (  15   ~;   0   |;  37   &)
%                                         (   2 <=>;  17  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   18 (   0 propositional; 1-3 arity)
%            Number of functors    :    5 (   0 constant; 1-1 arity)
%            Number of variables   :   19 (   0 sgn;  19   !;   0   ?)
%            Maximal term depth    :    5 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) )).

fof(dt_k3_yellow_1,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & l1_orders_2(k3_yellow_1(A)) ) )).

fof(fc7_yellow_1,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) )).

fof(cc1_waybel_7,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & v3_waybel_7(B,A) )
           => ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(A))
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A) ) ) ) ) )).

fof(t31_waybel_7,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(u1_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(u1_struct_0(A)))
            & v3_waybel_7(B,k3_yellow_1(u1_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A))))) )
         => ! [C] :
              ( r1_waybel_7(A,B,C)
            <=> r2_waybel_7(A,B,C) ) ) ) )).

fof(t32_waybel_7,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(u1_pre_topc(A))))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(u1_pre_topc(A))))
             => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(A)),B,C)
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & v1_subset_1(D,u1_struct_0(k3_yellow_1(u1_struct_0(A))))
                      & v2_waybel_0(D,k3_yellow_1(u1_struct_0(A)))
                      & v13_waybel_0(D,k3_yellow_1(u1_struct_0(A)))
                      & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A))))) )
                   => ~ ( r2_hidden(B,D)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ~ ( r2_hidden(E,C)
                                & r1_waybel_7(A,D,E) ) ) ) ) ) ) ) ) )).

fof(t33_waybel_7,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(u1_pre_topc(A))))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(u1_pre_topc(A))))
             => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(A)),B,C)
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & v2_waybel_0(D,k3_yellow_1(u1_struct_0(A)))
                      & v13_waybel_0(D,k3_yellow_1(u1_struct_0(A)))
                      & v3_waybel_7(D,k3_yellow_1(u1_struct_0(A)))
                      & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(A))))) )
                   => ~ ( r2_hidden(B,D)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ~ ( r2_hidden(E,C)
                                & r2_waybel_7(A,D,E) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

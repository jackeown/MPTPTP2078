%------------------------------------------------------------------------------
% File     : MPT2042+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_9__t41_waybel_9---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :   48 (   0 equality)
%            Maximal formula depth :   11 (  11 average)
%            Number of connectives :   47 (   2   ~;   0   |;  32   &)
%                                         (   0 <=>;  13  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   18 (   0 propositional; 1-3 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :    8 (   0 sgn;   8   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments : 
%------------------------------------------------------------------------------
fof(t37_waybel_9,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & v8_pre_topc(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_waybel_9(A) )
     => ( ( ! [B] :
              ( ( ~ v2_struct_0(B)
                & v4_orders_2(B)
                & v7_waybel_0(B)
                & l1_waybel_0(B,A) )
             => ( v10_waybel_0(B,A)
               => ( r1_waybel_9(A,B)
                  & r2_hidden(k1_waybel_2(A,B),k10_yellow_6(A,B)) ) ) )
          & ! [B] :
              ( m1_subset_1(B,u1_struct_0(A))
             => v5_pre_topc(k4_waybel_1(A,B),A,A) ) )
       => v2_waybel_2(A) ) ) )).

fof(t38_waybel_9,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & v8_pre_topc(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v1_compts_1(A)
        & l1_waybel_9(A) )
     => ( ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v5_pre_topc(k4_waybel_1(A,B),A,A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => ( v10_waybel_0(B,A)
             => ( r1_waybel_9(A,B)
                & r2_hidden(k1_waybel_2(A,B),k10_yellow_6(A,B)) ) ) ) ) ) )).

fof(t41_waybel_9,conjecture,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & v8_pre_topc(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v1_compts_1(A)
        & l1_waybel_9(A) )
     => ( ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v5_pre_topc(k4_waybel_1(A,B),A,A) )
       => v2_waybel_2(A) ) ) )).

%------------------------------------------------------------------------------

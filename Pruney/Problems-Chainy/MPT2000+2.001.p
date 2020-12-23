%------------------------------------------------------------------------------
% File     : MPT2000+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t49_waybel_7
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :   44 (   0 equality)
%            Maximal formula depth :   16 (  14 average)
%            Number of connectives :   49 (   8   ~;   0   |;  27   &)
%                                         (   1 <=>;  13  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   14 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   0 constant; 1-3 arity)
%            Number of variables   :   10 (   0 sgn;  10   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(l57_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_waybel_3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v5_waybel_7(k1_waybel_4(A),A)
              & ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ~ ( r1_waybel_3(A,k12_lattice3(A,C,D),B)
                          & ~ r3_orders_2(A,C,B)
                          & ~ r3_orders_2(A,D,B) ) ) )
              & ~ v5_waybel_6(B,A) ) ) ) )).

fof(t48_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_waybel_3(A)
        & l1_orders_2(A) )
     => ( v5_waybel_7(k1_waybel_4(A),A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v4_waybel_7(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ~ ( r1_waybel_3(A,k12_lattice3(A,C,D),B)
                          & ~ r3_orders_2(A,C,B)
                          & ~ r3_orders_2(A,D,B) ) ) ) ) ) ) ) )).

fof(t49_waybel_7,conjecture,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_waybel_3(A)
        & l1_orders_2(A) )
     => ( v5_waybel_7(k1_waybel_4(A),A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v4_waybel_7(B,A)
             => v5_waybel_6(B,A) ) ) ) ) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT2011+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t10_waybel_9
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   0 unit)
%            Number of atoms       :   55 (   4 equality)
%            Maximal formula depth :   16 (   9 average)
%            Number of connectives :   60 (  13   ~;   0   |;  30   &)
%                                         (   2 <=>;  15  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    9 (   0 propositional; 1-2 arity)
%            Number of functors    :    7 (   0 constant; 1-3 arity)
%            Number of variables   :   22 (   0 sgn;  21   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(dt_l1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) )).

fof(dt_l1_waybel_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) )).

fof(l16_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ( v4_orders_2(A)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(A),u1_orders_2(A))) ) ) )).

fof(d3_waybel_2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & l1_waybel_0(C,A) )
             => ! [D] :
                  ( ( v6_waybel_0(D,A)
                    & l1_waybel_0(D,A) )
                 => ( D = k3_waybel_2(A,B,C)
                  <=> ( g1_orders_2(u1_struct_0(D),u1_orders_2(D)) = g1_orders_2(u1_struct_0(C),u1_orders_2(C))
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(D))
                         => ? [F] :
                              ( m1_subset_1(F,u1_struct_0(A))
                              & F = k1_funct_1(u1_waybel_0(A,C),E)
                              & k1_funct_1(u1_waybel_0(A,D),E) = k11_lattice3(A,B,F) ) ) ) ) ) ) ) ) )).

fof(dt_k3_waybel_2,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,A) )
     => ( v6_waybel_0(k3_waybel_2(A,B,C),A)
        & l1_waybel_0(k3_waybel_2(A,B,C),A) ) ) )).

fof(fc5_waybel_2,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,A) )
     => ( ~ v2_struct_0(k3_waybel_2(A,B,C))
        & v6_waybel_0(k3_waybel_2(A,B,C),A) ) ) )).

fof(fc6_waybel_2,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & ~ v2_struct_0(C)
        & v7_waybel_0(C)
        & l1_waybel_0(C,A) )
     => ( v6_waybel_0(k3_waybel_2(A,B,C),A)
        & v7_waybel_0(k3_waybel_2(A,B,C)) ) ) )).

fof(t10_waybel_9,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v4_orders_2(C)
                & v7_waybel_0(C)
                & l1_waybel_0(C,A) )
             => ( ~ v2_struct_0(k3_waybel_2(A,B,C))
                & v4_orders_2(k3_waybel_2(A,B,C))
                & v7_waybel_0(k3_waybel_2(A,B,C))
                & l1_waybel_0(k3_waybel_2(A,B,C),A) ) ) ) ) )).

%------------------------------------------------------------------------------

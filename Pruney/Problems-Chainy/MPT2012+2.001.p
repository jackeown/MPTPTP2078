%------------------------------------------------------------------------------
% File     : MPT2012+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t11_waybel_9
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    6 (   0 unit)
%            Number of atoms       :   20 (   7 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   14 (   0   ~;   0   |;   5   &)
%                                         (   1 <=>;   8  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    8 (   0 constant; 1-3 arity)
%            Number of variables   :    7 (   0 sgn;   7   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(abstractness_v1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) )).

fof(d5_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(A) = g1_orders_2(u1_struct_0(A),k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))) ) )).

fof(dt_k7_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(k7_lattice3(A))
        & l1_orders_2(k7_lattice3(A)) ) ) )).

fof(d6_waybel_9,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v6_waybel_0(B,A)
            & l1_waybel_0(B,A) )
         => ( B = k3_waybel_9(A)
          <=> ( u1_struct_0(B) = u1_struct_0(A)
              & u1_orders_2(B) = k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))
              & u1_waybel_0(A,B) = k3_struct_0(A) ) ) ) ) )).

fof(dt_k3_waybel_9,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v6_waybel_0(k3_waybel_9(A),A)
        & l1_waybel_0(k3_waybel_9(A),A) ) ) )).

fof(t11_waybel_9,conjecture,(
    ! [A] :
      ( l1_orders_2(A)
     => g1_orders_2(u1_struct_0(k7_lattice3(A)),u1_orders_2(k7_lattice3(A))) = g1_orders_2(u1_struct_0(k3_waybel_9(A)),u1_orders_2(k3_waybel_9(A))) ) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT1609+2.003 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 003 of t17_yellow_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   17 (   3 unit)
%            Number of atoms       :   59 (  11 equality)
%            Maximal formula depth :    9 (   5 average)
%            Number of connectives :   48 (   6   ~;   0   |;  26   &)
%                                         (   1 <=>;  15  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   15 (   0 propositional; 1-2 arity)
%            Number of functors    :   16 (   0 constant; 1-3 arity)
%            Number of variables   :   31 (   0 sgn;  31   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) )).

fof(t12_setfam_1,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) )).

fof(dt_k1_lattice3,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & l3_lattices(k1_lattice3(A)) ) )).

fof(fc1_lattice3,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k1_lattice3(A))
      & v3_lattices(k1_lattice3(A)) ) )).

fof(fc2_lattice3,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & v10_lattices(k1_lattice3(A)) ) )).

fof(redefinition_k12_lattice3,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) )).

fof(redefinition_k13_lattice3,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) )).

fof(d2_yellow_1,axiom,(
    ! [A] : k3_yellow_1(A) = k3_lattice3(k1_lattice3(A)) )).

fof(dt_k3_yellow_1,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & l1_orders_2(k3_yellow_1(A)) ) )).

fof(fc1_yellow_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( v1_orders_2(k3_lattice3(A))
        & v3_orders_2(k3_lattice3(A))
        & v4_orders_2(k3_lattice3(A))
        & v5_orders_2(k3_lattice3(A))
        & v1_lattice3(k3_lattice3(A))
        & v2_lattice3(k3_lattice3(A)) ) ) )).

fof(fc7_yellow_1,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) )).

fof(l19_yellow_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
         => ( r2_hidden(k3_xboole_0(B,C),k9_setfam_1(A))
            & r2_hidden(k2_xboole_0(B,C),k9_setfam_1(A)) ) ) ) )).

fof(t1_yellow_1,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) )).

fof(t4_yellow_1,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) )).

fof(t8_yellow_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r2_hidden(k2_xboole_0(B,C),A)
               => k10_lattice3(k2_yellow_1(A),B,C) = k2_xboole_0(B,C) ) ) ) ) )).

fof(t9_yellow_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r2_hidden(k3_xboole_0(B,C),A)
               => k11_lattice3(k2_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ) )).

fof(t17_yellow_1,conjecture,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
         => ( k13_lattice3(k3_yellow_1(A),B,C) = k2_xboole_0(B,C)
            & k12_lattice3(k3_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) )).

%------------------------------------------------------------------------------

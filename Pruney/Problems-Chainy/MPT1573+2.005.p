%------------------------------------------------------------------------------
% File     : MPT1573+2.005 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 005 of t51_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    6 (   1 unit)
%            Number of atoms       :   37 (   3 equality)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   34 (   3   ~;   1   |;  10   &)
%                                         (   1 <=>;  19  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    9 (   0 propositional; 1-3 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :   15 (   0 sgn;  15   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) )).

fof(d9_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) )).

fof(dt_k1_yellow_0,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) )).

fof(t50_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( r1_yellow_0(A,B)
           => r1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
          & ( r1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A)))
           => r1_yellow_0(A,B) )
          & ( r2_yellow_0(A,B)
           => r2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
          & ( r2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A)))
           => r2_yellow_0(A,B) ) ) ) )).

fof(t5_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( ( r2_lattice3(A,B,C)
             => r2_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C) )
            & ( r2_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C)
             => r2_lattice3(A,B,C) )
            & ( r1_lattice3(A,B,C)
             => r1_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C) )
            & ( r1_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C)
             => r1_lattice3(A,B,C) ) ) ) ) )).

fof(t51_yellow_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( r1_yellow_0(A,B)
            | r1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
         => k1_yellow_0(A,B) = k1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) ) ) )).

%------------------------------------------------------------------------------

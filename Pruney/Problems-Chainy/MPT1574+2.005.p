%------------------------------------------------------------------------------
% File     : MPT1574+2.005 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 005 of t52_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :   23 (   2 equality)
%            Maximal formula depth :   10 (   9 average)
%            Number of connectives :   23 (   3   ~;   1   |;   7   &)
%                                         (   1 <=>;  11  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :    9 (   0 sgn;   9   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t49_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( ( r2_yellow_0(A,B)
            & ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r1_lattice3(A,B,D)
                <=> r1_lattice3(A,C,D) ) ) )
         => k2_yellow_0(A,B) = k2_yellow_0(A,C) ) ) )).

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

fof(t52_yellow_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( r2_yellow_0(A,B)
            | r2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
         => k2_yellow_0(A,B) = k2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) ) ) )).

%------------------------------------------------------------------------------

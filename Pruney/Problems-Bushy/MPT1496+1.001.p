%------------------------------------------------------------------------------
% File     : MPT1496+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : lattice3__t29_lattice3---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   27 (   2 equality)
%            Maximal formula depth :    7 (   6 average)
%            Number of connectives :   27 (   5   ~;   0   |;  11   &)
%                                         (   2 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-3 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :   12 (   0 sgn;  12   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d3_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattice3(A,B) = B ) ) )).

fof(d4_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k3_lattice3(A)))
         => k5_lattice3(A,B) = B ) ) )).

fof(dt_k5_lattice3,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(k3_lattice3(A))) )
     => m1_subset_1(k5_lattice3(A,B),u1_struct_0(A)) ) )).

fof(t28_lattice3,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & l3_lattices(B) )
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(B))
         => ( r3_lattice3(B,C,A)
          <=> r1_lattice3(k3_lattice3(B),A,k4_lattice3(B,C)) ) ) ) )).

fof(t29_lattice3,conjecture,(
    ! [A,B] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & l3_lattices(B) )
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k3_lattice3(B)))
         => ( r1_lattice3(k3_lattice3(B),A,C)
          <=> r3_lattice3(B,k5_lattice3(B,C),A) ) ) ) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT1518+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t52_lattice3
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   0 unit)
%            Number of atoms       :   76 (   4 equality)
%            Maximal formula depth :   15 (  11 average)
%            Number of connectives :   79 (  11   ~;   0   |;  41   &)
%                                         (   4 <=>;  23  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   17 (   0 propositional; 1-3 arity)
%            Number of functors    :    5 (   0 constant; 1-3 arity)
%            Number of variables   :   27 (   0 sgn;  26   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(cc1_lattices,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) )).

fof(redefinition_r3_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_lattices(A,B,C)
      <=> r1_lattices(A,B,C) ) ) )).

fof(d8_filter_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( ~ v2_struct_0(A)
                  & v10_lattices(A)
                  & v3_filter_0(A)
                  & l3_lattices(A) )
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( D = k4_filter_0(A,B,C)
                    <=> ( r3_lattices(A,k4_lattices(A,B,D),C)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ( r3_lattices(A,k4_lattices(A,B,E),C)
                             => r3_lattices(A,E,D) ) ) ) ) ) ) ) ) ) )).

fof(dt_k4_filter_0,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_filter_0(A,B,C),u1_struct_0(A)) ) )).

fof(d17_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r4_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,D,B) ) ) ) ) ) )).

fof(fraenkel_a_3_6_lattice3,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B)
        & m1_subset_1(C,u1_struct_0(B))
        & m1_subset_1(D,u1_struct_0(B)) )
     => ( r2_hidden(A,a_3_6_lattice3(B,C,D))
      <=> ? [E] :
            ( m1_subset_1(E,u1_struct_0(B))
            & A = E
            & r3_lattices(B,k4_lattices(B,C,E),D) ) ) ) )).

fof(t41_lattice3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( r2_hidden(B,C)
                & r4_lattice3(A,B,C) )
             => k15_lattice3(A,C) = B ) ) ) )).

fof(t52_lattice3,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( ~ v2_struct_0(A)
                  & v10_lattices(A)
                  & v3_filter_0(A)
                  & l3_lattices(A) )
               => k4_filter_0(A,B,C) = k15_lattice3(A,a_3_6_lattice3(A,B,C)) ) ) ) ) )).

%------------------------------------------------------------------------------

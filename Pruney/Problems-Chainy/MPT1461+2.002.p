%------------------------------------------------------------------------------
% File     : MPT1461+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t56_filter_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   12 (   0 unit)
%            Number of atoms       :   93 (   4 equality)
%            Maximal formula depth :   15 (  10 average)
%            Number of connectives :   94 (  13   ~;   0   |;  47   &)
%                                         (   1 <=>;  33  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   15 (   0 propositional; 1-3 arity)
%            Number of functors    :    4 (   0 constant; 1-3 arity)
%            Number of variables   :   38 (   0 sgn;  38   !;   0   ?)
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

fof(commutativity_k3_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) )).

fof(commutativity_k4_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) )).

fof(dt_k3_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_lattices(A,B,C),u1_struct_0(A)) ) )).

fof(dt_k4_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_lattices(A,B,C),u1_struct_0(A)) ) )).

fof(dt_l3_lattices,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) )).

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

fof(t17_filter_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v3_filter_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => k4_filter_0(A,k4_lattices(A,B,C),D) = k4_filter_0(A,B,k4_filter_0(A,C,D)) ) ) ) ) )).

fof(t2_filter_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r3_lattices(A,B,C)
                   => r3_lattices(A,k4_lattices(A,B,D),C) ) ) ) ) ) )).

fof(t3_filter_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r3_lattices(A,B,C)
                   => r3_lattices(A,B,k3_lattices(A,D,C)) ) ) ) ) ) )).

fof(t56_filter_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v3_filter_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r3_lattices(A,k4_filter_0(A,B,C),k4_filter_0(A,B,k3_lattices(A,C,D)))
                    & r3_lattices(A,k4_filter_0(A,B,C),k4_filter_0(A,k4_lattices(A,B,D),C))
                    & r3_lattices(A,k4_filter_0(A,B,C),k4_filter_0(A,B,k3_lattices(A,D,C)))
                    & r3_lattices(A,k4_filter_0(A,B,C),k4_filter_0(A,k4_lattices(A,D,B),C)) ) ) ) ) ) )).

%------------------------------------------------------------------------------

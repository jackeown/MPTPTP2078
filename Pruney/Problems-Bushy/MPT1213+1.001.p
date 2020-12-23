%------------------------------------------------------------------------------
% File     : MPT1213+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : lattices__t49_lattices---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   37 (   6 equality)
%            Maximal formula depth :   11 (   8 average)
%            Number of connectives :   39 (   7   ~;   0   |;  18   &)
%                                         (   2 <=>;  12  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :    6 (   0 constant; 1-3 arity)
%            Number of variables   :   11 (   0 sgn;  11   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(cc5_lattices,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v17_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v11_lattices(A)
          & v15_lattices(A)
          & v16_lattices(A) ) ) ) )).

fof(d18_lattices,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_lattices(A,B,C)
              <=> ( k1_lattices(A,B,C) = k6_lattices(A)
                  & k1_lattices(A,C,B) = k6_lattices(A)
                  & k2_lattices(A,B,C) = k5_lattices(A)
                  & k2_lattices(A,C,B) = k5_lattices(A) ) ) ) ) ) )).

fof(d21_lattices,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( ( ~ v2_struct_0(A)
              & v10_lattices(A)
              & v11_lattices(A)
              & v16_lattices(A)
              & l3_lattices(A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( C = k7_lattices(A,B)
                <=> r2_lattices(A,C,B) ) ) ) ) ) )).

fof(dt_k7_lattices,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) )).

fof(t49_lattices,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v17_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k7_lattices(A,k7_lattices(A,B)) = B ) ) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT1101+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : pre_topc__t18_pre_topc---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    4 (   1 unit)
%            Number of atoms       :    8 (   4 equality)
%            Maximal formula depth :    5 (   4 average)
%            Number of connectives :    4 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    6 (   0 constant; 1-3 arity)
%            Number of variables   :    6 (   0 sgn;   6   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d3_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) )).

fof(d4_subset_1,axiom,(
    ! [A] : k2_subset_1(A) = A )).

fof(t25_subset_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) )).

fof(t18_pre_topc,conjecture,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) )).

%------------------------------------------------------------------------------

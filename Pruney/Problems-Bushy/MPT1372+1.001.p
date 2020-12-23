%------------------------------------------------------------------------------
% File     : MPT1372+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : compts_1__t27_compts_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   14 (   0 equality)
%            Maximal formula depth :    5 (   4 average)
%            Number of connectives :   12 (   2   ~;   0   |;   4   &)
%                                         (   0 <=>;   6  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-1 arity)
%            Number of functors    :    1 (   0 constant; 1-1 arity)
%            Number of variables   :    4 (   0 sgn;   4   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments : 
%------------------------------------------------------------------------------
fof(cc3_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( v8_struct_0(A)
          & v2_pre_topc(A) )
       => ( v2_pre_topc(A)
          & v1_compts_1(A) ) ) ) )).

fof(dt_l1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) )).

fof(fc9_struct_0,axiom,(
    ! [A] :
      ( ( ~ v8_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_finset_1(u1_struct_0(A)) ) )).

fof(t27_compts_1,conjecture,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_finset_1(u1_struct_0(A))
       => v1_compts_1(A) ) ) )).

%------------------------------------------------------------------------------

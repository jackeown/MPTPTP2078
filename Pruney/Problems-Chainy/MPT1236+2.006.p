%------------------------------------------------------------------------------
% File     : MPT1236+2.006 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 006 of t47_tops_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    6 (   0 unit)
%            Number of atoms       :   13 (   3 equality)
%            Maximal formula depth :    5 (   3 average)
%            Number of connectives :    7 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   7  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   1 constant; 0-2 arity)
%            Number of variables   :    7 (   0 sgn;   7   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t3_xboole_1,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) )).

fof(d2_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) )).

fof(dt_k1_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k1_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) )).

fof(dt_l1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) )).

fof(t44_tops_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) )).

fof(t47_tops_1,conjecture,(
    ! [A] :
      ( l1_pre_topc(A)
     => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) )).

%------------------------------------------------------------------------------

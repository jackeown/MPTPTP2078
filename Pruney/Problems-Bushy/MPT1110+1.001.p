%------------------------------------------------------------------------------
% File     : MPT1110+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : pre_topc__t39_pre_topc---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    7 (   0 unit)
%            Number of atoms       :   25 (   2 equality)
%            Maximal formula depth :   13 (   6 average)
%            Number of connectives :   18 (   0   ~;   0   |;   4   &)
%                                         (   3 <=>;  11  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   0 constant; 1-3 arity)
%            Number of variables   :   16 (   0 sgn;  15   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d3_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) )).

fof(d9_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) )).

fof(dt_l1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) )).

fof(dt_m1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) )).

fof(t1_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(t39_pre_topc,conjecture,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) )).

%------------------------------------------------------------------------------

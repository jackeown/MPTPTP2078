%------------------------------------------------------------------------------
% File     : MPT1319+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : tops_2__t40_tops_2---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    7 (   1 unit)
%            Number of atoms       :   29 (   4 equality)
%            Maximal formula depth :   16 (   8 average)
%            Number of connectives :   22 (   0   ~;   0   |;   5   &)
%                                         (   3 <=>;  14  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    6 (   0 constant; 1-3 arity)
%            Number of variables   :   24 (   0 sgn;  23   !;   1   ?)
%            Maximal term depth    :    5 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) )).

fof(d3_tarski,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) )).

fof(d3_tops_2,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B)))))
                 => ( D = k1_tops_2(A,B,C)
                  <=> ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B))))
                       => ( r2_hidden(E,D)
                        <=> ? [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(A)))
                              & r2_hidden(F,C)
                              & k9_subset_1(u1_struct_0(A),F,B) = E ) ) ) ) ) ) ) ) )).

fof(dt_k1_tops_2,axiom,(
    ! [A,B,C] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
     => m1_subset_1(k1_tops_2(A,B,C),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B))))) ) )).

fof(redefinition_k9_subset_1,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) )).

fof(t4_subset,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) )).

fof(t40_tops_2,conjecture,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                 => ( r1_tarski(C,D)
                   => r1_tarski(k1_tops_2(A,B,C),k1_tops_2(A,B,D)) ) ) ) ) ) )).

%------------------------------------------------------------------------------

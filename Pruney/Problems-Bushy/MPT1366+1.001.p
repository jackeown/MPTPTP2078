%------------------------------------------------------------------------------
% File     : MPT1366+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : compts_1__t21_compts_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   42 (   2 equality)
%            Maximal formula depth :   21 (  14 average)
%            Number of connectives :   45 (   7   ~;   1   |;  19   &)
%                                         (   1 <=>;  17  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   14 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :   13 (   0 sgn;  13   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d5_compts_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v9_pre_topc(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( C != k1_xboole_0
                    & v4_pre_topc(C,A)
                    & r2_hidden(B,k3_subset_1(u1_struct_0(A),C))
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ! [E] :
                            ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                           => ~ ( v3_pre_topc(D,A)
                                & v3_pre_topc(E,A)
                                & r2_hidden(B,D)
                                & r1_tarski(C,E)
                                & r1_xboole_0(D,E) ) ) ) ) ) ) ) ) )).

fof(t15_compts_1,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v8_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_compts_1(B,A)
             => ( B = k1_xboole_0
                | ! [C] :
                    ( m1_subset_1(C,u1_struct_0(A))
                   => ~ ( r2_hidden(C,k3_subset_1(u1_struct_0(A),B))
                        & ! [D] :
                            ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                           => ! [E] :
                                ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                               => ~ ( v3_pre_topc(D,A)
                                    & v3_pre_topc(E,A)
                                    & r2_hidden(C,D)
                                    & r1_tarski(B,E)
                                    & r1_xboole_0(D,E) ) ) ) ) ) ) ) ) ) ) )).

fof(t17_compts_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_compts_1(A)
              & v4_pre_topc(B,A) )
           => v2_compts_1(B,A) ) ) ) )).

fof(t21_compts_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( ( v8_pre_topc(A)
          & v1_compts_1(A) )
       => v9_pre_topc(A) ) ) )).

%------------------------------------------------------------------------------

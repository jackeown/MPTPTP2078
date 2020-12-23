%------------------------------------------------------------------------------
% File     : MPT1724+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t33_tmap_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   61 (  10 equality)
%            Maximal formula depth :   15 (  12 average)
%            Number of connectives :   82 (  25   ~;   3   |;  33   &)
%                                         (   0 <=>;  21  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   0 constant; 1-3 arity)
%            Number of variables   :   14 (   0 sgn;  14   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t22_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
               => ( ~ r1_tsep_1(B,C)
                  & ~ r1_tsep_1(C,B) ) ) ) ) ) )).

fof(t31_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( ~ ( ( r1_tsep_1(B,C)
                          | r1_tsep_1(C,B) )
                        & ~ ( r1_tsep_1(D,C)
                            & r1_tsep_1(C,D) )
                        & ~ ( k2_tsep_1(A,k1_tsep_1(A,B,D),C) = k2_tsep_1(A,D,C)
                            & k2_tsep_1(A,C,k1_tsep_1(A,B,D)) = k2_tsep_1(A,C,D) ) )
                    & ~ ( ~ ( r1_tsep_1(B,C)
                            & r1_tsep_1(C,B) )
                        & ( r1_tsep_1(D,C)
                          | r1_tsep_1(C,D) )
                        & ~ ( k2_tsep_1(A,k1_tsep_1(A,B,D),C) = k2_tsep_1(A,B,C)
                            & k2_tsep_1(A,C,k1_tsep_1(A,B,D)) = k2_tsep_1(A,C,B) ) ) ) ) ) ) ) )).

fof(t31_tsep_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ( ( m1_pre_topc(B,C)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                   => m1_pre_topc(B,C) )
                  & ( m1_pre_topc(C,B)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                   => m1_pre_topc(C,B) ) ) ) ) ) ) )).

fof(t33_tmap_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( m1_pre_topc(B,C)
                   => ( ( ~ r1_tsep_1(C,D)
                        & ~ r1_tsep_1(D,C) )
                      | ( k2_tsep_1(A,C,k1_tsep_1(A,B,D)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & k2_tsep_1(A,C,k1_tsep_1(A,D,B)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

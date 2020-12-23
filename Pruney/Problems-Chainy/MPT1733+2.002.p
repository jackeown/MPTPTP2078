%------------------------------------------------------------------------------
% File     : MPT1733+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t42_tmap_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    2 (   0 unit)
%            Number of atoms       :   32 (   0 equality)
%            Maximal formula depth :   14 (  14 average)
%            Number of connectives :   46 (  16   ~;   2   |;  14   &)
%                                         (   0 <=>;  14  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    1 (   0 constant; 3-3 arity)
%            Number of variables   :    8 (   0 sgn;   8   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t41_tmap_1,axiom,(
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
                 => ( ~ r1_tsep_1(B,C)
                   => ( ( ~ r1_tsep_1(k2_tsep_1(A,B,C),D)
                       => ( ~ r1_tsep_1(B,D)
                          & ~ r1_tsep_1(C,D) ) )
                      & ( ~ r1_tsep_1(D,k2_tsep_1(A,B,C))
                       => ( ~ r1_tsep_1(D,B)
                          & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ) )).

fof(t42_tmap_1,conjecture,(
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
                 => ( ~ r1_tsep_1(B,C)
                   => ( ( ( r1_tsep_1(B,D)
                          | r1_tsep_1(C,D) )
                       => r1_tsep_1(k2_tsep_1(A,B,C),D) )
                      & ( ( r1_tsep_1(D,B)
                          | r1_tsep_1(D,C) )
                       => r1_tsep_1(D,k2_tsep_1(A,B,C)) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

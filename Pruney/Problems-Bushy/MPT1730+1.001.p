%------------------------------------------------------------------------------
% File     : MPT1730+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : tmap_1__t39_tmap_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   14 (   4 unit)
%            Number of atoms       :   64 (   7 equality)
%            Maximal formula depth :   16 (   6 average)
%            Number of connectives :   72 (  22   ~;   0   |;  29   &)
%                                         (   3 <=>;  18  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-2 arity)
%            Number of functors    :    6 (   2 constant; 0-3 arity)
%            Number of variables   :   29 (   0 sgn;  29   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) )).

fof(d2_tsep_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) )).

fof(d3_tsep_1,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) )).

fof(d7_xboole_0,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) )).

fof(dt_k1_tsep_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) )).

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

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(fc5_xboole_0,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) )).

fof(symmetry_r1_tsep_1,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) )).

fof(t1_boole,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A )).

fof(t23_xboole_1,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t39_tmap_1,conjecture,(
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
                 => ( ~ ( ~ r1_tsep_1(k1_tsep_1(A,B,C),D)
                        & r1_tsep_1(B,D)
                        & r1_tsep_1(C,D) )
                    & ~ ( ~ ( r1_tsep_1(B,D)
                            & r1_tsep_1(C,D) )
                        & r1_tsep_1(k1_tsep_1(A,B,C),D) )
                    & ~ ( ~ r1_tsep_1(D,k1_tsep_1(A,B,C))
                        & r1_tsep_1(D,B)
                        & r1_tsep_1(D,C) )
                    & ~ ( ~ ( r1_tsep_1(D,B)
                            & r1_tsep_1(D,C) )
                        & r1_tsep_1(D,k1_tsep_1(A,B,C)) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

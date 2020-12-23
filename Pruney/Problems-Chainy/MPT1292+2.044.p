%------------------------------------------------------------------------------
% File     : MPT1292+2.044 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 044 of t5_tops_2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   2 unit)
%            Number of atoms       :   21 (   5 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   17 (   4   ~;   0   |;   6   &)
%                                         (   1 <=>;   6  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    9 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   1 constant; 0-2 arity)
%            Number of variables   :   10 (   0 sgn;   9   !;   1   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(l13_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 )).

fof(t4_subset_1,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) )).

fof(redefinition_k5_setfam_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) )).

fof(t60_setfam_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) )).

fof(fc2_struct_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) )).

fof(rc4_xreal_0,axiom,(
    ? [A] :
      ( v1_xboole_0(A)
      & v1_xcmplx_0(A)
      & v1_xxreal_0(A)
      & v1_xreal_0(A) ) )).

fof(t5_tops_2,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ~ ( m1_setfam_1(B,u1_struct_0(A))
              & B = k1_xboole_0 ) ) ) )).

%------------------------------------------------------------------------------

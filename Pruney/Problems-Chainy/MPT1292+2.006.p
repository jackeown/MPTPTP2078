%------------------------------------------------------------------------------
% File     : MPT1292+2.006 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 006 of t5_tops_2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    9 (   2 unit)
%            Number of atoms       :   27 (   5 equality)
%            Maximal formula depth :    9 (   5 average)
%            Number of connectives :   31 (  13   ~;   0   |;  12   &)
%                                         (   3 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    9 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   1 constant; 0-1 arity)
%            Number of variables   :   15 (   0 sgn;  14   !;   1   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) )).

fof(t3_xboole_0,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) )).

fof(d10_xboole_0,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) )).

fof(t2_xboole_1,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) )).

fof(t66_xboole_1,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) )).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 )).

fof(d12_setfam_1,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) )).

fof(fc2_struct_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) )).

fof(t5_tops_2,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ~ ( m1_setfam_1(B,u1_struct_0(A))
              & B = k1_xboole_0 ) ) ) )).

%------------------------------------------------------------------------------

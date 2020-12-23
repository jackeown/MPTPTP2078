%------------------------------------------------------------------------------
% File     : MPT0326+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : zfmisc_1__t139_zfmisc_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    7 (   3 unit)
%            Number of atoms       :   16 (   5 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   11 (   2   ~;   3   |;   1   &)
%                                         (   1 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   2 constant; 0-2 arity)
%            Number of variables   :   13 (   0 sgn;  12   !;   1   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ v1_xboole_0(A) )).

fof(t113_zfmisc_1,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) )).

fof(t138_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) )).

fof(t2_xboole_1,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t139_zfmisc_1,conjecture,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B,C,D] :
          ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
            | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
         => r1_tarski(B,D) ) ) )).

%------------------------------------------------------------------------------

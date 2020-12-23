%------------------------------------------------------------------------------
% File     : MPT0324+2.007 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 007 of t137_zfmisc_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   2 unit)
%            Number of atoms       :   12 (   3 equality)
%            Maximal formula depth :    9 (   6 average)
%            Number of connectives :    9 (   2   ~;   0   |;   2   &)
%                                         (   4 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   0 constant; 2-2 arity)
%            Number of variables   :   18 (   0 sgn;  18   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) )).

fof(t1_xboole_0,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) )).

fof(t100_xboole_1,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) )).

fof(t123_zfmisc_1,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) )).

fof(t137_zfmisc_1,conjecture,(
    ! [A,B,C,D,E] :
      ( ( r2_hidden(A,k2_zfmisc_1(B,C))
        & r2_hidden(A,k2_zfmisc_1(D,E)) )
     => r2_hidden(A,k2_zfmisc_1(k3_xboole_0(B,D),k3_xboole_0(C,E))) ) )).

%------------------------------------------------------------------------------

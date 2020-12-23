%------------------------------------------------------------------------------
% File     : MPT0898+2.016 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 016 of t58_mcart_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :   16 (  16 equality)
%            Maximal formula depth :   17 (  10 average)
%            Number of connectives :   18 (   5   ~;   4   |;   6   &)
%                                         (   1 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    2 (   1 constant; 0-4 arity)
%            Number of variables   :   14 (   0 sgn;  14   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t55_mcart_1,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) )).

fof(t56_mcart_1,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | D = k1_xboole_0
        | ( A = E
          & B = F
          & C = G
          & D = H ) ) ) )).

fof(t58_mcart_1,conjecture,(
    ! [A,B] :
      ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
     => A = B ) )).

%------------------------------------------------------------------------------

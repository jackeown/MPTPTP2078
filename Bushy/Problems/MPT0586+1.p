%------------------------------------------------------------------------------
% File     : MPT0586+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : relat_1__t190_relat_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :    9 (   0 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :    8 (   2   ~;   0   |;   3   &)
%                                         (   0 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 1-1 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :    6 (   0 sgn;   6   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t190_relat_1,conjecture,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( ~ v3_relat_1(k7_relat_1(B,A))
          & v3_relat_1(B) ) ) )).

fof(dt_k7_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) )).

fof(fc19_relat_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v3_relat_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v3_relat_1(k7_relat_1(A,B)) ) ) )).

%------------------------------------------------------------------------------

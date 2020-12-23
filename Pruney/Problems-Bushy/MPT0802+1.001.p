%------------------------------------------------------------------------------
% File     : MPT0802+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : wellord1__t54_wellord1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :   29 (   0 equality)
%            Maximal formula depth :   13 (  10 average)
%            Number of connectives :   26 (   0   ~;   0   |;  11   &)
%                                         (   1 <=>;  14  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    9 (   0 propositional; 1-3 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    7 (   0 sgn;   7   !;   0   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d4_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) )).

fof(t53_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( r3_wellord1(A,B,C)
               => ( ( v1_relat_2(A)
                   => v1_relat_2(B) )
                  & ( v8_relat_2(A)
                   => v8_relat_2(B) )
                  & ( v6_relat_2(A)
                   => v6_relat_2(B) )
                  & ( v4_relat_2(A)
                   => v4_relat_2(B) )
                  & ( v1_wellord1(A)
                   => v1_wellord1(B) ) ) ) ) ) ) )).

fof(t54_wellord1,conjecture,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( ( v2_wellord1(A)
                  & r3_wellord1(A,B,C) )
               => v2_wellord1(B) ) ) ) ) )).

%------------------------------------------------------------------------------

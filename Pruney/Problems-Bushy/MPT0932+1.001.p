%------------------------------------------------------------------------------
% File     : MPT0932+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : mcart_1__t93_mcart_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   16 (   3 equality)
%            Maximal formula depth :    9 (   6 average)
%            Number of connectives :   14 (   3   ~;   0   |;   5   &)
%                                         (   1 <=>;   5  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :   12 (   0 sgn;  11   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(fraenkel_a_2_0_mcart_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(B)
        & v1_relat_1(B) )
     => ( r2_hidden(A,a_2_0_mcart_1(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,B)
            & A = k2_mcart_1(D)
            & k1_mcart_1(D) = C ) ) ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(t92_mcart_1,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ! [B] : k11_relat_1(A,B) = a_2_0_mcart_1(A,B) ) )).

fof(t93_mcart_1,conjecture,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r2_hidden(B,A)
         => r2_hidden(k2_mcart_1(B),k11_relat_1(A,k1_mcart_1(B))) ) ) )).

%------------------------------------------------------------------------------

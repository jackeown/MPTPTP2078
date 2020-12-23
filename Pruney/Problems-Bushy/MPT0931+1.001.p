%------------------------------------------------------------------------------
% File     : MPT0931+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : mcart_1__t92_mcart_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   13 (   1 unit)
%            Number of atoms       :   41 (  17 equality)
%            Maximal formula depth :   10 (   6 average)
%            Number of connectives :   31 (   3   ~;   1   |;   6   &)
%                                         (   8 <=>;  13  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    7 (   0 constant; 1-2 arity)
%            Number of variables   :   41 (   0 sgn;  34   !;   7   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d13_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) )).

fof(d16_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) )).

fof(d1_mcart_1,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k1_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = C ) ) ) )).

fof(d1_tarski,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) )).

fof(d2_mcart_1,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k2_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = D ) ) ) )).

fof(existence_m1_subset_1,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) )).

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

fof(t23_mcart_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t2_tarski,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(t92_mcart_1,conjecture,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ! [B] : k11_relat_1(A,B) = a_2_0_mcart_1(A,B) ) )).

%------------------------------------------------------------------------------

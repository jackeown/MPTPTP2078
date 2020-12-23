%------------------------------------------------------------------------------
% File     : MPT0787+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : wellord1__t37_wellord1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    8 (   0 unit)
%            Number of atoms       :   42 (   4 equality)
%            Maximal formula depth :   12 (   8 average)
%            Number of connectives :   39 (   5   ~;   0   |;  13   &)
%                                         (   9 <=>;  12  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :   23 (   0 sgn;  23   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d1_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) )).

fof(d3_tarski,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) )).

fof(d4_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) )).

fof(l1_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) )).

fof(l2_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v8_relat_2(A)
      <=> ! [B,C,D] :
            ( ( r2_hidden(k4_tarski(B,C),A)
              & r2_hidden(k4_tarski(C,D),A) )
           => r2_hidden(k4_tarski(B,D),A) ) ) ) )).

fof(l3_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v4_relat_2(A)
      <=> ! [B,C] :
            ( ( r2_hidden(k4_tarski(B,C),A)
              & r2_hidden(k4_tarski(C,B),A) )
           => B = C ) ) ) )).

fof(l4_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> ! [B,C] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r2_hidden(C,k3_relat_1(A))
              & B != C
              & ~ r2_hidden(k4_tarski(B,C),A)
              & ~ r2_hidden(k4_tarski(C,B),A) ) ) ) )).

fof(t37_wellord1,conjecture,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) )
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT0950+1.002 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : wellord2__t17_wellord2---2.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   20 (   1 unit)
%            Number of atoms       :   66 (   6 equality)
%            Maximal formula depth :   11 (   5 average)
%            Number of connectives :   52 (   6   ~;   2   |;  12   &)
%                                         (   6 <=>;  26  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   12 (   0 propositional; 1-2 arity)
%            Number of functors    :    7 (   0 constant; 1-2 arity)
%            Number of variables   :   40 (   0 sgn;  40   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(cc1_ordinal1,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) )).

fof(cc5_ordinal1,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => v3_ordinal1(B) ) ) )).

fof(connectedness_r1_ordinal1,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) )).

fof(d1_wellord2,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) )).

fof(d2_ordinal1,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) )).

fof(d2_wellord2,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( B = k2_wellord2(A)
            <=> r4_wellord1(A,k1_wellord2(B)) ) ) ) ) )).

fof(dt_k1_wellord2,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) )).

fof(dt_k2_wellord2,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v3_ordinal1(k2_wellord2(A)) ) )).

fof(redefinition_r1_ordinal1,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) )).

fof(t10_wellord2,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(t50_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) )).

fof(t64_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r1_tarski(A,k3_relat_1(B))
          & v2_wellord1(B)
          & ~ r4_wellord1(B,k2_wellord1(B,A))
          & ! [C] :
              ~ ( r2_hidden(C,k3_relat_1(B))
                & r4_wellord1(k2_wellord1(B,k1_wellord1(B,C)),k2_wellord1(B,A)) ) ) ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(t8_boole,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) )).

fof(t8_wellord2,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) )).

fof(t9_wellord2,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( r1_tarski(B,A)
         => v2_wellord1(k1_wellord2(B)) ) ) )).

fof(t17_wellord2,conjecture,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r1_tarski(A,B)
       => r1_ordinal1(k2_wellord2(k1_wellord2(A)),B) ) ) )).

%------------------------------------------------------------------------------

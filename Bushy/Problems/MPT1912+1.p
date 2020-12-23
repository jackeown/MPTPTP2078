%------------------------------------------------------------------------------
% File     : MPT1912+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow_6__t5_yellow_6.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   38 (  16 unit)
%            Number of atoms       :   98 (   5 equality)
%            Maximal formula depth :    9 (   4 average)
%            Number of connectives :   69 (   9   ~;   2   |;  28   &)
%                                         (   4 <=>;  26  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   16 (   1 propositional; 0-2 arity)
%            Number of functors    :   12 (   1 constant; 0-2 arity)
%            Number of variables   :   52 (   0 sgn;  51   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t5_yellow_6,conjecture,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_classes2(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( r2_hidden(k1_relat_1(B),A)
              & r1_tarski(k2_relat_1(B),A) )
           => r2_hidden(k4_card_3(B),A) ) ) ) )).

fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) )).

fof(connectedness_r1_ordinal1,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) )).

fof(d1_classes1,axiom,(
    ! [A] :
      ( v1_classes1(A)
    <=> ! [B,C] :
          ( ( r2_hidden(B,A)
            & r1_tarski(C,B) )
         => r2_hidden(C,A) ) ) )).

fof(d4_card_3,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => k3_card_3(A) = k3_tarski(k2_relat_1(A)) ) )).

fof(dt_k1_card_1,axiom,(
    ! [A] : v1_card_1(k1_card_1(A)) )).

fof(dt_k1_funct_2,axiom,(
    $true )).

fof(dt_k1_relat_1,axiom,(
    $true )).

fof(dt_k1_setfam_1,axiom,(
    $true )).

fof(dt_k1_xboole_0,axiom,(
    $true )).

fof(dt_k1_zfmisc_1,axiom,(
    $true )).

fof(dt_k2_relat_1,axiom,(
    $true )).

fof(dt_k2_zfmisc_1,axiom,(
    $true )).

fof(dt_k3_card_3,axiom,(
    $true )).

fof(dt_k3_tarski,axiom,(
    $true )).

fof(dt_k4_card_3,axiom,(
    $true )).

fof(dt_k9_setfam_1,axiom,(
    ! [A] : m1_subset_1(k9_setfam_1(A),k1_zfmisc_1(k1_zfmisc_1(A))) )).

fof(dt_m1_subset_1,axiom,(
    $true )).

fof(existence_m1_subset_1,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) )).

fof(projectivity_k1_card_1,axiom,(
    ! [A] : k1_card_1(k1_card_1(A)) = k1_card_1(A) )).

fof(redefinition_k9_setfam_1,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) )).

fof(redefinition_r1_ordinal1,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) )).

fof(reflexivity_r1_ordinal1,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => r1_ordinal1(A,A) ) )).

fof(t10_funct_6,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => r1_tarski(k4_card_3(A),k1_funct_2(k1_relat_1(A),k3_card_3(A))) ) )).

fof(t1_classes2,axiom,(
    ! [A,B] :
      ( ( v1_classes1(A)
        & r2_hidden(B,A) )
     => ( ~ r2_tarski(B,A)
        & r2_hidden(k1_card_1(B),k1_card_1(A)) ) ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(t22_ordinal1,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ! [C] :
              ( v3_ordinal1(C)
             => ( ( r1_tarski(A,B)
                  & r2_hidden(B,C) )
               => r2_hidden(A,C) ) ) ) ) )).

fof(t2_classes1,axiom,(
    ! [A] :
      ( v2_classes1(A)
    <=> ( v1_classes1(A)
        & ! [B] :
            ( r2_hidden(B,A)
           => r2_hidden(k9_setfam_1(B),A) )
        & ! [B] :
            ( ( r1_tarski(B,A)
              & r2_hidden(k1_card_1(B),k1_card_1(A)) )
           => r2_hidden(B,A) ) ) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(t4_subset,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) )).

fof(t5_subset,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) )).

fof(t65_classes2,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(B)
        & v1_classes2(B) )
     => ( r2_hidden(A,B)
       => ( r2_hidden(k9_setfam_1(A),B)
          & r2_hidden(k3_tarski(A),B)
          & r2_hidden(k1_setfam_1(A),B) ) ) ) )).

fof(t67_classes2,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(C)
        & v1_classes2(C) )
     => ( ( r2_hidden(A,C)
          & r2_hidden(B,C) )
       => ( r2_hidden(k2_zfmisc_1(A,B),C)
          & r2_hidden(k1_funct_2(A,B),C) ) ) ) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(t80_card_2,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => r1_ordinal1(k1_card_1(k2_relat_1(A)),k1_card_1(k1_relat_1(A))) ) )).

fof(t8_boole,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) )).

%------------------------------------------------------------------------------

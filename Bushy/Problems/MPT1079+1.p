%------------------------------------------------------------------------------
% File     : MPT1079+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : funct_2__t196_funct_2.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   34 (  11 unit)
%            Number of atoms       :  125 (  11 equality)
%            Maximal formula depth :   14 (   6 average)
%            Number of connectives :  123 (  32   ~;   1   |;  54   &)
%                                         (   3 <=>;  33  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   1 propositional; 0-3 arity)
%            Number of functors    :   13 (   2 constant; 0-4 arity)
%            Number of variables   :   71 (   0 sgn;  69   !;   2   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t196_funct_2,conjecture,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,k2_zfmisc_1(B,C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
                 => ! [E] :
                      ( m1_subset_1(E,A)
                     => k3_funct_2(A,k2_zfmisc_1(B,C),D,E) = k4_tarski(k3_funct_2(A,B,k4_funct_2(A,B,C,D),E),k3_funct_2(A,C,k5_funct_2(A,B,C,D),E)) ) ) ) ) ) )).

fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) )).

fof(d6_funct_2,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,k2_zfmisc_1(B,C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,A,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                     => ( E = k4_funct_2(A,B,C,D)
                      <=> ! [F] :
                            ( m1_subset_1(F,A)
                           => k3_funct_2(A,B,E,F) = k1_mcart_1(k3_funct_2(A,k2_zfmisc_1(B,C),D,F)) ) ) ) ) ) ) ) )).

fof(d7_funct_2,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,k2_zfmisc_1(B,C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,A,C)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                     => ( E = k5_funct_2(A,B,C,D)
                      <=> ! [F] :
                            ( m1_subset_1(F,A)
                           => k3_funct_2(A,C,E,F) = k2_mcart_1(k3_funct_2(A,k2_zfmisc_1(B,C),D,F)) ) ) ) ) ) ) ) )).

fof(dt_k15_mcart_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k15_mcart_1(A))
        & v1_funct_1(k15_mcart_1(A)) ) ) )).

fof(dt_k16_mcart_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k16_mcart_1(A))
        & v1_funct_1(k16_mcart_1(A)) ) ) )).

fof(dt_k1_funct_1,axiom,(
    $true )).

fof(dt_k1_mcart_1,axiom,(
    $true )).

fof(dt_k1_xboole_0,axiom,(
    $true )).

fof(dt_k1_zfmisc_1,axiom,(
    $true )).

fof(dt_k2_mcart_1,axiom,(
    $true )).

fof(dt_k2_zfmisc_1,axiom,(
    $true )).

fof(dt_k3_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) )).

fof(dt_k4_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & v1_funct_1(D)
        & v1_funct_2(D,A,k2_zfmisc_1(B,C))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
     => ( v1_funct_1(k4_funct_2(A,B,C,D))
        & v1_funct_2(k4_funct_2(A,B,C,D),A,B)
        & m1_subset_1(k4_funct_2(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) )).

fof(dt_k4_tarski,axiom,(
    $true )).

fof(dt_k5_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & v1_funct_1(D)
        & v1_funct_2(D,A,k2_zfmisc_1(B,C))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
     => ( v1_funct_1(k5_funct_2(A,B,C,D))
        & v1_funct_2(k5_funct_2(A,B,C,D),A,C)
        & m1_subset_1(k5_funct_2(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) )).

fof(dt_m1_subset_1,axiom,(
    $true )).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(existence_m1_subset_1,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) )).

fof(redefinition_k3_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) )).

fof(redefinition_k4_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & v1_funct_1(D)
        & v1_funct_2(D,A,k2_zfmisc_1(B,C))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
     => k4_funct_2(A,B,C,D) = k15_mcart_1(D) ) )).

fof(redefinition_k5_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & v1_funct_1(D)
        & v1_funct_2(D,A,k2_zfmisc_1(B,C))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k2_zfmisc_1(B,C)))) )
     => k5_funct_2(A,B,C,D) = k16_mcart_1(D) ) )).

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

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(t8_boole,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) )).

fof(fc10_subset_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) )).

fof(fc6_relat_1,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) )).

fof(rc7_funct_1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v4_funct_1(A) ) )).

%------------------------------------------------------------------------------

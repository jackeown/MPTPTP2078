%------------------------------------------------------------------------------
% File     : MPT1079+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : funct_2__t196_funct_2---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   10 (   1 unit)
%            Number of atoms       :   66 (   6 equality)
%            Maximal formula depth :   14 (   9 average)
%            Number of connectives :   75 (  19   ~;   1   |;  29   &)
%                                         (   2 <=>;  24  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-3 arity)
%            Number of functors    :    8 (   0 constant; 1-4 arity)
%            Number of variables   :   37 (   0 sgn;  37   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
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

fof(fc10_subset_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) )).

fof(fc6_relat_1,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) )).

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

%------------------------------------------------------------------------------

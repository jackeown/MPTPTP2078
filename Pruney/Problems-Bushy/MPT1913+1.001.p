%------------------------------------------------------------------------------
% File     : MPT1913+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow_6__t9_yellow_6---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   42 (   5 equality)
%            Maximal formula depth :   14 (   9 average)
%            Number of connectives :   41 (   4   ~;   1   |;  26   &)
%                                         (   1 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   0 constant; 1-3 arity)
%            Number of variables   :   15 (   0 sgn;  15   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d13_pralg_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v2_pralg_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A)
            & v1_funct_1(C)
            & v1_partfun1(C,A) )
         => ( C = k12_pralg_1(A,B)
          <=> ! [D] :
                ~ ( r2_hidden(D,A)
                  & ! [E] :
                      ( l1_struct_0(E)
                     => ~ ( E = k1_funct_1(B,D)
                          & k1_funct_1(C,D) = u1_struct_0(E) ) ) ) ) ) ) )).

fof(dt_k12_pralg_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v2_pralg_1(B) )
     => ( v1_relat_1(k12_pralg_1(A,B))
        & v4_relat_1(k12_pralg_1(A,B),A)
        & v1_funct_1(k12_pralg_1(A,B))
        & v1_partfun1(k12_pralg_1(A,B),A) ) ) )).

fof(redefinition_k10_pralg_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v2_pralg_1(B)
        & m1_subset_1(C,A) )
     => k10_pralg_1(A,B,C) = k1_funct_1(B,C) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t9_yellow_6,conjecture,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_relat_1(B)
            & v4_relat_1(B,A)
            & v1_funct_1(B)
            & v1_partfun1(B,A)
            & v2_pralg_1(B) )
         => ! [C] :
              ( m1_subset_1(C,A)
             => k1_funct_1(k12_pralg_1(A,B),C) = u1_struct_0(k10_pralg_1(A,B,C)) ) ) ) )).

%------------------------------------------------------------------------------

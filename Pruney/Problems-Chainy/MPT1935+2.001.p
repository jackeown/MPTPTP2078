%------------------------------------------------------------------------------
% File     : MPT1935+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t33_yellow_6
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   38 (   3 equality)
%            Maximal formula depth :   12 (   9 average)
%            Number of connectives :   35 (   2   ~;   0   |;  18   &)
%                                         (   5 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   12 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :   17 (   0 sgn;  16   !;   1   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d5_funct_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) )).

fof(d4_partfun1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) )).

fof(d15_yellow_6,axiom,(
    ! [A,B] :
      ( l1_struct_0(B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A)
            & v1_funct_1(C)
            & v1_partfun1(C,A) )
         => ( m3_yellow_6(C,A,B)
          <=> ! [D] :
                ( r2_hidden(D,k2_relat_1(C))
               => ( ~ v2_struct_0(D)
                  & v4_orders_2(D)
                  & v7_waybel_0(D)
                  & l1_waybel_0(D,B) ) ) ) ) ) )).

fof(dt_m3_yellow_6,axiom,(
    ! [A,B] :
      ( l1_struct_0(B)
     => ! [C] :
          ( m3_yellow_6(C,A,B)
         => ( v1_relat_1(C)
            & v4_relat_1(C,A)
            & v1_funct_1(C)
            & v1_partfun1(C,A) ) ) ) )).

fof(t33_yellow_6,conjecture,(
    ! [A,B] :
      ( l1_struct_0(B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A)
            & v1_funct_1(C)
            & v1_partfun1(C,A) )
         => ( m3_yellow_6(C,A,B)
          <=> ! [D] :
                ( r2_hidden(D,A)
               => ( ~ v2_struct_0(k1_funct_1(C,D))
                  & v4_orders_2(k1_funct_1(C,D))
                  & v7_waybel_0(k1_funct_1(C,D))
                  & l1_waybel_0(k1_funct_1(C,D),B) ) ) ) ) ) )).

%------------------------------------------------------------------------------

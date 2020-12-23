%------------------------------------------------------------------------------
% File     : MPT0650+2.023 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 023 of t57_funct_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   38 (   9 equality)
%            Maximal formula depth :   13 (   8 average)
%            Number of connectives :   33 (   0   ~;   0   |;  18   &)
%                                         (   2 <=>;  13  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :   13 (   0 sgn;  13   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(dt_k2_funct_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) )).

fof(t21_funct_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) )).

fof(t22_funct_1,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) )).

fof(t54_funct_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) )).

fof(t57_funct_1,conjecture,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k2_relat_1(B)) )
       => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
          & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) )).

%------------------------------------------------------------------------------

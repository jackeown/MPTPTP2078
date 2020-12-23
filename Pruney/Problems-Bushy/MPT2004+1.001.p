%------------------------------------------------------------------------------
% File     : MPT2004+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_9__t3_waybel_9---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :    8 (   2 equality)
%            Maximal formula depth :   12 (  12 average)
%            Number of connectives :    7 (   0   ~;   0   |;   2   &)
%                                         (   0 <=>;   5  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-1 arity)
%            Number of variables   :    4 (   0 sgn;   4   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(t3_waybel_9,conjecture,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                 => ( ( u1_struct_0(A) = u1_struct_0(B)
                      & C = D
                      & m1_setfam_1(C,u1_struct_0(A)) )
                   => m1_setfam_1(D,u1_struct_0(B)) ) ) ) ) ) )).

%------------------------------------------------------------------------------

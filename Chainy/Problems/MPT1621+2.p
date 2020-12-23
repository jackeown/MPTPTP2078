%------------------------------------------------------------------------------
% File     : MPT1621+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_0__t1_waybel_0.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 3156 ( 439 unit)
%            Number of atoms       : 16003 (2332 equality)
%            Maximal formula depth :   35 (   7 average)
%            Number of connectives : 14913 (2066   ~; 118   |;6414   &)
%                                         ( 660 <=>;5655  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  209 (   1 propositional; 0-4 arity)
%            Number of functors    :  299 (   9 constant; 0-10 arity)
%            Number of variables   : 9123 (   9 sgn;8714   !; 409   ?)
%            Maximal term depth    :    6 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
include('Axioms/MPT001+2.ax').
include('Axioms/MPT002+2.ax').
include('Axioms/MPT003+2.ax').
include('Axioms/MPT004+2.ax').
include('Axioms/MPT005+2.ax').
include('Axioms/MPT006+2.ax').
include('Axioms/MPT007+2.ax').
include('Axioms/MPT008+2.ax').
include('Axioms/MPT009+2.ax').
include('Axioms/MPT010+2.ax').
include('Axioms/MPT011+2.ax').
include('Axioms/MPT012+2.ax').
include('Axioms/MPT013+2.ax').
include('Axioms/MPT014+2.ax').
include('Axioms/MPT015+2.ax').
include('Axioms/MPT016+2.ax').
include('Axioms/MPT017+2.ax').
include('Axioms/MPT018+2.ax').
include('Axioms/MPT019+2.ax').
include('Axioms/MPT020+2.ax').
include('Axioms/MPT021+2.ax').
include('Axioms/MPT022+2.ax').
include('Axioms/MPT023+2.ax').
include('Axioms/MPT024+2.ax').
include('Axioms/MPT025+2.ax').
include('Axioms/MPT026+2.ax').
%------------------------------------------------------------------------------
fof(d1_waybel_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ~ ( r2_hidden(C,B)
                        & r2_hidden(D,B)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ~ ( r2_hidden(E,B)
                                & r1_orders_2(A,C,E)
                                & r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) )).

fof(dt_o_1_2_waybel_0,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => m1_subset_1(o_1_2_waybel_0(A),A) ) )).

fof(s2_finset_1__e10_2_1__waybel_0,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v1_finset_1(C)
        & m1_subset_1(C,k1_zfmisc_1(B)) )
     => ( ( v1_finset_1(C)
          & ? [D] :
              ( m1_subset_1(D,u1_struct_0(A))
              & r2_hidden(D,B)
              & r2_lattice3(A,k1_xboole_0,D) )
          & ! [E,F] :
              ( ( r2_hidden(E,C)
                & r1_tarski(F,C)
                & ? [G] :
                    ( m1_subset_1(G,u1_struct_0(A))
                    & r2_hidden(G,B)
                    & r2_lattice3(A,F,G) ) )
             => ? [H] :
                  ( m1_subset_1(H,u1_struct_0(A))
                  & r2_hidden(H,B)
                  & r2_lattice3(A,k2_xboole_0(F,k1_tarski(E)),H) ) ) )
       => ? [I] :
            ( m1_subset_1(I,u1_struct_0(A))
            & r2_hidden(I,B)
            & r2_lattice3(A,C,I) ) ) ) )).

fof(t1_waybel_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( ~ v1_xboole_0(B)
              & v1_waybel_0(B,A) )
          <=> ! [C] :
                ( ( v1_finset_1(C)
                  & m1_subset_1(C,k1_zfmisc_1(B)) )
               => ? [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                    & r2_hidden(D,B)
                    & r2_lattice3(A,C,D) ) ) ) ) ) )).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : MPT1408+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : filter_1__t2_filter_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 2589 ( 420 unit)
%            Number of atoms       : 11565 (1968 equality)
%            Maximal formula depth :   27 (   7 average)
%            Number of connectives : 10497 (1521   ~; 116   |;4191   &)
%                                         ( 498 <=>;4171  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  173 (   1 propositional; 0-4 arity)
%            Number of functors    :  200 (   9 constant; 0-10 arity)
%            Number of variables   : 7338 (   9 sgn;7032   !; 306   ?)
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
%------------------------------------------------------------------------------
fof(cc3_lattice2,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v8_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A) ) ) ) )).

fof(cc4_lattice2,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v8_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v14_lattices(A) ) ) ) )).

fof(cc5_lattice2,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v8_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v15_lattices(A) ) ) ) )).

fof(d1_binop_1,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] : k1_binop_1(A,B,C) = k1_funct_1(A,k4_tarski(B,C)) ) )).

fof(d3_filter_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k2_filter_0(A,B) = a_2_0_filter_0(A,B) ) ) )).

fof(dt_k2_filter_0,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k2_filter_0(A,B))
        & v19_lattices(k2_filter_0(A,B),A)
        & v20_lattices(k2_filter_0(A,B),A)
        & m1_subset_1(k2_filter_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ) )).

fof(fc10_lattice2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v14_lattices(A)
        & l3_lattices(A) )
     => ( v1_funct_1(u1_lattices(A))
        & v1_funct_2(u1_lattices(A),k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)),u1_struct_0(A))
        & v1_setwiseo(u1_lattices(A),u1_struct_0(A)) ) ) )).

fof(fc2_lattice2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( v1_funct_1(u2_lattices(A))
        & v1_funct_2(u2_lattices(A),k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)),u1_struct_0(A))
        & v3_binop_1(u2_lattices(A),u1_struct_0(A)) ) ) )).

fof(fc3_lattice2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A) )
     => ( v1_funct_1(u2_lattices(A))
        & v1_funct_2(u2_lattices(A),k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)),u1_struct_0(A))
        & v1_binop_1(u2_lattices(A),u1_struct_0(A)) ) ) )).

fof(fc4_lattice2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_lattices(A)
        & l2_lattices(A) )
     => ( v1_funct_1(u2_lattices(A))
        & v1_funct_2(u2_lattices(A),k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)),u1_struct_0(A))
        & v2_binop_1(u2_lattices(A),u1_struct_0(A)) ) ) )).

fof(fc5_lattice2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ( v1_funct_1(u1_lattices(A))
        & v1_funct_2(u1_lattices(A),k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)),u1_struct_0(A))
        & v3_binop_1(u1_lattices(A),u1_struct_0(A)) ) ) )).

fof(fc6_lattice2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A) )
     => ( v1_funct_1(u1_lattices(A))
        & v1_funct_2(u1_lattices(A),k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)),u1_struct_0(A))
        & v1_binop_1(u1_lattices(A),u1_struct_0(A)) ) ) )).

fof(fc7_lattice2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_lattices(A)
        & l1_lattices(A) )
     => ( v1_funct_1(u1_lattices(A))
        & v1_funct_2(u1_lattices(A),k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)),u1_struct_0(A))
        & v2_binop_1(u1_lattices(A),u1_struct_0(A)) ) ) )).

fof(fc9_lattice2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v13_lattices(A)
        & l3_lattices(A) )
     => ( v1_funct_1(u2_lattices(A))
        & v1_funct_2(u2_lattices(A),k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)),u1_struct_0(A))
        & v1_setwiseo(u2_lattices(A),u1_struct_0(A)) ) ) )).

fof(fraenkel_a_2_0_filter_0,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & l3_lattices(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r2_hidden(A,a_2_0_filter_0(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattices(B,C,D) ) ) ) )).

fof(t10_filter_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & v19_lattices(D,A)
                    & v20_lattices(D,A)
                    & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                 => ( r2_hidden(B,D)
                   => ( r2_hidden(k3_lattices(A,B,C),D)
                      & r2_hidden(k3_lattices(A,C,B),D) ) ) ) ) ) ) )).

fof(t18_filter_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(B,k2_filter_0(A,C))
              <=> r3_lattices(A,C,B) ) ) ) ) )).

fof(t1_filter_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v19_lattices(B,A)
            & v20_lattices(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & v19_lattices(C,A)
                & v20_lattices(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ( ~ v1_xboole_0(k9_subset_1(u1_struct_0(A),B,C))
                & v19_lattices(k9_subset_1(u1_struct_0(A),B,C),A)
                & v20_lattices(k9_subset_1(u1_struct_0(A),B,C),A)
                & m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ) )).

fof(t2_filter_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( k2_filter_0(A,B) = k2_filter_0(A,C)
               => B = C ) ) ) ) )).

fof(t8_filter_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( ( ~ v1_xboole_0(B)
              & v19_lattices(B,A)
              & v20_lattices(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r2_hidden(D,B) )
                    <=> r2_hidden(k4_lattices(A,C,D),B) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

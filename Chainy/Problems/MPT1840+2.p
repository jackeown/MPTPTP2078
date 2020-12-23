%------------------------------------------------------------------------------
% File     : MPT1840+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : tex_2__t4_tex_2.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 3550 ( 439 unit)
%            Number of atoms       : 20716 (2562 equality)
%            Maximal formula depth :   35 (   8 average)
%            Number of connectives : 20171 (3005   ~; 154   |;8950   &)
%                                         ( 795 <=>;7267  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  242 (   1 propositional; 0-6 arity)
%            Number of functors    :  337 (   9 constant; 0-10 arity)
%            Number of variables   : 10653 (   9 sgn;10174   !; 479   ?)
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
include('Axioms/MPT027+2.ax').
include('Axioms/MPT028+2.ax').
%------------------------------------------------------------------------------
fof(cc1_realset1,axiom,(
    ! [A] :
      ( ~ v1_zfmisc_1(A)
     => ~ v1_xboole_0(A) ) )).

fof(cc2_realset1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) )).

fof(cc3_realset1,axiom,(
    ! [A] :
      ( v1_zfmisc_1(A)
     => v1_finset_1(A) ) )).

fof(cc4_realset1,axiom,(
    ! [A] :
      ( ~ v1_finset_1(A)
     => ~ v1_zfmisc_1(A) ) )).

fof(d1_tex_2,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) )).

fof(rc1_realset1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_zfmisc_1(A) ) )).

fof(rc2_realset1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & ~ v1_zfmisc_1(A) ) )).

fof(rc3_realset1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B)
          & v1_zfmisc_1(B) ) ) )).

fof(t1_tex_2,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) )).

fof(t2_tex_2,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( ~ v1_xboole_0(k3_xboole_0(A,B))
         => r1_tarski(A,B) ) ) )).

fof(t4_tex_2,conjecture,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( ( u1_struct_0(A) = u1_struct_0(B)
              & v7_struct_0(A) )
           => v7_struct_0(B) ) ) ) )).

%------------------------------------------------------------------------------

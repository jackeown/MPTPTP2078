%------------------------------------------------------------------------------
% File     : MPT1844+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : tex_2__t9_tex_2.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 3563 ( 439 unit)
%            Number of atoms       : 20784 (2563 equality)
%            Maximal formula depth :   35 (   8 average)
%            Number of connectives : 20263 (3042   ~; 154   |;8977   &)
%                                         ( 796 <=>;7294  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  242 (   1 propositional; 0-6 arity)
%            Number of functors    :  337 (   9 constant; 0-10 arity)
%            Number of variables   : 10679 (   9 sgn;10197   !; 482   ?)
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

fof(cc1_tex_2,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( v1_subset_1(B,A)
           => v1_xboole_0(B) ) ) ) )).

fof(cc2_realset1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) )).

fof(cc2_tex_2,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) )).

fof(cc3_realset1,axiom,(
    ! [A] :
      ( v1_zfmisc_1(A)
     => v1_finset_1(A) ) )).

fof(cc3_tex_2,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ( ~ v1_xboole_0(B)
              & ~ v1_subset_1(B,A) )
           => ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) ) ) ) ) )).

fof(cc4_realset1,axiom,(
    ! [A] :
      ( ~ v1_finset_1(A)
     => ~ v1_zfmisc_1(A) ) )).

fof(cc4_tex_2,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( ~ v1_xboole_0(B)
              & v1_subset_1(B,A) ) ) ) ) )).

fof(cc5_tex_2,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ( ~ v1_xboole_0(B)
              & ~ v1_subset_1(B,A) )
           => ( ~ v1_xboole_0(B)
              & ~ v1_zfmisc_1(B) ) ) ) ) )).

fof(d1_tex_2,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) )).

fof(d7_subset_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) )).

fof(rc1_realset1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_zfmisc_1(A) ) )).

fof(rc1_tex_2,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B)
          & v1_zfmisc_1(B) ) ) )).

fof(rc2_realset1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & ~ v1_zfmisc_1(A) ) )).

fof(rc2_tex_2,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B)
          & v1_zfmisc_1(B)
          & v1_subset_1(B,A) ) ) )).

fof(rc3_realset1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B)
          & v1_zfmisc_1(B) ) ) )).

fof(rc3_tex_2,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B)
          & ~ v1_zfmisc_1(B)
          & ~ v1_subset_1(B,A) ) ) )).

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

fof(t4_tex_2,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( ( u1_struct_0(A) = u1_struct_0(B)
              & v7_struct_0(A) )
           => v7_struct_0(B) ) ) ) )).

fof(t6_tex_2,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) )).

fof(t7_tex_2,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) )).

fof(t8_tex_2,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) )).

fof(t9_tex_2,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) )).

%------------------------------------------------------------------------------

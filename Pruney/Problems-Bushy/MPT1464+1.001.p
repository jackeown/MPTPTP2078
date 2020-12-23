%------------------------------------------------------------------------------
% File     : MPT1464+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : filter_1__t59_filter_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   13 (   0 unit)
%            Number of atoms       :  116 (   1 equality)
%            Maximal formula depth :   15 (  10 average)
%            Number of connectives :  121 (  18   ~;   0   |;  62   &)
%                                         (   2 <=>;  39  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   18 (   0 propositional; 1-2 arity)
%            Number of functors    :    6 (   0 constant; 1-3 arity)
%            Number of variables   :   44 (   0 sgn;  44   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(cc1_lattices,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) )).

fof(d11_filter_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k7_filter_0(A,B,C) = k4_lattices(A,k4_filter_0(A,B,C),k4_filter_0(A,C,B)) ) ) ) )).

fof(dt_k3_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_lattices(A,B,C),u1_struct_0(A)) ) )).

fof(dt_k4_filter_0,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_filter_0(A,B,C),u1_struct_0(A)) ) )).

fof(dt_k4_lattices,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_lattices(A,B,C),u1_struct_0(A)) ) )).

fof(dt_l3_lattices,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) )).

fof(l66_filter_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v3_filter_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v19_lattices(B,A)
            & v20_lattices(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(A))
                     => ( r2_hidden(k4_filter_0(A,C,D),B)
                       => ( r2_hidden(k4_filter_0(A,C,k3_lattices(A,D,E)),B)
                          & r2_hidden(k4_filter_0(A,C,k3_lattices(A,E,D)),B)
                          & r2_hidden(k4_filter_0(A,k4_lattices(A,C,E),D),B)
                          & r2_hidden(k4_filter_0(A,k4_lattices(A,E,C),D),B) ) ) ) ) ) ) ) )).

fof(l68_filter_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v3_filter_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v19_lattices(B,A)
            & v20_lattices(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(A))
                     => ( ( r2_hidden(k4_filter_0(A,C,D),B)
                          & r2_hidden(k4_filter_0(A,E,D),B) )
                       => r2_hidden(k4_filter_0(A,k3_lattices(A,C,E),D),B) ) ) ) ) ) ) )).

fof(l70_filter_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v3_filter_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v19_lattices(B,A)
            & v20_lattices(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(A))
                     => ( ( r2_hidden(k4_filter_0(A,C,D),B)
                          & r2_hidden(k4_filter_0(A,C,E),B) )
                       => r2_hidden(k4_filter_0(A,C,k4_lattices(A,D,E)),B) ) ) ) ) ) ) )).

fof(t4_subset,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

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

fof(t59_filter_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v3_filter_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v19_lattices(B,A)
            & v20_lattices(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(A))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(A))
                         => ( ( r2_hidden(k7_filter_0(A,C,D),B)
                              & r2_hidden(k7_filter_0(A,E,F),B) )
                           => ( r2_hidden(k7_filter_0(A,k3_lattices(A,C,E),k3_lattices(A,D,F)),B)
                              & r2_hidden(k7_filter_0(A,k4_lattices(A,C,E),k4_lattices(A,D,F)),B) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

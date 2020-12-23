%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t2_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:08 EDT 2019

% Result     : Theorem 9.39s
% Output     : Refutation 9.39s
% Verified   : 
% Statistics : Number of formulae       :  180 (2162 expanded)
%              Number of leaves         :   13 ( 767 expanded)
%              Depth                    :   39
%              Number of atoms          :  922 (14992 expanded)
%              Number of equality atoms :   78 (4067 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7548,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7547,f94])).

fof(f94,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,
    ( sK1 != sK2
    & k2_filter_0(sK0,sK1) = k2_filter_0(sK0,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f71,f70,f69])).

fof(f69,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k2_filter_0(X0,X1) = k2_filter_0(X0,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_filter_0(sK0,X1) = k2_filter_0(sK0,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_filter_0(X0,X1) = k2_filter_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK1 != X2
            & k2_filter_0(X0,sK1) = k2_filter_0(X0,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k2_filter_0(X0,X1) = k2_filter_0(X0,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK2 != X1
        & k2_filter_0(X0,sK2) = k2_filter_0(X0,X1)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_filter_0(X0,X1) = k2_filter_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_filter_0(X0,X1) = k2_filter_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_filter_0(X0,X1) = k2_filter_0(X0,X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_filter_0(X0,X1) = k2_filter_0(X0,X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t2_filter_1.p',t2_filter_1)).

fof(f7547,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f7546,f91])).

fof(f91,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f72])).

fof(f7546,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f7545,f92])).

fof(f92,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f72])).

fof(f7545,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f7528,f1221])).

fof(f1221,plain,(
    r3_lattices(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f624,f1219])).

fof(f1219,plain,(
    r2_hidden(sK1,k2_filter_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1218,f592])).

fof(f592,plain,(
    sK1 = sK6(sK1,sK0,sK1) ),
    inference(subsumption_resolution,[],[f575,f91])).

fof(f575,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK6(sK1,sK0,sK1) ),
    inference(resolution,[],[f569,f313])).

fof(f313,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_filter_0(sK0,sK1))
      | sK6(X0,sK0,sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f310,f91])).

fof(f310,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_filter_0(sK0,sK1))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | sK6(X0,sK0,sK1) = X0 ) ),
    inference(superposition,[],[f301,f185])).

fof(f185,plain,(
    k2_filter_0(sK0,sK1) = a_2_0_filter_0(sK0,sK1) ),
    inference(resolution,[],[f184,f91])).

fof(f184,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_filter_0(sK0,X0) = a_2_0_filter_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f183,f88])).

fof(f88,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f183,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_filter_0(sK0,X0) = a_2_0_filter_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f182,f90])).

fof(f90,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k2_filter_0(sK0,X0) = a_2_0_filter_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f100,f89])).

fof(f89,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_filter_0(X0,X1) = a_2_0_filter_0(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_filter_0(X0,X1) = a_2_0_filter_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_filter_0(X0,X1) = a_2_0_filter_0(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k2_filter_0(X0,X1) = a_2_0_filter_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t2_filter_1.p',d3_filter_0)).

fof(f301,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_filter_0(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | sK6(X0,sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f300,f88])).

fof(f300,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_filter_0(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | sK6(X0,sK0,X1) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f299,f90])).

fof(f299,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_filter_0(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | sK6(X0,sK0,X1) = X0
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f107,f89])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ r2_hidden(X0,a_2_0_filter_0(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | sK6(X0,X1,X2) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_filter_0(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,X2,sK6(X0,X1,X2))
            & sK6(X0,X1,X2) = X0
            & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_filter_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f82,f83])).

fof(f83,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattices(X1,X2,X4)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,sK6(X0,X1,X2))
        & sK6(X0,X1,X2) = X0
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_filter_0(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattices(X1,X2,X4)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_filter_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_filter_0(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattices(X1,X2,X3)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_filter_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_filter_0(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_filter_0(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_filter_0(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t2_filter_1.p',fraenkel_a_2_0_filter_0)).

fof(f569,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f568,f90])).

fof(f568,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f567,f88])).

fof(f567,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f566,f89])).

fof(f566,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f565,f118])).

fof(f118,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t2_filter_1.p',cc1_lattices)).

fof(f565,plain,(
    ! [X0] :
      ( ~ v6_lattices(sK0)
      | r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f564,f90])).

fof(f564,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ v6_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f563,f88])).

fof(f563,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f562,f89])).

fof(f562,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ v6_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f561,f119])).

fof(f119,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f561,plain,(
    ! [X0] :
      ( ~ v8_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f560,f90])).

fof(f560,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f559,f88])).

fof(f559,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f558,f89])).

fof(f558,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f553,f120])).

fof(f120,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f553,plain,(
    ! [X0] :
      ( ~ v9_lattices(sK0)
      | r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f552,f88])).

fof(f552,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f551,f90])).

fof(f551,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f546])).

fof(f546,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k2_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f545,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r3_lattices(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t2_filter_1.p',reflexivity_r3_lattices)).

fof(f545,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k2_filter_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f544,f88])).

fof(f544,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k2_filter_0(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f543,f90])).

fof(f543,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r2_hidden(X1,k2_filter_0(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f99,f89])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ r3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r2_hidden(X1,k2_filter_0(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X1,k2_filter_0(X0,X2))
                  | ~ r3_lattices(X0,X2,X1) )
                & ( r3_lattices(X0,X2,X1)
                  | ~ r2_hidden(X1,k2_filter_0(X0,X2)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X1,k2_filter_0(X0,X2))
              <=> r3_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X1,k2_filter_0(X0,X2))
              <=> r3_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_filter_0(X0,X2))
              <=> r3_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t2_filter_1.p',t18_filter_0)).

fof(f1218,plain,(
    r2_hidden(sK6(sK1,sK0,sK1),k2_filter_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1197,f592])).

fof(f1197,plain,(
    r2_hidden(sK6(sK6(sK1,sK0,sK1),sK0,sK1),k2_filter_0(sK0,sK1)) ),
    inference(resolution,[],[f1168,f91])).

fof(f1168,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK6(sK6(X1,sK0,X1),sK0,X1),k2_filter_0(sK0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f1154])).

fof(f1154,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK6(sK6(X1,sK0,X1),sK0,X1),k2_filter_0(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f1146,f557])).

fof(f557,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,a_2_0_filter_0(sK0,X1))
      | r2_hidden(sK6(X2,sK0,X1),k2_filter_0(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f556,f468])).

fof(f468,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_filter_0(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(sK6(X0,sK0,X1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f467,f88])).

fof(f467,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_filter_0(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(sK6(X0,sK0,X1),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f466,f90])).

fof(f466,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_filter_0(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | m1_subset_1(sK6(X0,sK0,X1),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f106,f89])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ r2_hidden(X0,a_2_0_filter_0(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f556,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(X2,sK0,X1),u1_struct_0(sK0))
      | r2_hidden(sK6(X2,sK0,X1),k2_filter_0(sK0,X1))
      | ~ r2_hidden(X2,a_2_0_filter_0(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f555,f88])).

fof(f555,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(X2,sK0,X1),u1_struct_0(sK0))
      | r2_hidden(sK6(X2,sK0,X1),k2_filter_0(sK0,X1))
      | ~ r2_hidden(X2,a_2_0_filter_0(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f554,f89])).

fof(f554,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(X2,sK0,X1),u1_struct_0(sK0))
      | r2_hidden(sK6(X2,sK0,X1),k2_filter_0(sK0,X1))
      | ~ r2_hidden(X2,a_2_0_filter_0(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f550,f90])).

fof(f550,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(X2,sK0,X1),u1_struct_0(sK0))
      | r2_hidden(sK6(X2,sK0,X1),k2_filter_0(sK0,X1))
      | ~ r2_hidden(X2,a_2_0_filter_0(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f547])).

fof(f547,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(X2,sK0,X1),u1_struct_0(sK0))
      | r2_hidden(sK6(X2,sK0,X1),k2_filter_0(sK0,X1))
      | ~ r2_hidden(X2,a_2_0_filter_0(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f545,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X1,X2,sK6(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_filter_0(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f1146,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0,sK0,X0),a_2_0_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f1134])).

fof(f1134,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0,sK0,X0),a_2_0_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f746,f761])).

fof(f761,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f760,f90])).

fof(f760,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f759,f88])).

fof(f759,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f758,f89])).

fof(f758,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f757,f118])).

fof(f757,plain,(
    ! [X0] :
      ( ~ v6_lattices(sK0)
      | r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f756,f90])).

fof(f756,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ v6_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f755,f88])).

fof(f755,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f754,f89])).

fof(f754,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ v6_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f753,f119])).

fof(f753,plain,(
    ! [X0] :
      ( ~ v8_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f752,f90])).

fof(f752,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f751,f88])).

fof(f751,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f750,f89])).

fof(f750,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f742,f120])).

fof(f742,plain,(
    ! [X0] :
      ( ~ v9_lattices(sK0)
      | r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f741,f88])).

fof(f741,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f724,f90])).

fof(f724,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f719])).

fof(f719,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_filter_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f708,f125])).

fof(f708,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X1,a_2_0_filter_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f707,f88])).

fof(f707,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X1,a_2_0_filter_0(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f706,f90])).

fof(f706,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r2_hidden(X1,a_2_0_filter_0(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f124,f89])).

fof(f124,plain,(
    ! [X2,X3,X1] :
      ( ~ v10_lattices(X1)
      | ~ r3_lattices(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r2_hidden(X3,a_2_0_filter_0(X1,X2))
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_filter_0(X1,X2))
      | ~ r3_lattices(X1,X2,X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f746,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,a_2_0_filter_0(sK0,X2))
      | r2_hidden(sK6(X1,sK0,X2),a_2_0_filter_0(sK0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f745,f468])).

fof(f745,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(X1,sK0,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(sK6(X1,sK0,X2),a_2_0_filter_0(sK0,X2))
      | ~ r2_hidden(X1,a_2_0_filter_0(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f744,f88])).

fof(f744,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(X1,sK0,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(sK6(X1,sK0,X2),a_2_0_filter_0(sK0,X2))
      | ~ r2_hidden(X1,a_2_0_filter_0(sK0,X2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f743,f89])).

fof(f743,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(X1,sK0,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(sK6(X1,sK0,X2),a_2_0_filter_0(sK0,X2))
      | ~ r2_hidden(X1,a_2_0_filter_0(sK0,X2))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f723,f90])).

fof(f723,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(X1,sK0,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(sK6(X1,sK0,X2),a_2_0_filter_0(sK0,X2))
      | ~ r2_hidden(X1,a_2_0_filter_0(sK0,X2))
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f720])).

fof(f720,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(X1,sK0,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(sK6(X1,sK0,X2),a_2_0_filter_0(sK0,X2))
      | ~ r2_hidden(X1,a_2_0_filter_0(sK0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f708,f108])).

fof(f624,plain,
    ( r3_lattices(sK0,sK2,sK1)
    | ~ r2_hidden(sK1,k2_filter_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f623,f191])).

fof(f191,plain,(
    k2_filter_0(sK0,sK1) = a_2_0_filter_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f186,f93])).

fof(f93,plain,(
    k2_filter_0(sK0,sK1) = k2_filter_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f72])).

fof(f186,plain,(
    k2_filter_0(sK0,sK2) = a_2_0_filter_0(sK0,sK2) ),
    inference(resolution,[],[f184,f92])).

fof(f623,plain,
    ( r3_lattices(sK0,sK2,sK1)
    | ~ r2_hidden(sK1,a_2_0_filter_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f622,f88])).

fof(f622,plain,
    ( r3_lattices(sK0,sK2,sK1)
    | ~ r2_hidden(sK1,a_2_0_filter_0(sK0,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f621,f89])).

fof(f621,plain,
    ( r3_lattices(sK0,sK2,sK1)
    | ~ r2_hidden(sK1,a_2_0_filter_0(sK0,sK2))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f620,f90])).

fof(f620,plain,
    ( r3_lattices(sK0,sK2,sK1)
    | ~ r2_hidden(sK1,a_2_0_filter_0(sK0,sK2))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f619,f92])).

fof(f619,plain,
    ( r3_lattices(sK0,sK2,sK1)
    | ~ r2_hidden(sK1,a_2_0_filter_0(sK0,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f108,f590])).

fof(f590,plain,(
    sK1 = sK6(sK1,sK0,sK2) ),
    inference(subsumption_resolution,[],[f574,f91])).

fof(f574,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK6(sK1,sK0,sK2) ),
    inference(resolution,[],[f569,f314])).

fof(f314,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_filter_0(sK0,sK1))
      | sK6(X1,sK0,sK2) = X1 ) ),
    inference(subsumption_resolution,[],[f311,f92])).

fof(f311,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_filter_0(sK0,sK1))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | sK6(X1,sK0,sK2) = X1 ) ),
    inference(superposition,[],[f301,f191])).

fof(f7528,plain,
    ( ~ r3_lattices(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK2 ),
    inference(resolution,[],[f7526,f652])).

fof(f652,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f651,f597])).

fof(f597,plain,(
    r2_hidden(sK2,k2_filter_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f583,f92])).

fof(f583,plain,
    ( r2_hidden(sK2,k2_filter_0(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[],[f569,f93])).

fof(f651,plain,
    ( ~ r2_hidden(sK2,k2_filter_0(sK0,sK1))
    | r3_lattices(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f650,f185])).

fof(f650,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,a_2_0_filter_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f649,f88])).

fof(f649,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,a_2_0_filter_0(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f648,f89])).

fof(f648,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,a_2_0_filter_0(sK0,sK1))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f647,f90])).

fof(f647,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,a_2_0_filter_0(sK0,sK1))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f646,f91])).

fof(f646,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,a_2_0_filter_0(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f108,f601])).

fof(f601,plain,(
    sK2 = sK6(sK2,sK0,sK1) ),
    inference(resolution,[],[f597,f313])).

fof(f7526,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X1,X0)
      | ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f7525])).

fof(f7525,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f7524,f7515])).

fof(f7515,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f7514,f88])).

fof(f7514,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f7513,f90])).

fof(f7513,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f7512,f89])).

fof(f7512,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f7511,f118])).

fof(f7511,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f7510,f119])).

fof(f7510,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f7509])).

fof(f7509,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f114,f120])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t2_filter_1.p',redefinition_r3_lattices)).

fof(f7524,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X1,X0)
      | X0 = X1
      | ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f7523,f90])).

fof(f7523,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | X0 = X1
      | ~ r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f7522,f88])).

fof(f7522,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | X0 = X1
      | ~ r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f7521,f89])).

fof(f7521,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | X0 = X1
      | ~ r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f7520,f117])).

fof(f117,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f7520,plain,(
    ! [X0,X1] :
      ( ~ v4_lattices(sK0)
      | ~ r3_lattices(sK0,X1,X0)
      | X0 = X1
      | ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f7519,f90])).

fof(f7519,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X1,X0)
      | X0 = X1
      | ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v4_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f7518,f123])).

fof(f123,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t2_filter_1.p',dt_l3_lattices)).

fof(f7518,plain,(
    ! [X0,X1] :
      ( ~ l2_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | X0 = X1
      | ~ r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f7517,f88])).

fof(f7517,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | X0 = X1
      | ~ r1_lattices(sK0,X1,X0)
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f7516])).

fof(f7516,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | X0 = X1
      | ~ r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f7515,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t2_filter_1.p',t26_lattices)).
%------------------------------------------------------------------------------

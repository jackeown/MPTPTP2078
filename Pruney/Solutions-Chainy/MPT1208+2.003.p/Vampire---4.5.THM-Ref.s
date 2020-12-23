%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:41 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  191 (2133 expanded)
%              Number of leaves         :   20 ( 659 expanded)
%              Depth                    :   44
%              Number of atoms          :  902 (12049 expanded)
%              Number of equality atoms :  101 (1846 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2143,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2104,f2134])).

fof(f2134,plain,(
    ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f2133])).

fof(f2133,plain,
    ( $false
    | ~ spl8_18 ),
    inference(global_subsumption,[],[f786,f1991,f802])).

fof(f802,plain,(
    sK1 != k2_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(superposition,[],[f71,f331])).

fof(f331,plain,(
    k4_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(resolution,[],[f174,f130])).

fof(f130,plain,(
    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f129,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v14_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k4_lattices(X0,k6_lattices(X0),X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k4_lattices(sK0,k6_lattices(sK0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v14_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( k4_lattices(sK0,k6_lattices(sK0),X1) != X1
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

fof(f129,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f84,f110])).

fof(f110,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f73,f69])).

fof(f69,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f84,plain,(
    ! [X0] :
      ( ~ l2_lattices(X0)
      | m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f174,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,sK1) = k4_lattices(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f173,f66])).

fof(f173,plain,(
    ! [X0] :
      ( k2_lattices(sK0,X0,sK1) = k4_lattices(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f172,f119])).

fof(f119,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f118,f69])).

fof(f118,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f117,f66])).

fof(f117,plain,
    ( v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f77,f67])).

fof(f67,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f172,plain,(
    ! [X0] :
      ( k2_lattices(sK0,X0,sK1) = k4_lattices(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f109])).

fof(f109,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f72,f69])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f171,plain,(
    ! [X0] :
      ( k2_lattices(sK0,X0,sK1) = k4_lattices(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f101,f70])).

fof(f70,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f71,plain,(
    sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1991,plain,(
    r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1)) ),
    inference(forward_demodulation,[],[f1990,f372])).

fof(f372,plain,(
    sK1 = k2_lattices(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f371,f66])).

fof(f371,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f370,f125])).

fof(f125,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f124,f69])).

fof(f124,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f123,f66])).

fof(f123,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f79,f67])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f370,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK1)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f369,f128])).

fof(f128,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f127,f69])).

fof(f127,plain,
    ( v9_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f126,f66])).

fof(f126,plain,
    ( v9_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f80,f67])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f369,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK1)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f368,f69])).

fof(f368,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK1)
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f359,f70])).

fof(f359,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f356])).

fof(f356,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f318,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f318,plain,(
    r1_lattices(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f317,f66])).

fof(f317,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f316,f119])).

fof(f316,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f315,f125])).

fof(f315,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f314,f128])).

fof(f314,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f313,f69])).

fof(f313,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f312,f70])).

fof(f312,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f303,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f303,plain,(
    r3_lattices(sK0,sK1,sK1) ),
    inference(resolution,[],[f166,f70])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_lattices(sK0,X0,X0) ) ),
    inference(subsumption_resolution,[],[f165,f66])).

fof(f165,plain,(
    ! [X0] :
      ( r3_lattices(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f164,f119])).

fof(f164,plain,(
    ! [X0] :
      ( r3_lattices(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f163,f125])).

fof(f163,plain,(
    ! [X0] :
      ( r3_lattices(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f162,f128])).

fof(f162,plain,(
    ! [X0] :
      ( r3_lattices(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f161,f69])).

fof(f161,plain,(
    ! [X0] :
      ( r3_lattices(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f102,f70])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

fof(f1990,plain,(
    r1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k2_lattices(sK0,k6_lattices(sK0),sK1)) ),
    inference(forward_demodulation,[],[f1979,f372])).

fof(f1979,plain,(
    r1_lattices(sK0,k2_lattices(sK0,sK1,k2_lattices(sK0,sK1,sK1)),k2_lattices(sK0,k6_lattices(sK0),k2_lattices(sK0,sK1,sK1))) ),
    inference(resolution,[],[f829,f307])).

fof(f307,plain,(
    m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f147,f70])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(k2_lattices(sK0,X0,sK1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f146,f66])).

fof(f146,plain,(
    ! [X0] :
      ( m1_subset_1(k2_lattices(sK0,X0,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f109])).

fof(f145,plain,(
    ! [X0] :
      ( m1_subset_1(k2_lattices(sK0,X0,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f100,f70])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(f829,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0)) ) ),
    inference(subsumption_resolution,[],[f828,f66])).

fof(f828,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f827,f122])).

fof(f122,plain,(
    v7_lattices(sK0) ),
    inference(subsumption_resolution,[],[f121,f69])).

fof(f121,plain,
    ( v7_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f120,f66])).

fof(f120,plain,
    ( v7_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f78,f67])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v7_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f827,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f826,f125])).

fof(f826,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v7_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f825,f128])).

fof(f825,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v7_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f824,f69])).

fof(f824,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v7_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f823,f70])).

fof(f823,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v7_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f819,f130])).

fof(f819,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v7_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f810,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).

fof(f810,plain,(
    r1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f809,f139])).

fof(f139,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f138,f66])).

fof(f138,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f137,f110])).

fof(f137,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f136,f68])).

fof(f68,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f136,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ v14_lattices(sK0)
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f107,f70])).

fof(f107,plain,(
    ! [X0,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f105,f84])).

fof(f105,plain,(
    ! [X0,X3] :
      ( k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( k1_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ( ( k1_lattices(X0,sK2(X0,X1),X1) != X1
                  | k1_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k1_lattices(X0,X2,X1) != X1
            | k1_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k1_lattices(X0,sK2(X0,X1),X1) != X1
          | k1_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k6_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattices)).

fof(f809,plain,(
    r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f805,f372])).

fof(f805,plain,(
    r1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k6_lattices(sK0))) ),
    inference(resolution,[],[f284,f307])).

fof(f284,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0))) ) ),
    inference(subsumption_resolution,[],[f283,f66])).

fof(f283,plain,(
    ! [X0] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f282,f116])).

fof(f116,plain,(
    v5_lattices(sK0) ),
    inference(subsumption_resolution,[],[f115,f69])).

fof(f115,plain,
    ( v5_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f114,f66])).

fof(f114,plain,
    ( v5_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f76,f67])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v5_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f282,plain,(
    ! [X0] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f281,f119])).

fof(f281,plain,(
    ! [X0] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f280,f125])).

fof(f280,plain,(
    ! [X0] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f279,f128])).

fof(f279,plain,(
    ! [X0] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f268,f69])).

fof(f268,plain,(
    ! [X0] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f130,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_lattices)).

fof(f786,plain,
    ( sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1))
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f785,f66])).

fof(f785,plain,
    ( sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f784,f113])).

fof(f113,plain,(
    v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f112,f69])).

fof(f112,plain,
    ( v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f111,f66])).

fof(f111,plain,
    ( v4_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f75,f67])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f784,plain,
    ( sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1))
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f783,f110])).

fof(f783,plain,
    ( sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f782,f70])).

fof(f782,plain,
    ( sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f759,f309])).

fof(f309,plain,(
    m1_subset_1(k2_lattices(sK0,k6_lattices(sK0),sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f147,f130])).

fof(f759,plain,
    ( sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1))
    | ~ m1_subset_1(k2_lattices(sK0,k6_lattices(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_18 ),
    inference(resolution,[],[f546,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

fof(f546,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl8_18
  <=> r1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f2104,plain,(
    spl8_18 ),
    inference(avatar_contradiction_clause,[],[f2103])).

fof(f2103,plain,
    ( $false
    | spl8_18 ),
    inference(global_subsumption,[],[f721,f545])).

fof(f545,plain,
    ( ~ r1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f544])).

fof(f721,plain,(
    r1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1) ),
    inference(forward_demodulation,[],[f707,f327])).

fof(f327,plain,(
    sK1 = k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1) ),
    inference(resolution,[],[f170,f130])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,X0,sK1),sK1) ) ),
    inference(subsumption_resolution,[],[f169,f66])).

fof(f169,plain,(
    ! [X0] :
      ( sK1 = k1_lattices(sK0,k2_lattices(sK0,X0,sK1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f168,f69])).

fof(f168,plain,(
    ! [X0] :
      ( sK1 = k1_lattices(sK0,k2_lattices(sK0,X0,sK1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f125])).

fof(f167,plain,(
    ! [X0] :
      ( sK1 = k1_lattices(sK0,k2_lattices(sK0,X0,sK1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f70])).

fof(f96,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK7(X0) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f61,f63,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK7(X0) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0))
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(f707,plain,(
    r1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1)) ),
    inference(resolution,[],[f309,f186])).

fof(f186,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) ) ),
    inference(subsumption_resolution,[],[f185,f66])).

fof(f185,plain,(
    ! [X0] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f116])).

fof(f184,plain,(
    ! [X0] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f183,f119])).

fof(f183,plain,(
    ! [X0] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f182,f125])).

fof(f182,plain,(
    ! [X0] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f181,f128])).

fof(f181,plain,(
    ! [X0] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f69])).

fof(f180,plain,(
    ! [X0] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f83,f70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (15458)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.50  % (15450)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (15455)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (15439)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (15442)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (15437)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (15438)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (15441)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (15447)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (15445)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (15453)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (15449)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (15459)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.53  % (15457)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (15435)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.53  % (15456)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (15443)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (15452)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.54  % (15446)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.54  % (15454)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.54  % (15444)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.54  % (15451)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.55  % (15440)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.55  % (15460)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.56  % (15448)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (15436)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.87/0.61  % (15445)Refutation found. Thanks to Tanya!
% 1.87/0.61  % SZS status Theorem for theBenchmark
% 1.87/0.61  % SZS output start Proof for theBenchmark
% 1.87/0.61  fof(f2143,plain,(
% 1.87/0.61    $false),
% 1.87/0.61    inference(avatar_sat_refutation,[],[f2104,f2134])).
% 1.87/0.61  fof(f2134,plain,(
% 1.87/0.61    ~spl8_18),
% 1.87/0.61    inference(avatar_contradiction_clause,[],[f2133])).
% 1.87/0.61  fof(f2133,plain,(
% 1.87/0.61    $false | ~spl8_18),
% 1.87/0.61    inference(global_subsumption,[],[f786,f1991,f802])).
% 1.87/0.61  fof(f802,plain,(
% 1.87/0.61    sK1 != k2_lattices(sK0,k6_lattices(sK0),sK1)),
% 1.87/0.61    inference(superposition,[],[f71,f331])).
% 1.87/0.61  fof(f331,plain,(
% 1.87/0.61    k4_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k6_lattices(sK0),sK1)),
% 1.87/0.61    inference(resolution,[],[f174,f130])).
% 1.87/0.61  fof(f130,plain,(
% 1.87/0.61    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 1.87/0.61    inference(subsumption_resolution,[],[f129,f66])).
% 1.87/0.61  fof(f66,plain,(
% 1.87/0.61    ~v2_struct_0(sK0)),
% 1.87/0.61    inference(cnf_transformation,[],[f48])).
% 1.87/0.61  fof(f48,plain,(
% 1.87/0.61    (sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v14_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f47,f46])).
% 1.87/0.61  fof(f46,plain,(
% 1.87/0.61    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k4_lattices(sK0,k6_lattices(sK0),X1) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v14_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f47,plain,(
% 1.87/0.61    ? [X1] : (k4_lattices(sK0,k6_lattices(sK0),X1) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) => (sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f18,plain,(
% 1.87/0.61    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.87/0.61    inference(flattening,[],[f17])).
% 1.87/0.61  fof(f17,plain,(
% 1.87/0.61    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f16])).
% 1.87/0.61  fof(f16,negated_conjecture,(
% 1.87/0.61    ~! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 1.87/0.61    inference(negated_conjecture,[],[f15])).
% 1.87/0.61  fof(f15,conjecture,(
% 1.87/0.61    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).
% 1.87/0.61  fof(f129,plain,(
% 1.87/0.61    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.87/0.61    inference(resolution,[],[f84,f110])).
% 1.87/0.61  fof(f110,plain,(
% 1.87/0.61    l2_lattices(sK0)),
% 1.87/0.61    inference(resolution,[],[f73,f69])).
% 1.87/0.61  fof(f69,plain,(
% 1.87/0.61    l3_lattices(sK0)),
% 1.87/0.61    inference(cnf_transformation,[],[f48])).
% 1.87/0.61  fof(f73,plain,(
% 1.87/0.61    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f19])).
% 1.87/0.61  fof(f19,plain,(
% 1.87/0.61    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f7])).
% 1.87/0.61  fof(f7,axiom,(
% 1.87/0.61    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.87/0.61  fof(f84,plain,(
% 1.87/0.61    ( ! [X0] : (~l2_lattices(X0) | m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f29])).
% 1.87/0.61  fof(f29,plain,(
% 1.87/0.61    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(flattening,[],[f28])).
% 1.87/0.61  fof(f28,plain,(
% 1.87/0.61    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f6])).
% 1.87/0.61  fof(f6,axiom,(
% 1.87/0.61    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).
% 1.87/0.61  fof(f174,plain,(
% 1.87/0.61    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK1) = k4_lattices(sK0,X0,sK1)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f173,f66])).
% 1.87/0.61  fof(f173,plain,(
% 1.87/0.61    ( ! [X0] : (k2_lattices(sK0,X0,sK1) = k4_lattices(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f172,f119])).
% 1.87/0.61  fof(f119,plain,(
% 1.87/0.61    v6_lattices(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f118,f69])).
% 1.87/0.61  fof(f118,plain,(
% 1.87/0.61    v6_lattices(sK0) | ~l3_lattices(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f117,f66])).
% 1.87/0.61  fof(f117,plain,(
% 1.87/0.61    v6_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.87/0.61    inference(resolution,[],[f77,f67])).
% 1.87/0.61  fof(f67,plain,(
% 1.87/0.61    v10_lattices(sK0)),
% 1.87/0.61    inference(cnf_transformation,[],[f48])).
% 1.87/0.61  fof(f77,plain,(
% 1.87/0.61    ( ! [X0] : (~v10_lattices(X0) | v6_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f21])).
% 1.87/0.61  fof(f21,plain,(
% 1.87/0.61    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.87/0.61    inference(flattening,[],[f20])).
% 1.87/0.61  fof(f20,plain,(
% 1.87/0.61    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f1])).
% 1.87/0.61  fof(f1,axiom,(
% 1.87/0.61    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 1.87/0.61  fof(f172,plain,(
% 1.87/0.61    ( ! [X0] : (k2_lattices(sK0,X0,sK1) = k4_lattices(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f171,f109])).
% 1.87/0.61  fof(f109,plain,(
% 1.87/0.61    l1_lattices(sK0)),
% 1.87/0.61    inference(resolution,[],[f72,f69])).
% 1.87/0.61  fof(f72,plain,(
% 1.87/0.61    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f19])).
% 1.87/0.61  fof(f171,plain,(
% 1.87/0.61    ( ! [X0] : (k2_lattices(sK0,X0,sK1) = k4_lattices(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(resolution,[],[f101,f70])).
% 1.87/0.61  fof(f70,plain,(
% 1.87/0.61    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.87/0.61    inference(cnf_transformation,[],[f48])).
% 1.87/0.61  fof(f101,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f41])).
% 1.87/0.61  fof(f41,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(flattening,[],[f40])).
% 1.87/0.61  fof(f40,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f8])).
% 1.87/0.61  fof(f8,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 1.87/0.61  fof(f71,plain,(
% 1.87/0.61    sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 1.87/0.61    inference(cnf_transformation,[],[f48])).
% 1.87/0.61  fof(f1991,plain,(
% 1.87/0.61    r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1))),
% 1.87/0.61    inference(forward_demodulation,[],[f1990,f372])).
% 1.87/0.61  fof(f372,plain,(
% 1.87/0.61    sK1 = k2_lattices(sK0,sK1,sK1)),
% 1.87/0.61    inference(subsumption_resolution,[],[f371,f66])).
% 1.87/0.61  fof(f371,plain,(
% 1.87/0.61    sK1 = k2_lattices(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f370,f125])).
% 1.87/0.61  fof(f125,plain,(
% 1.87/0.61    v8_lattices(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f124,f69])).
% 1.87/0.61  fof(f124,plain,(
% 1.87/0.61    v8_lattices(sK0) | ~l3_lattices(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f123,f66])).
% 1.87/0.61  fof(f123,plain,(
% 1.87/0.61    v8_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.87/0.61    inference(resolution,[],[f79,f67])).
% 1.87/0.61  fof(f79,plain,(
% 1.87/0.61    ( ! [X0] : (~v10_lattices(X0) | v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f21])).
% 1.87/0.61  fof(f370,plain,(
% 1.87/0.61    sK1 = k2_lattices(sK0,sK1,sK1) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f369,f128])).
% 1.87/0.61  fof(f128,plain,(
% 1.87/0.61    v9_lattices(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f127,f69])).
% 1.87/0.61  fof(f127,plain,(
% 1.87/0.61    v9_lattices(sK0) | ~l3_lattices(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f126,f66])).
% 1.87/0.61  fof(f126,plain,(
% 1.87/0.61    v9_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.87/0.61    inference(resolution,[],[f80,f67])).
% 1.87/0.61  fof(f80,plain,(
% 1.87/0.61    ( ! [X0] : (~v10_lattices(X0) | v9_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f21])).
% 1.87/0.61  fof(f369,plain,(
% 1.87/0.61    sK1 = k2_lattices(sK0,sK1,sK1) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f368,f69])).
% 1.87/0.61  fof(f368,plain,(
% 1.87/0.61    sK1 = k2_lattices(sK0,sK1,sK1) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f359,f70])).
% 1.87/0.61  fof(f359,plain,(
% 1.87/0.61    sK1 = k2_lattices(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(duplicate_literal_removal,[],[f356])).
% 1.87/0.61  fof(f356,plain,(
% 1.87/0.61    sK1 = k2_lattices(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(resolution,[],[f318,f94])).
% 1.87/0.61  fof(f94,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f59])).
% 1.87/0.61  fof(f59,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(nnf_transformation,[],[f35])).
% 1.87/0.61  fof(f35,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(flattening,[],[f34])).
% 1.87/0.61  fof(f34,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f11])).
% 1.87/0.61  fof(f11,axiom,(
% 1.87/0.61    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 1.87/0.61  fof(f318,plain,(
% 1.87/0.61    r1_lattices(sK0,sK1,sK1)),
% 1.87/0.61    inference(subsumption_resolution,[],[f317,f66])).
% 1.87/0.61  fof(f317,plain,(
% 1.87/0.61    r1_lattices(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f316,f119])).
% 1.87/0.61  fof(f316,plain,(
% 1.87/0.61    r1_lattices(sK0,sK1,sK1) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f315,f125])).
% 1.87/0.61  fof(f315,plain,(
% 1.87/0.61    r1_lattices(sK0,sK1,sK1) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f314,f128])).
% 1.87/0.61  fof(f314,plain,(
% 1.87/0.61    r1_lattices(sK0,sK1,sK1) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f313,f69])).
% 1.87/0.61  fof(f313,plain,(
% 1.87/0.61    r1_lattices(sK0,sK1,sK1) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f312,f70])).
% 1.87/0.61  fof(f312,plain,(
% 1.87/0.61    r1_lattices(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(duplicate_literal_removal,[],[f311])).
% 1.87/0.61  fof(f311,plain,(
% 1.87/0.61    r1_lattices(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(resolution,[],[f303,f103])).
% 1.87/0.61  fof(f103,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f65])).
% 1.87/0.61  fof(f65,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(nnf_transformation,[],[f45])).
% 1.87/0.61  fof(f45,plain,(
% 1.87/0.61    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(flattening,[],[f44])).
% 1.87/0.61  fof(f44,plain,(
% 1.87/0.61    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f9])).
% 1.87/0.61  fof(f9,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.87/0.61  fof(f303,plain,(
% 1.87/0.61    r3_lattices(sK0,sK1,sK1)),
% 1.87/0.61    inference(resolution,[],[f166,f70])).
% 1.87/0.61  fof(f166,plain,(
% 1.87/0.61    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattices(sK0,X0,X0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f165,f66])).
% 1.87/0.61  fof(f165,plain,(
% 1.87/0.61    ( ! [X0] : (r3_lattices(sK0,X0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f164,f119])).
% 1.87/0.61  fof(f164,plain,(
% 1.87/0.61    ( ! [X0] : (r3_lattices(sK0,X0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f163,f125])).
% 1.87/0.61  fof(f163,plain,(
% 1.87/0.61    ( ! [X0] : (r3_lattices(sK0,X0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f162,f128])).
% 1.87/0.61  fof(f162,plain,(
% 1.87/0.61    ( ! [X0] : (r3_lattices(sK0,X0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f161,f69])).
% 1.87/0.61  fof(f161,plain,(
% 1.87/0.61    ( ! [X0] : (r3_lattices(sK0,X0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(resolution,[],[f102,f70])).
% 1.87/0.61  fof(f102,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | r3_lattices(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f43])).
% 1.87/0.61  fof(f43,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(flattening,[],[f42])).
% 1.87/0.61  fof(f42,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f10])).
% 1.87/0.61  fof(f10,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => r3_lattices(X0,X1,X1))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).
% 1.87/0.61  fof(f1990,plain,(
% 1.87/0.61    r1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k2_lattices(sK0,k6_lattices(sK0),sK1))),
% 1.87/0.61    inference(forward_demodulation,[],[f1979,f372])).
% 1.87/0.61  fof(f1979,plain,(
% 1.87/0.61    r1_lattices(sK0,k2_lattices(sK0,sK1,k2_lattices(sK0,sK1,sK1)),k2_lattices(sK0,k6_lattices(sK0),k2_lattices(sK0,sK1,sK1)))),
% 1.87/0.61    inference(resolution,[],[f829,f307])).
% 1.87/0.61  fof(f307,plain,(
% 1.87/0.61    m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0))),
% 1.87/0.61    inference(resolution,[],[f147,f70])).
% 1.87/0.61  fof(f147,plain,(
% 1.87/0.61    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k2_lattices(sK0,X0,sK1),u1_struct_0(sK0))) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f146,f66])).
% 1.87/0.61  fof(f146,plain,(
% 1.87/0.61    ( ! [X0] : (m1_subset_1(k2_lattices(sK0,X0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f145,f109])).
% 1.87/0.61  fof(f145,plain,(
% 1.87/0.61    ( ! [X0] : (m1_subset_1(k2_lattices(sK0,X0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(resolution,[],[f100,f70])).
% 1.87/0.61  fof(f100,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f39])).
% 1.87/0.61  fof(f39,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(flattening,[],[f38])).
% 1.87/0.61  fof(f38,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f5])).
% 1.87/0.61  fof(f5,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).
% 1.87/0.61  fof(f829,plain,(
% 1.87/0.61    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0))) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f828,f66])).
% 1.87/0.61  fof(f828,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f827,f122])).
% 1.87/0.61  fof(f122,plain,(
% 1.87/0.61    v7_lattices(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f121,f69])).
% 1.87/0.61  fof(f121,plain,(
% 1.87/0.61    v7_lattices(sK0) | ~l3_lattices(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f120,f66])).
% 1.87/0.61  fof(f120,plain,(
% 1.87/0.61    v7_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.87/0.61    inference(resolution,[],[f78,f67])).
% 1.87/0.61  fof(f78,plain,(
% 1.87/0.61    ( ! [X0] : (~v10_lattices(X0) | v7_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f21])).
% 1.87/0.61  fof(f827,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v7_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f826,f125])).
% 1.87/0.61  fof(f826,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v7_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f825,f128])).
% 1.87/0.61  fof(f825,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v7_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f824,f69])).
% 1.87/0.61  fof(f824,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v7_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f823,f70])).
% 1.87/0.61  fof(f823,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v7_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f819,f130])).
% 1.87/0.61  fof(f819,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k6_lattices(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v7_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(resolution,[],[f810,f82])).
% 1.87/0.61  fof(f82,plain,(
% 1.87/0.61    ( ! [X2,X0,X3,X1] : (~r1_lattices(X0,X1,X2) | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f25])).
% 1.87/0.61  fof(f25,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(flattening,[],[f24])).
% 1.87/0.61  fof(f24,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f14])).
% 1.87/0.61  fof(f14,axiom,(
% 1.87/0.61    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).
% 1.87/0.61  fof(f810,plain,(
% 1.87/0.61    r1_lattices(sK0,sK1,k6_lattices(sK0))),
% 1.87/0.61    inference(forward_demodulation,[],[f809,f139])).
% 1.87/0.61  fof(f139,plain,(
% 1.87/0.61    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 1.87/0.61    inference(subsumption_resolution,[],[f138,f66])).
% 1.87/0.61  fof(f138,plain,(
% 1.87/0.61    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f137,f110])).
% 1.87/0.61  fof(f137,plain,(
% 1.87/0.61    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f136,f68])).
% 1.87/0.61  fof(f68,plain,(
% 1.87/0.61    v14_lattices(sK0)),
% 1.87/0.61    inference(cnf_transformation,[],[f48])).
% 1.87/0.61  fof(f136,plain,(
% 1.87/0.61    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) | ~v14_lattices(sK0) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 1.87/0.61    inference(resolution,[],[f107,f70])).
% 1.87/0.61  fof(f107,plain,(
% 1.87/0.61    ( ! [X0,X3] : (~m1_subset_1(X3,u1_struct_0(X0)) | k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f105,f84])).
% 1.87/0.61  fof(f105,plain,(
% 1.87/0.61    ( ! [X0,X3] : (k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.87/0.61    inference(equality_resolution,[],[f86])).
% 1.87/0.61  fof(f86,plain,(
% 1.87/0.61    ( ! [X0,X3,X1] : (k1_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k6_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f52])).
% 1.87/0.61  fof(f52,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ((k1_lattices(X0,sK2(X0,X1),X1) != X1 | k1_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k1_lattices(X0,X3,X1) = X1 & k1_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).
% 1.87/0.61  fof(f51,plain,(
% 1.87/0.61    ! [X1,X0] : (? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k1_lattices(X0,sK2(X0,X1),X1) != X1 | k1_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f50,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k1_lattices(X0,X3,X1) = X1 & k1_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(rectify,[],[f49])).
% 1.87/0.61  fof(f49,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(nnf_transformation,[],[f31])).
% 1.87/0.61  fof(f31,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(flattening,[],[f30])).
% 1.87/0.61  fof(f30,plain,(
% 1.87/0.61    ! [X0] : ((! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f2])).
% 1.87/0.61  fof(f2,axiom,(
% 1.87/0.61    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k6_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1))))))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattices)).
% 1.87/0.61  fof(f809,plain,(
% 1.87/0.61    r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k6_lattices(sK0)))),
% 1.87/0.61    inference(forward_demodulation,[],[f805,f372])).
% 1.87/0.61  fof(f805,plain,(
% 1.87/0.61    r1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k6_lattices(sK0)))),
% 1.87/0.61    inference(resolution,[],[f284,f307])).
% 1.87/0.61  fof(f284,plain,(
% 1.87/0.61    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0)))) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f283,f66])).
% 1.87/0.61  fof(f283,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f282,f116])).
% 1.87/0.61  fof(f116,plain,(
% 1.87/0.61    v5_lattices(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f115,f69])).
% 1.87/0.61  fof(f115,plain,(
% 1.87/0.61    v5_lattices(sK0) | ~l3_lattices(sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f114,f66])).
% 1.87/0.61  fof(f114,plain,(
% 1.87/0.61    v5_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.87/0.61    inference(resolution,[],[f76,f67])).
% 1.87/0.61  fof(f76,plain,(
% 1.87/0.61    ( ! [X0] : (~v10_lattices(X0) | v5_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f21])).
% 1.87/0.61  fof(f282,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f281,f119])).
% 1.87/0.61  fof(f281,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~v5_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f280,f125])).
% 1.87/0.61  fof(f280,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~v5_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f279,f128])).
% 1.87/0.61  fof(f279,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~v5_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f268,f69])).
% 1.87/0.61  fof(f268,plain,(
% 1.87/0.61    ( ! [X0] : (r1_lattices(sK0,X0,k1_lattices(sK0,X0,k6_lattices(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~v5_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.61    inference(resolution,[],[f130,f83])).
% 1.87/0.61  fof(f83,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | v2_struct_0(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f27])).
% 1.87/0.61  fof(f27,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.61    inference(flattening,[],[f26])).
% 1.87/0.61  fof(f26,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | v2_struct_0(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f12])).
% 1.87/0.62  fof(f12,axiom,(
% 1.87/0.62    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)))))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_lattices)).
% 1.87/0.62  fof(f786,plain,(
% 1.87/0.62    sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1) | ~r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1)) | ~spl8_18),
% 1.87/0.62    inference(subsumption_resolution,[],[f785,f66])).
% 1.87/0.62  fof(f785,plain,(
% 1.87/0.62    sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1) | ~r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1)) | v2_struct_0(sK0) | ~spl8_18),
% 1.87/0.62    inference(subsumption_resolution,[],[f784,f113])).
% 1.87/0.62  fof(f113,plain,(
% 1.87/0.62    v4_lattices(sK0)),
% 1.87/0.62    inference(subsumption_resolution,[],[f112,f69])).
% 1.87/0.62  fof(f112,plain,(
% 1.87/0.62    v4_lattices(sK0) | ~l3_lattices(sK0)),
% 1.87/0.62    inference(subsumption_resolution,[],[f111,f66])).
% 1.87/0.62  fof(f111,plain,(
% 1.87/0.62    v4_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.87/0.62    inference(resolution,[],[f75,f67])).
% 1.87/0.62  fof(f75,plain,(
% 1.87/0.62    ( ! [X0] : (~v10_lattices(X0) | v4_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f21])).
% 1.87/0.62  fof(f784,plain,(
% 1.87/0.62    sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1) | ~r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1)) | ~v4_lattices(sK0) | v2_struct_0(sK0) | ~spl8_18),
% 1.87/0.62    inference(subsumption_resolution,[],[f783,f110])).
% 1.87/0.62  fof(f783,plain,(
% 1.87/0.62    sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1) | ~r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0) | ~spl8_18),
% 1.87/0.62    inference(subsumption_resolution,[],[f782,f70])).
% 1.87/0.62  fof(f782,plain,(
% 1.87/0.62    sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1) | ~r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0) | ~spl8_18),
% 1.87/0.62    inference(subsumption_resolution,[],[f759,f309])).
% 1.87/0.62  fof(f309,plain,(
% 1.87/0.62    m1_subset_1(k2_lattices(sK0,k6_lattices(sK0),sK1),u1_struct_0(sK0))),
% 1.87/0.62    inference(resolution,[],[f147,f130])).
% 1.87/0.62  fof(f759,plain,(
% 1.87/0.62    sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1) | ~r1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1)) | ~m1_subset_1(k2_lattices(sK0,k6_lattices(sK0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0) | ~spl8_18),
% 1.87/0.62    inference(resolution,[],[f546,f81])).
% 1.87/0.62  fof(f81,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~r1_lattices(X0,X2,X1) | X1 = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f23])).
% 1.87/0.62  fof(f23,plain,(
% 1.87/0.62    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.62    inference(flattening,[],[f22])).
% 1.87/0.62  fof(f22,plain,(
% 1.87/0.62    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.87/0.62    inference(ennf_transformation,[],[f13])).
% 1.87/0.62  fof(f13,axiom,(
% 1.87/0.62    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).
% 1.87/0.62  fof(f546,plain,(
% 1.87/0.62    r1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1) | ~spl8_18),
% 1.87/0.62    inference(avatar_component_clause,[],[f544])).
% 1.87/0.62  fof(f544,plain,(
% 1.87/0.62    spl8_18 <=> r1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.87/0.62  fof(f2104,plain,(
% 1.87/0.62    spl8_18),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f2103])).
% 1.87/0.62  fof(f2103,plain,(
% 1.87/0.62    $false | spl8_18),
% 1.87/0.62    inference(global_subsumption,[],[f721,f545])).
% 1.87/0.62  fof(f545,plain,(
% 1.87/0.62    ~r1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1) | spl8_18),
% 1.87/0.62    inference(avatar_component_clause,[],[f544])).
% 1.87/0.62  fof(f721,plain,(
% 1.87/0.62    r1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1)),
% 1.87/0.62    inference(forward_demodulation,[],[f707,f327])).
% 1.87/0.62  fof(f327,plain,(
% 1.87/0.62    sK1 = k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1)),
% 1.87/0.62    inference(resolution,[],[f170,f130])).
% 1.87/0.62  fof(f170,plain,(
% 1.87/0.62    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k2_lattices(sK0,X0,sK1),sK1)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f169,f66])).
% 1.87/0.62  fof(f169,plain,(
% 1.87/0.62    ( ! [X0] : (sK1 = k1_lattices(sK0,k2_lattices(sK0,X0,sK1),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f168,f69])).
% 1.87/0.62  fof(f168,plain,(
% 1.87/0.62    ( ! [X0] : (sK1 = k1_lattices(sK0,k2_lattices(sK0,X0,sK1),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f167,f125])).
% 1.87/0.62  fof(f167,plain,(
% 1.87/0.62    ( ! [X0] : (sK1 = k1_lattices(sK0,k2_lattices(sK0,X0,sK1),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.62    inference(resolution,[],[f96,f70])).
% 1.87/0.62  fof(f96,plain,(
% 1.87/0.62    ( ! [X4,X0,X3] : (~m1_subset_1(X4,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f64])).
% 1.87/0.62  fof(f64,plain,(
% 1.87/0.62    ! [X0] : (((v8_lattices(X0) | ((sK7(X0) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0)) & m1_subset_1(sK7(X0),u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f61,f63,f62])).
% 1.87/0.62  fof(f62,plain,(
% 1.87/0.62    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 1.87/0.62    introduced(choice_axiom,[])).
% 1.87/0.62  fof(f63,plain,(
% 1.87/0.62    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK7(X0) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0)) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 1.87/0.62    introduced(choice_axiom,[])).
% 1.87/0.62  fof(f61,plain,(
% 1.87/0.62    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.62    inference(rectify,[],[f60])).
% 1.87/0.62  fof(f60,plain,(
% 1.87/0.62    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.62    inference(nnf_transformation,[],[f37])).
% 1.87/0.62  fof(f37,plain,(
% 1.87/0.62    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.87/0.62    inference(flattening,[],[f36])).
% 1.87/0.62  fof(f36,plain,(
% 1.87/0.62    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.87/0.62    inference(ennf_transformation,[],[f4])).
% 1.87/0.62  fof(f4,axiom,(
% 1.87/0.62    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).
% 1.87/0.62  fof(f707,plain,(
% 1.87/0.62    r1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1))),
% 1.87/0.62    inference(resolution,[],[f309,f186])).
% 1.87/0.62  fof(f186,plain,(
% 1.87/0.62    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1))) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f185,f66])).
% 1.87/0.62  fof(f185,plain,(
% 1.87/0.62    ( ! [X0] : (r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f184,f116])).
% 1.87/0.62  fof(f184,plain,(
% 1.87/0.62    ( ! [X0] : (r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f183,f119])).
% 1.87/0.62  fof(f183,plain,(
% 1.87/0.62    ( ! [X0] : (r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~v5_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f182,f125])).
% 1.87/0.62  fof(f182,plain,(
% 1.87/0.62    ( ! [X0] : (r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~v5_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f181,f128])).
% 1.87/0.62  fof(f181,plain,(
% 1.87/0.62    ( ! [X0] : (r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~v5_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f180,f69])).
% 1.87/0.62  fof(f180,plain,(
% 1.87/0.62    ( ! [X0] : (r1_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~v5_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.87/0.62    inference(resolution,[],[f83,f70])).
% 1.87/0.62  % SZS output end Proof for theBenchmark
% 1.87/0.62  % (15445)------------------------------
% 1.87/0.62  % (15445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (15445)Termination reason: Refutation
% 1.87/0.62  
% 1.87/0.62  % (15445)Memory used [KB]: 11769
% 1.87/0.62  % (15445)Time elapsed: 0.190 s
% 1.87/0.62  % (15445)------------------------------
% 1.87/0.62  % (15445)------------------------------
% 1.87/0.62  % (15434)Success in time 0.256 s
%------------------------------------------------------------------------------

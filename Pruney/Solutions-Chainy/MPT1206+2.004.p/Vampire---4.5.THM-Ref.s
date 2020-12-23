%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:40 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 358 expanded)
%              Number of leaves         :   11 ( 105 expanded)
%              Depth                    :   47
%              Number of atoms          :  463 (1965 expanded)
%              Number of equality atoms :   68 ( 320 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(subsumption_resolution,[],[f138,f38])).

fof(f38,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v13_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v13_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).

fof(f138,plain,(
    ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f137,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f137,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f136,f36])).

fof(f36,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f136,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f135,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
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
    inference(pure_predicate_removal,[],[f1])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f135,plain,(
    ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f134,f38])).

fof(f134,plain,
    ( ~ v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f133,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f133,plain,
    ( ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f132,f35])).

fof(f132,plain,
    ( ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f131,f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f131,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f130,f38])).

fof(f130,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f129,f41])).

fof(f129,plain,
    ( ~ l1_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f128,f35])).

fof(f128,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f127,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f127,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f125,f40])).

fof(f40,plain,(
    k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f125,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f124,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f124,plain,(
    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f123,f38])).

fof(f123,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f122,f42])).

fof(f42,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f122,plain,
    ( ~ l2_lattices(sK0)
    | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f121,f38])).

fof(f121,plain,
    ( ~ l2_lattices(sK0)
    | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f120,f41])).

fof(f120,plain,
    ( ~ l1_lattices(sK0)
    | ~ l2_lattices(sK0)
    | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f119,f35])).

fof(f119,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ l2_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f118,f51])).

fof(f118,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ l2_lattices(sK0) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l2_lattices(sK0) ),
    inference(resolution,[],[f114,f81])).

fof(f81,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l2_lattices(sK0) ),
    inference(subsumption_resolution,[],[f80,f35])).

fof(f80,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f79,f39])).

fof(f79,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,
    ( sK1 != sK1
    | r1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f53,f76])).

fof(f76,plain,(
    sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f75,f35])).

fof(f75,plain,
    ( sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f74,f36])).

fof(f74,plain,
    ( sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f73,f37])).

fof(f37,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,
    ( sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f72,f38])).

fof(f72,plain,
    ( sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f70,f39])).

fof(f70,plain,
    ( sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f69,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k5_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).

fof(f69,plain,(
    k1_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f68,f38])).

fof(f68,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f67,f41])).

fof(f67,plain,
    ( ~ l1_lattices(sK0)
    | k1_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f66,f35])).

fof(f66,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f62,f51])).

fof(f62,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,X0,sK1) = k3_lattices(sK0,X0,sK1) ) ),
    inference(resolution,[],[f61,f39])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f60,f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f59,f35])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f58,f36])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | k1_lattices(X1,X0,X2) = k3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | k1_lattices(X1,X0,X2) = k3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f56,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f54,f42])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(f114,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK0,X0,sK1)
      | k2_lattices(sK0,X0,sK1) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f113,f39])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,X0) = X1
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f112,f35])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,X0) = X1
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f111,f38])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k2_lattices(sK0,X1,X0) = X1
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f110,f36])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f109,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f48,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:11:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (10058)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (10050)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (10050)Refutation not found, incomplete strategy% (10050)------------------------------
% 0.21/0.50  % (10050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10050)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (10050)Memory used [KB]: 10618
% 0.21/0.50  % (10050)Time elapsed: 0.073 s
% 0.21/0.50  % (10050)------------------------------
% 0.21/0.50  % (10050)------------------------------
% 0.21/0.51  % (10058)Refutation not found, incomplete strategy% (10058)------------------------------
% 0.21/0.51  % (10058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10058)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10058)Memory used [KB]: 1663
% 0.21/0.51  % (10058)Time elapsed: 0.076 s
% 0.21/0.51  % (10058)------------------------------
% 0.21/0.51  % (10058)------------------------------
% 0.21/0.52  % (10044)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.52  % (10052)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (10052)Refutation not found, incomplete strategy% (10052)------------------------------
% 0.21/0.52  % (10052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10052)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10052)Memory used [KB]: 10618
% 0.21/0.52  % (10052)Time elapsed: 0.097 s
% 0.21/0.52  % (10052)------------------------------
% 0.21/0.52  % (10052)------------------------------
% 1.33/0.53  % (10049)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.53  % (10045)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.33/0.53  % (10047)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.33/0.53  % (10049)Refutation not found, incomplete strategy% (10049)------------------------------
% 1.33/0.53  % (10049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (10049)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (10049)Memory used [KB]: 6140
% 1.33/0.53  % (10049)Time elapsed: 0.113 s
% 1.33/0.53  % (10049)------------------------------
% 1.33/0.53  % (10049)------------------------------
% 1.33/0.53  % (10045)Refutation not found, incomplete strategy% (10045)------------------------------
% 1.33/0.53  % (10045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (10045)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (10045)Memory used [KB]: 10618
% 1.33/0.53  % (10045)Time elapsed: 0.113 s
% 1.33/0.53  % (10045)------------------------------
% 1.33/0.53  % (10045)------------------------------
% 1.33/0.53  % (10063)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.33/0.53  % (10043)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.33/0.53  % (10061)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.33/0.53  % (10065)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.33/0.54  % (10065)Refutation not found, incomplete strategy% (10065)------------------------------
% 1.33/0.54  % (10065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (10065)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (10065)Memory used [KB]: 10618
% 1.33/0.54  % (10065)Time elapsed: 0.116 s
% 1.33/0.54  % (10065)------------------------------
% 1.33/0.54  % (10065)------------------------------
% 1.33/0.54  % (10061)Refutation found. Thanks to Tanya!
% 1.33/0.54  % SZS status Theorem for theBenchmark
% 1.33/0.54  % SZS output start Proof for theBenchmark
% 1.33/0.54  fof(f139,plain,(
% 1.33/0.54    $false),
% 1.33/0.54    inference(subsumption_resolution,[],[f138,f38])).
% 1.33/0.54  fof(f38,plain,(
% 1.33/0.54    l3_lattices(sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f32])).
% 1.33/0.54  fof(f32,plain,(
% 1.33/0.54    (k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v13_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f31,f30])).
% 1.33/0.54  fof(f30,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v13_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f31,plain,(
% 1.33/0.54    ? [X1] : (k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1) & m1_subset_1(X1,u1_struct_0(sK0))) => (k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f14,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f13])).
% 1.33/0.54  fof(f13,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f10])).
% 1.33/0.54  fof(f10,negated_conjecture,(
% 1.33/0.54    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 1.33/0.54    inference(negated_conjecture,[],[f9])).
% 1.33/0.54  fof(f9,conjecture,(
% 1.33/0.54    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).
% 1.33/0.54  fof(f138,plain,(
% 1.33/0.54    ~l3_lattices(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f137,f35])).
% 1.33/0.54  fof(f35,plain,(
% 1.33/0.54    ~v2_struct_0(sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f32])).
% 1.33/0.54  fof(f137,plain,(
% 1.33/0.54    v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f136,f36])).
% 1.33/0.54  fof(f36,plain,(
% 1.33/0.54    v10_lattices(sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f32])).
% 1.33/0.54  fof(f136,plain,(
% 1.33/0.54    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.33/0.54    inference(resolution,[],[f135,f45])).
% 1.33/0.54  fof(f45,plain,(
% 1.33/0.54    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f17])).
% 1.33/0.54  fof(f17,plain,(
% 1.33/0.54    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.33/0.54    inference(flattening,[],[f16])).
% 1.33/0.54  fof(f16,plain,(
% 1.33/0.54    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f12])).
% 1.33/0.54  fof(f12,plain,(
% 1.33/0.54    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.33/0.54    inference(pure_predicate_removal,[],[f11])).
% 1.33/0.54  fof(f11,plain,(
% 1.33/0.54    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.33/0.54    inference(pure_predicate_removal,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 1.33/0.54  fof(f135,plain,(
% 1.33/0.54    ~v6_lattices(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f134,f38])).
% 1.33/0.54  fof(f134,plain,(
% 1.33/0.54    ~v6_lattices(sK0) | ~l3_lattices(sK0)),
% 1.33/0.54    inference(resolution,[],[f133,f41])).
% 1.33/0.54  fof(f41,plain,(
% 1.33/0.54    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f15,plain,(
% 1.33/0.54    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f4])).
% 1.33/0.54  fof(f4,axiom,(
% 1.33/0.54    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.33/0.54  fof(f133,plain,(
% 1.33/0.54    ~l1_lattices(sK0) | ~v6_lattices(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f132,f35])).
% 1.33/0.54  fof(f132,plain,(
% 1.33/0.54    ~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(resolution,[],[f131,f51])).
% 1.33/0.54  fof(f51,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f23])).
% 1.33/0.54  fof(f23,plain,(
% 1.33/0.54    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f22])).
% 1.33/0.54  fof(f22,plain,(
% 1.33/0.54    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f3])).
% 1.33/0.54  fof(f3,axiom,(
% 1.33/0.54    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 1.33/0.54  fof(f131,plain,(
% 1.33/0.54    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v6_lattices(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f130,f38])).
% 1.33/0.54  fof(f130,plain,(
% 1.33/0.54    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~l3_lattices(sK0)),
% 1.33/0.54    inference(resolution,[],[f129,f41])).
% 1.33/0.54  fof(f129,plain,(
% 1.33/0.54    ~l1_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v6_lattices(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f128,f35])).
% 1.33/0.54  fof(f128,plain,(
% 1.33/0.54    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f127,f39])).
% 1.33/0.54  fof(f39,plain,(
% 1.33/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.33/0.54    inference(cnf_transformation,[],[f32])).
% 1.33/0.54  fof(f127,plain,(
% 1.33/0.54    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f125,f40])).
% 1.33/0.54  fof(f40,plain,(
% 1.33/0.54    k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1)),
% 1.33/0.54    inference(cnf_transformation,[],[f32])).
% 1.33/0.54  fof(f125,plain,(
% 1.33/0.54    k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(superposition,[],[f124,f55])).
% 1.33/0.54  fof(f55,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f29])).
% 1.33/0.54  fof(f29,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f28])).
% 1.33/0.54  fof(f28,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f6])).
% 1.33/0.54  fof(f6,axiom,(
% 1.33/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 1.33/0.54  fof(f124,plain,(
% 1.33/0.54    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)),
% 1.33/0.54    inference(subsumption_resolution,[],[f123,f38])).
% 1.33/0.54  fof(f123,plain,(
% 1.33/0.54    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1) | ~l3_lattices(sK0)),
% 1.33/0.54    inference(resolution,[],[f122,f42])).
% 1.33/0.54  fof(f42,plain,(
% 1.33/0.54    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f122,plain,(
% 1.33/0.54    ~l2_lattices(sK0) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)),
% 1.33/0.54    inference(subsumption_resolution,[],[f121,f38])).
% 1.33/0.54  fof(f121,plain,(
% 1.33/0.54    ~l2_lattices(sK0) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1) | ~l3_lattices(sK0)),
% 1.33/0.54    inference(resolution,[],[f120,f41])).
% 1.33/0.54  fof(f120,plain,(
% 1.33/0.54    ~l1_lattices(sK0) | ~l2_lattices(sK0) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)),
% 1.33/0.54    inference(subsumption_resolution,[],[f119,f35])).
% 1.33/0.54  fof(f119,plain,(
% 1.33/0.54    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1) | ~l2_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(resolution,[],[f118,f51])).
% 1.33/0.54  fof(f118,plain,(
% 1.33/0.54    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1) | ~l2_lattices(sK0)),
% 1.33/0.54    inference(duplicate_literal_removal,[],[f117])).
% 1.33/0.54  fof(f117,plain,(
% 1.33/0.54    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l2_lattices(sK0)),
% 1.33/0.54    inference(resolution,[],[f114,f81])).
% 1.33/0.54  fof(f81,plain,(
% 1.33/0.54    r1_lattices(sK0,k5_lattices(sK0),sK1) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l2_lattices(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f80,f35])).
% 1.33/0.54  fof(f80,plain,(
% 1.33/0.54    r1_lattices(sK0,k5_lattices(sK0),sK1) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f79,f39])).
% 1.33/0.54  fof(f79,plain,(
% 1.33/0.54    r1_lattices(sK0,k5_lattices(sK0),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(trivial_inequality_removal,[],[f78])).
% 1.33/0.54  fof(f78,plain,(
% 1.33/0.54    sK1 != sK1 | r1_lattices(sK0,k5_lattices(sK0),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(superposition,[],[f53,f76])).
% 1.33/0.54  fof(f76,plain,(
% 1.33/0.54    sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)),
% 1.33/0.54    inference(subsumption_resolution,[],[f75,f35])).
% 1.33/0.54  fof(f75,plain,(
% 1.33/0.54    sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) | v2_struct_0(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f74,f36])).
% 1.33/0.54  fof(f74,plain,(
% 1.33/0.54    sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f73,f37])).
% 1.33/0.54  fof(f37,plain,(
% 1.33/0.54    v13_lattices(sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f32])).
% 1.33/0.54  fof(f73,plain,(
% 1.33/0.54    sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f72,f38])).
% 1.33/0.54  fof(f72,plain,(
% 1.33/0.54    sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f70,f39])).
% 1.33/0.54  fof(f70,plain,(
% 1.33/0.54    sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(superposition,[],[f69,f50])).
% 1.33/0.54  fof(f50,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f21])).
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f20])).
% 1.33/0.54  fof(f20,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f8])).
% 1.33/0.54  fof(f8,axiom,(
% 1.33/0.54    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).
% 1.33/0.54  fof(f69,plain,(
% 1.33/0.54    k1_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 1.33/0.54    inference(subsumption_resolution,[],[f68,f38])).
% 1.33/0.54  fof(f68,plain,(
% 1.33/0.54    k1_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,k5_lattices(sK0),sK1) | ~l3_lattices(sK0)),
% 1.33/0.54    inference(resolution,[],[f67,f41])).
% 1.33/0.54  fof(f67,plain,(
% 1.33/0.54    ~l1_lattices(sK0) | k1_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 1.33/0.54    inference(subsumption_resolution,[],[f66,f35])).
% 1.33/0.54  fof(f66,plain,(
% 1.33/0.54    k1_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,k5_lattices(sK0),sK1) | ~l1_lattices(sK0) | v2_struct_0(sK0)),
% 1.33/0.54    inference(resolution,[],[f62,f51])).
% 1.33/0.54  fof(f62,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,X0,sK1) = k3_lattices(sK0,X0,sK1)) )),
% 1.33/0.54    inference(resolution,[],[f61,f39])).
% 1.33/0.54  fof(f61,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f60,f38])).
% 1.33/0.54  fof(f60,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f59,f35])).
% 1.33/0.54  fof(f59,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.33/0.54    inference(resolution,[],[f58,f36])).
% 1.33/0.54  fof(f58,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~v10_lattices(X1) | k1_lattices(X1,X0,X2) = k3_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.33/0.54    inference(duplicate_literal_removal,[],[f57])).
% 1.33/0.54  fof(f57,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | k1_lattices(X1,X0,X2) = k3_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.33/0.54    inference(resolution,[],[f56,f44])).
% 1.33/0.54  fof(f44,plain,(
% 1.33/0.54    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f17])).
% 1.33/0.54  fof(f56,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~v4_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.33/0.54    inference(resolution,[],[f54,f42])).
% 1.33/0.54  fof(f54,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f27])).
% 1.33/0.54  fof(f27,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f26])).
% 1.33/0.54  fof(f26,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f5])).
% 1.33/0.54  fof(f5,axiom,(
% 1.33/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 1.33/0.54  fof(f53,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) != X2 | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f34])).
% 1.33/0.54  fof(f34,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(nnf_transformation,[],[f25])).
% 1.33/0.54  fof(f25,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f24])).
% 1.33/0.54  fof(f24,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f2])).
% 1.33/0.54  fof(f2,axiom,(
% 1.33/0.54    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 1.33/0.54  fof(f114,plain,(
% 1.33/0.54    ( ! [X0] : (~r1_lattices(sK0,X0,sK1) | k2_lattices(sK0,X0,sK1) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.33/0.54    inference(resolution,[],[f113,f39])).
% 1.33/0.54  fof(f113,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = X1 | ~r1_lattices(sK0,X1,X0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f112,f35])).
% 1.33/0.54  fof(f112,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = X1 | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f111,f38])).
% 1.33/0.54  fof(f111,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k2_lattices(sK0,X1,X0) = X1 | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 1.33/0.54    inference(resolution,[],[f110,f36])).
% 1.33/0.54  fof(f110,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | v2_struct_0(X0) | ~r1_lattices(X0,X1,X2)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f109,f46])).
% 1.33/0.54  fof(f46,plain,(
% 1.33/0.54    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f17])).
% 1.33/0.54  fof(f109,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 1.33/0.54    inference(duplicate_literal_removal,[],[f108])).
% 1.33/0.54  fof(f108,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.33/0.54    inference(resolution,[],[f48,f47])).
% 1.33/0.54  fof(f47,plain,(
% 1.33/0.54    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f17])).
% 1.33/0.54  fof(f48,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f33])).
% 1.33/0.54  fof(f33,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(nnf_transformation,[],[f19])).
% 1.33/0.54  fof(f19,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f18])).
% 1.33/0.54  fof(f18,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f7])).
% 1.33/0.54  fof(f7,axiom,(
% 1.33/0.54    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (10061)------------------------------
% 1.33/0.54  % (10061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (10061)Termination reason: Refutation
% 1.33/0.54  
% 1.33/0.54  % (10061)Memory used [KB]: 6140
% 1.33/0.54  % (10061)Time elapsed: 0.118 s
% 1.33/0.54  % (10061)------------------------------
% 1.33/0.54  % (10061)------------------------------
% 1.33/0.54  % (10057)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.33/0.54  % (10064)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.33/0.54  % (10041)Success in time 0.177 s
%------------------------------------------------------------------------------

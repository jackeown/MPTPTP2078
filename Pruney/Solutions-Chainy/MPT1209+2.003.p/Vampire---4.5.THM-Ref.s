%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 591 expanded)
%              Number of leaves         :   14 ( 183 expanded)
%              Depth                    :   28
%              Number of atoms          :  478 (3194 expanded)
%              Number of equality atoms :   71 ( 530 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f341,plain,(
    $false ),
    inference(subsumption_resolution,[],[f340,f213])).

fof(f213,plain,(
    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f208,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v14_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v14_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_lattices)).

fof(f208,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f120,f59])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f120,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f43,f47])).

fof(f47,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f43,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f340,plain,(
    ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f336,f331])).

fof(f331,plain,(
    k6_lattices(sK0) != k3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f198,f213])).

fof(f198,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | k6_lattices(sK0) != k3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f197,f40])).

fof(f197,plain,
    ( k6_lattices(sK0) != k3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f196,f84])).

fof(f84,plain,(
    v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f83,f43])).

fof(f83,plain,
    ( v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f66,f41])).

fof(f41,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,
    ( v4_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f40,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f196,plain,
    ( k6_lattices(sK0) != k3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f195,f120])).

fof(f195,plain,
    ( k6_lattices(sK0) != k3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f193,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f193,plain,
    ( k6_lattices(sK0) != k3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f45,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f45,plain,(
    k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f336,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f313,f184])).

fof(f184,plain,(
    ! [X8] :
      ( k3_lattices(sK0,sK1,X8) = k1_lattices(sK0,sK1,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f183,f40])).

fof(f183,plain,(
    ! [X8] :
      ( k3_lattices(sK0,sK1,X8) = k1_lattices(sK0,sK1,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f182,f84])).

fof(f182,plain,(
    ! [X8] :
      ( k3_lattices(sK0,sK1,X8) = k1_lattices(sK0,sK1,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f144,f120])).

fof(f144,plain,(
    ! [X8] :
      ( k3_lattices(sK0,sK1,X8) = k1_lattices(sK0,sK1,X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f44,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f313,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f309,f307])).

fof(f307,plain,(
    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f306,f40])).

fof(f306,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f305,f92])).

fof(f92,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f91,f43])).

fof(f91,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f70,f41])).

fof(f70,plain,
    ( v8_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f40,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f305,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f304,f94])).

fof(f94,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f93,f43])).

fof(f93,plain,
    ( v9_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f71,f41])).

fof(f71,plain,
    ( v9_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f40,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f304,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f303,f43])).

fof(f303,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f302,f44])).

fof(f302,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f301,f213])).

fof(f301,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f222,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f222,plain,(
    r1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f221,f40])).

fof(f221,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f220,f88])).

fof(f88,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f87,f43])).

fof(f87,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f68,f41])).

fof(f68,plain,
    ( v6_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f40,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f220,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f219,f92])).

fof(f219,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f218,f43])).

fof(f218,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ l3_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f217,f213])).

fof(f217,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f216,f44])).

fof(f216,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f55,f159])).

fof(f159,plain,(
    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f158,f40])).

fof(f158,plain,
    ( sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f157,f41])).

fof(f157,plain,
    ( sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f156,f42])).

fof(f42,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f156,plain,
    ( sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ v14_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f137,f43])).

fof(f137,plain,
    ( sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ l3_lattices(sK0)
    | ~ v14_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f44,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k6_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

fof(f309,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0)) ),
    inference(resolution,[],[f181,f213])).

fof(f181,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK1,X7),X7) = X7 ) ),
    inference(subsumption_resolution,[],[f180,f40])).

fof(f180,plain,(
    ! [X7] :
      ( k1_lattices(sK0,k2_lattices(sK0,sK1,X7),X7) = X7
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f179,f43])).

fof(f179,plain,(
    ! [X7] :
      ( k1_lattices(sK0,k2_lattices(sK0,sK1,X7),X7) = X7
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f92])).

fof(f143,plain,(
    ! [X7] :
      ( k1_lattices(sK0,k2_lattices(sK0,sK1,X7),X7) = X7
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f44,f60])).

fof(f60,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK3(X0) != k1_lattices(X0,k2_lattices(X0,sK2(X0),sK3(X0)),sK3(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK2(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK2(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK3(X0) != k1_lattices(X0,k2_lattices(X0,sK2(X0),sK3(X0)),sK3(X0))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (4940)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.45  % (4932)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.45  % (4940)Refutation not found, incomplete strategy% (4940)------------------------------
% 0.21/0.45  % (4940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (4940)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (4940)Memory used [KB]: 10618
% 0.21/0.45  % (4940)Time elapsed: 0.065 s
% 0.21/0.45  % (4940)------------------------------
% 0.21/0.45  % (4940)------------------------------
% 0.21/0.49  % (4935)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (4937)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (4943)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.49  % (4941)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.50  % (4948)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (4935)Refutation not found, incomplete strategy% (4935)------------------------------
% 0.21/0.50  % (4935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4935)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4935)Memory used [KB]: 10618
% 0.21/0.50  % (4935)Time elapsed: 0.086 s
% 0.21/0.50  % (4935)------------------------------
% 0.21/0.50  % (4935)------------------------------
% 0.21/0.50  % (4955)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (4938)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (4933)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (4955)Refutation not found, incomplete strategy% (4955)------------------------------
% 0.21/0.50  % (4955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4955)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4955)Memory used [KB]: 10618
% 0.21/0.50  % (4955)Time elapsed: 0.055 s
% 0.21/0.50  % (4955)------------------------------
% 0.21/0.50  % (4955)------------------------------
% 0.21/0.50  % (4942)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.50  % (4934)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (4938)Refutation not found, incomplete strategy% (4938)------------------------------
% 0.21/0.50  % (4938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4938)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4938)Memory used [KB]: 10746
% 0.21/0.50  % (4938)Time elapsed: 0.097 s
% 0.21/0.50  % (4938)------------------------------
% 0.21/0.50  % (4938)------------------------------
% 0.21/0.50  % (4942)Refutation not found, incomplete strategy% (4942)------------------------------
% 0.21/0.50  % (4942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4942)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4942)Memory used [KB]: 10618
% 0.21/0.50  % (4942)Time elapsed: 0.100 s
% 0.21/0.50  % (4942)------------------------------
% 0.21/0.50  % (4942)------------------------------
% 0.21/0.50  % (4948)Refutation not found, incomplete strategy% (4948)------------------------------
% 0.21/0.50  % (4948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4948)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4948)Memory used [KB]: 1535
% 0.21/0.50  % (4948)Time elapsed: 0.104 s
% 0.21/0.50  % (4948)------------------------------
% 0.21/0.50  % (4948)------------------------------
% 0.21/0.50  % (4947)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (4950)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (4943)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f340,f213])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f208,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    (k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v14_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f32,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),X1) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v14_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ? [X1] : (k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),X1) & m1_subset_1(X1,u1_struct_0(sK0))) => (k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_lattices)).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f120,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    l2_lattices(sK0)),
% 0.21/0.51    inference(resolution,[],[f43,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    l3_lattices(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f336,f331])).
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    k6_lattices(sK0) != k3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    inference(resolution,[],[f198,f213])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | k6_lattices(sK0) != k3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f197,f40])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    k6_lattices(sK0) != k3_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f196,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    v4_lattices(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f83,f43])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    v4_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f66,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    v10_lattices(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    v4_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.51    inference(resolution,[],[f40,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    k6_lattices(sK0) != k3_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~v4_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f195,f120])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    k6_lattices(sK0) != k3_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f193,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    k6_lattices(sK0) != k3_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(superposition,[],[f45,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.51    inference(superposition,[],[f313,f184])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ( ! [X8] : (k3_lattices(sK0,sK1,X8) = k1_lattices(sK0,sK1,X8) | ~m1_subset_1(X8,u1_struct_0(sK0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f183,f40])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ( ! [X8] : (k3_lattices(sK0,sK1,X8) = k1_lattices(sK0,sK1,X8) | ~m1_subset_1(X8,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f182,f84])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    ( ! [X8] : (k3_lattices(sK0,sK1,X8) = k1_lattices(sK0,sK1,X8) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~v4_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f144,f120])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X8] : (k3_lattices(sK0,sK1,X8) = k1_lattices(sK0,sK1,X8) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f44,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    inference(forward_demodulation,[],[f309,f307])).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f306,f40])).
% 0.21/0.51  fof(f306,plain,(
% 0.21/0.51    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f305,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    v8_lattices(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f91,f43])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    v8_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f41])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    v8_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.51    inference(resolution,[],[f40,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f304,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    v9_lattices(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f93,f43])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    v9_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f71,f41])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    v9_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.51    inference(resolution,[],[f40,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f303,f43])).
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f302,f44])).
% 0.21/0.51  fof(f302,plain,(
% 0.21/0.51    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f301,f213])).
% 0.21/0.51  fof(f301,plain,(
% 0.21/0.51    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f222,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    r1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f221,f40])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    r1_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f220,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    v6_lattices(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f87,f43])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    v6_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f68,f41])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    v6_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.51    inference(resolution,[],[f40,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f219,f92])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f218,f43])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~l3_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f217,f213])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f216,f44])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(superposition,[],[f55,f159])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f158,f40])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f157,f41])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f156,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    v14_lattices(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) | ~v14_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f137,f43])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) | ~l3_lattices(sK0) | ~v14_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f44,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0))),
% 0.21/0.51    inference(resolution,[],[f181,f213])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    ( ! [X7] : (~m1_subset_1(X7,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,sK1,X7),X7) = X7) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f180,f40])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ( ! [X7] : (k1_lattices(sK0,k2_lattices(sK0,sK1,X7),X7) = X7 | ~m1_subset_1(X7,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f179,f43])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    ( ! [X7] : (k1_lattices(sK0,k2_lattices(sK0,sK1,X7),X7) = X7 | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f143,f92])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X7] : (k1_lattices(sK0,k2_lattices(sK0,sK1,X7),X7) = X7 | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f44,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0] : (((v8_lattices(X0) | ((sK3(X0) != k1_lattices(X0,k2_lattices(X0,sK2(X0),sK3(X0)),sK3(X0)) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK2(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK2(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK3(X0) != k1_lattices(X0,k2_lattices(X0,sK2(X0),sK3(X0)),sK3(X0)) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(rectify,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (4943)------------------------------
% 0.21/0.51  % (4943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4943)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (4943)Memory used [KB]: 1791
% 0.21/0.51  % (4943)Time elapsed: 0.105 s
% 0.21/0.51  % (4943)------------------------------
% 0.21/0.51  % (4943)------------------------------
% 0.21/0.51  % (4931)Success in time 0.151 s
%------------------------------------------------------------------------------

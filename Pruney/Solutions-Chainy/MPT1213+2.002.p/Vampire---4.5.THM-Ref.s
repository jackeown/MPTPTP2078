%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:43 EST 2020

% Result     : Theorem 3.76s
% Output     : Refutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  294 (5844 expanded)
%              Number of leaves         :   33 (1818 expanded)
%              Depth                    :   30
%              Number of atoms          : 1206 (31529 expanded)
%              Number of equality atoms :  215 (5326 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6916,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6915,f97])).

fof(f97,plain,(
    sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,
    ( sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f74,f73])).

fof(f73,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k7_lattices(sK0,k7_lattices(sK0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ? [X1] :
        ( k7_lattices(sK0,k7_lattices(sK0,X1)) != X1
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).

fof(f6915,plain,(
    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(backward_demodulation,[],[f6782,f6873])).

fof(f6873,plain,(
    sK1 = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) ),
    inference(backward_demodulation,[],[f6682,f6775])).

fof(f6775,plain,(
    sK1 = k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) ),
    inference(backward_demodulation,[],[f3607,f6686])).

fof(f6686,plain,(
    sK1 = k1_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),sK1) ),
    inference(backward_demodulation,[],[f3380,f6680])).

fof(f6680,plain,(
    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) ),
    inference(forward_demodulation,[],[f6679,f6243])).

fof(f6243,plain,(
    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f6242,f92])).

fof(f92,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f6242,plain,
    ( k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f6241,f93])).

fof(f93,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f6241,plain,
    ( k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f6240,f405])).

fof(f405,plain,(
    v14_lattices(sK0) ),
    inference(subsumption_resolution,[],[f404,f95])).

fof(f95,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f404,plain,
    ( v14_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f401,f92])).

fof(f401,plain,
    ( v14_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f188,f102])).

fof(f102,plain,(
    ! [X0] :
      ( v14_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_lattices)).

fof(f188,plain,(
    v15_lattices(sK0) ),
    inference(subsumption_resolution,[],[f187,f95])).

fof(f187,plain,
    ( v15_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f146,f94])).

fof(f94,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f146,plain,
    ( v15_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f92,f105])).

fof(f105,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

fof(f6240,plain,
    ( k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))
    | ~ v14_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f6175,f95])).

fof(f6175,plain,
    ( k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))
    | ~ l3_lattices(sK0)
    | ~ v14_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f1787,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k6_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).

fof(f1787,plain,(
    m1_subset_1(k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),u1_struct_0(sK0)) ),
    inference(resolution,[],[f572,f371])).

fof(f371,plain,(
    ! [X16] :
      ( ~ m1_subset_1(X16,u1_struct_0(sK0))
      | m1_subset_1(k3_lattices(sK0,sK1,X16),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f370,f92])).

fof(f370,plain,(
    ! [X16] :
      ( m1_subset_1(k3_lattices(sK0,sK1,X16),u1_struct_0(sK0))
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f369,f192])).

fof(f192,plain,(
    v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f191,f95])).

fof(f191,plain,
    ( v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f148,f93])).

fof(f148,plain,
    ( v4_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f92,f108])).

fof(f108,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f369,plain,(
    ! [X16] :
      ( m1_subset_1(k3_lattices(sK0,sK1,X16),u1_struct_0(sK0))
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f298,f253])).

fof(f253,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f95,f99])).

fof(f99,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f298,plain,(
    ! [X16] :
      ( m1_subset_1(k3_lattices(sK0,sK1,X16),u1_struct_0(sK0))
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).

fof(f96,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f75])).

fof(f572,plain,(
    m1_subset_1(k7_lattices(sK0,k7_lattices(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f571,f92])).

fof(f571,plain,
    ( m1_subset_1(k7_lattices(sK0,k7_lattices(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f499,f95])).

fof(f499,plain,
    ( m1_subset_1(k7_lattices(sK0,k7_lattices(sK0,sK1)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f368,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f368,plain,(
    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f367,f92])).

fof(f367,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f297,f95])).

fof(f297,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f96,f136])).

fof(f6679,plain,(
    k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f6678,f6367])).

fof(f6367,plain,(
    k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) ),
    inference(resolution,[],[f1791,f453])).

fof(f453,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_lattices(sK0,k5_lattices(sK0),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f452,f92])).

fof(f452,plain,(
    ! [X0] :
      ( k3_lattices(sK0,k5_lattices(sK0),X0) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f451,f93])).

fof(f451,plain,(
    ! [X0] :
      ( k3_lattices(sK0,k5_lattices(sK0),X0) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f450,f95])).

fof(f450,plain,(
    ! [X0] :
      ( k3_lattices(sK0,k5_lattices(sK0),X0) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f403,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k5_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).

fof(f403,plain,(
    v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f402,f95])).

fof(f402,plain,
    ( v13_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f400,f92])).

fof(f400,plain,
    ( v13_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f188,f101])).

fof(f101,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1791,plain,(
    m1_subset_1(k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),u1_struct_0(sK0)) ),
    inference(resolution,[],[f572,f386])).

fof(f386,plain,(
    ! [X22] :
      ( ~ m1_subset_1(X22,u1_struct_0(sK0))
      | m1_subset_1(k4_lattices(sK0,sK1,X22),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f385,f92])).

fof(f385,plain,(
    ! [X22] :
      ( m1_subset_1(k4_lattices(sK0,sK1,X22),u1_struct_0(sK0))
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f384,f196])).

fof(f196,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f195,f95])).

fof(f195,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f150,f93])).

fof(f150,plain,
    ( v6_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f92,f110])).

fof(f110,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f384,plain,(
    ! [X22] :
      ( m1_subset_1(k4_lattices(sK0,sK1,X22),u1_struct_0(sK0))
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f304,f252])).

fof(f252,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f95,f98])).

fof(f98,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f304,plain,(
    ! [X22] :
      ( m1_subset_1(k4_lattices(sK0,sK1,X22),u1_struct_0(sK0))
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f6678,plain,(
    k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f6677,f772])).

fof(f772,plain,(
    k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f771,f92])).

fof(f771,plain,
    ( k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f770,f196])).

fof(f770,plain,
    ( k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f769,f200])).

fof(f200,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f199,f95])).

fof(f199,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f152,f93])).

fof(f152,plain,
    ( v8_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f92,f112])).

fof(f112,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f769,plain,
    ( k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f768,f202])).

fof(f202,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f201,f95])).

fof(f201,plain,
    ( v9_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f153,f93])).

fof(f153,plain,
    ( v9_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f92,f113])).

fof(f113,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f768,plain,
    ( k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f735,f95])).

fof(f735,plain,
    ( k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f441,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattices)).

fof(f441,plain,(
    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f432,f92])).

fof(f432,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f253,f117])).

fof(f117,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f6677,plain,(
    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) = k4_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f6676,f554])).

fof(f554,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f553,f92])).

fof(f553,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f552,f93])).

fof(f552,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f551,f94])).

fof(f551,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f493,f95])).

fof(f493,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f368,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattices)).

fof(f6676,plain,(
    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f6675,f656])).

fof(f656,plain,(
    k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f655,f92])).

fof(f655,plain,
    ( k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f654,f93])).

fof(f654,plain,
    ( k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f653,f403])).

fof(f653,plain,
    ( k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f610,f95])).

fof(f610,plain,
    ( k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f431,f123])).

fof(f431,plain,(
    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f424,f92])).

fof(f424,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f252,f114])).

fof(f114,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f6675,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) = k3_lattices(sK0,k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)),k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f6638,f558])).

fof(f558,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f557,f92])).

fof(f557,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f556,f93])).

fof(f556,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f555,f94])).

fof(f555,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f494,f95])).

fof(f494,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f368,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattices)).

fof(f6638,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)),k5_lattices(sK0)),k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) ),
    inference(resolution,[],[f876,f572])).

fof(f876,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k5_lattices(sK0)),k4_lattices(sK0,sK1,X1)) ) ),
    inference(forward_demodulation,[],[f875,f354])).

fof(f354,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f353,f92])).

fof(f353,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f352,f93])).

fof(f352,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f351,f94])).

fof(f351,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f292,f95])).

fof(f292,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f96,f127])).

fof(f875,plain,(
    ! [X1] :
      ( k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f874,f92])).

fof(f874,plain,(
    ! [X1] :
      ( k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f873,f93])).

fof(f873,plain,(
    ! [X1] :
      ( k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f872,f186])).

fof(f186,plain,(
    v11_lattices(sK0) ),
    inference(subsumption_resolution,[],[f185,f95])).

fof(f185,plain,
    ( v11_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f145,f94])).

fof(f145,plain,
    ( v11_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f92,f104])).

fof(f104,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f872,plain,(
    ! [X1] :
      ( k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v11_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f871,f95])).

fof(f871,plain,(
    ! [X1] :
      ( k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v11_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f870,f368])).

fof(f870,plain,(
    ! [X1] :
      ( k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1))
      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v11_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f856,f96])).

fof(f856,plain,(
    ! [X1] :
      ( k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v11_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f125,f350])).

fof(f350,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f349,f92])).

fof(f349,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f348,f93])).

fof(f348,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f347,f94])).

fof(f347,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f291,f95])).

fof(f291,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f96,f126])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) = k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) = k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) = k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) = k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattices)).

fof(f3380,plain,(
    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),sK1) ),
    inference(forward_demodulation,[],[f3363,f1793])).

fof(f1793,plain,(
    k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) ),
    inference(resolution,[],[f572,f398])).

fof(f398,plain,(
    ! [X26] :
      ( ~ m1_subset_1(X26,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X26) = k4_lattices(sK0,X26,sK1) ) ),
    inference(subsumption_resolution,[],[f397,f92])).

fof(f397,plain,(
    ! [X26] :
      ( k4_lattices(sK0,sK1,X26) = k4_lattices(sK0,X26,sK1)
      | ~ m1_subset_1(X26,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f396,f196])).

fof(f396,plain,(
    ! [X26] :
      ( k4_lattices(sK0,sK1,X26) = k4_lattices(sK0,X26,sK1)
      | ~ m1_subset_1(X26,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f308,f252])).

fof(f308,plain,(
    ! [X26] :
      ( k4_lattices(sK0,sK1,X26) = k4_lattices(sK0,X26,sK1)
      | ~ m1_subset_1(X26,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f3363,plain,(
    sK1 = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1),sK1) ),
    inference(resolution,[],[f1406,f572])).

fof(f1406,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k4_lattices(sK0,X0,sK1),sK1) ) ),
    inference(subsumption_resolution,[],[f1405,f92])).

fof(f1405,plain,(
    ! [X0] :
      ( sK1 = k1_lattices(sK0,k4_lattices(sK0,X0,sK1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1404,f196])).

fof(f1404,plain,(
    ! [X0] :
      ( sK1 = k1_lattices(sK0,k4_lattices(sK0,X0,sK1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1403,f252])).

fof(f1403,plain,(
    ! [X0] :
      ( sK1 = k1_lattices(sK0,k4_lattices(sK0,X0,sK1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1402,f96])).

fof(f1402,plain,(
    ! [X0] :
      ( sK1 = k1_lattices(sK0,k4_lattices(sK0,X0,sK1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1396])).

fof(f1396,plain,(
    ! [X0] :
      ( sK1 = k1_lattices(sK0,k4_lattices(sK0,X0,sK1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f366,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f366,plain,(
    ! [X15] :
      ( sK1 = k1_lattices(sK0,k2_lattices(sK0,X15,sK1),sK1)
      | ~ m1_subset_1(X15,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f365,f92])).

fof(f365,plain,(
    ! [X15] :
      ( sK1 = k1_lattices(sK0,k2_lattices(sK0,X15,sK1),sK1)
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f364,f95])).

fof(f364,plain,(
    ! [X15] :
      ( sK1 = k1_lattices(sK0,k2_lattices(sK0,X15,sK1),sK1)
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f296,f200])).

fof(f296,plain,(
    ! [X15] :
      ( sK1 = k1_lattices(sK0,k2_lattices(sK0,X15,sK1),sK1)
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f132])).

fof(f132,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f88,f90,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0))
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
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
    inference(rectify,[],[f87])).

fof(f87,plain,(
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
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(f3607,plain,(
    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k1_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),sK1) ),
    inference(forward_demodulation,[],[f3590,f1823])).

fof(f1823,plain,(
    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) ),
    inference(backward_demodulation,[],[f1789,f1790])).

fof(f1790,plain,(
    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) ),
    inference(resolution,[],[f572,f383])).

fof(f383,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,u1_struct_0(sK0))
      | k3_lattices(sK0,sK1,X20) = k3_lattices(sK0,X20,sK1) ) ),
    inference(subsumption_resolution,[],[f382,f92])).

fof(f382,plain,(
    ! [X20] :
      ( k3_lattices(sK0,sK1,X20) = k3_lattices(sK0,X20,sK1)
      | ~ m1_subset_1(X20,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f381,f192])).

fof(f381,plain,(
    ! [X20] :
      ( k3_lattices(sK0,sK1,X20) = k3_lattices(sK0,X20,sK1)
      | ~ m1_subset_1(X20,u1_struct_0(sK0))
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f302,f253])).

fof(f302,plain,(
    ! [X20] :
      ( k3_lattices(sK0,sK1,X20) = k3_lattices(sK0,X20,sK1)
      | ~ m1_subset_1(X20,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f1789,plain,(
    k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) = k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) ),
    inference(resolution,[],[f572,f380])).

fof(f380,plain,(
    ! [X19] :
      ( ~ m1_subset_1(X19,u1_struct_0(sK0))
      | k3_lattices(sK0,X19,sK1) = k1_lattices(sK0,X19,sK1) ) ),
    inference(subsumption_resolution,[],[f379,f92])).

fof(f379,plain,(
    ! [X19] :
      ( k3_lattices(sK0,X19,sK1) = k1_lattices(sK0,X19,sK1)
      | ~ m1_subset_1(X19,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f378,f192])).

fof(f378,plain,(
    ! [X19] :
      ( k3_lattices(sK0,X19,sK1) = k1_lattices(sK0,X19,sK1)
      | ~ m1_subset_1(X19,u1_struct_0(sK0))
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f301,f253])).

fof(f301,plain,(
    ! [X19] :
      ( k3_lattices(sK0,X19,sK1) = k1_lattices(sK0,X19,sK1)
      | ~ m1_subset_1(X19,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f3590,plain,(
    k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) = k1_lattices(sK0,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1),sK1) ),
    inference(resolution,[],[f1971,f572])).

fof(f1971,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k1_lattices(sK0,X6,sK1) = k1_lattices(sK0,k1_lattices(sK0,X6,sK1),sK1) ) ),
    inference(forward_demodulation,[],[f1958,f314])).

fof(f314,plain,(
    sK1 = k1_lattices(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f313,f92])).

fof(f313,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f312,f196])).

fof(f312,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f311,f200])).

fof(f311,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f310,f202])).

fof(f310,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f281,f95])).

fof(f281,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f96,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

fof(f1958,plain,(
    ! [X6] :
      ( k1_lattices(sK0,X6,k1_lattices(sK0,sK1,sK1)) = k1_lattices(sK0,k1_lattices(sK0,X6,sK1),sK1)
      | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f325,f96])).

fof(f325,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k1_lattices(sK0,X2,k1_lattices(sK0,sK1,X3)) = k1_lattices(sK0,k1_lattices(sK0,X2,sK1),X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f324,f92])).

fof(f324,plain,(
    ! [X2,X3] :
      ( k1_lattices(sK0,X2,k1_lattices(sK0,sK1,X3)) = k1_lattices(sK0,k1_lattices(sK0,X2,sK1),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f323,f253])).

fof(f323,plain,(
    ! [X2,X3] :
      ( k1_lattices(sK0,X2,k1_lattices(sK0,sK1,X3)) = k1_lattices(sK0,k1_lattices(sK0,X2,sK1),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f284,f194])).

fof(f194,plain,(
    v5_lattices(sK0) ),
    inference(subsumption_resolution,[],[f193,f95])).

fof(f193,plain,
    ( v5_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f149,f93])).

fof(f149,plain,
    ( v5_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f92,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f284,plain,(
    ! [X2,X3] :
      ( k1_lattices(sK0,X2,k1_lattices(sK0,sK1,X3)) = k1_lattices(sK0,k1_lattices(sK0,X2,sK1),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v5_lattices(sK0)
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f118])).

fof(f118,plain,(
    ! [X6,X4,X0,X5] :
      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ( k1_lattices(X0,sK2(X0),k1_lattices(X0,sK3(X0),sK4(X0))) != k1_lattices(X0,k1_lattices(X0,sK2(X0),sK3(X0)),sK4(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f77,f80,f79,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,sK2(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK2(X0),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,sK2(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK2(X0),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,sK2(X0),k1_lattices(X0,sK3(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK2(X0),sK3(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k1_lattices(X0,sK2(X0),k1_lattices(X0,sK3(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK2(X0),sK3(X0)),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,sK2(X0),k1_lattices(X0,sK3(X0),sK4(X0))) != k1_lattices(X0,k1_lattices(X0,sK2(X0),sK3(X0)),sK4(X0))
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattices)).

fof(f6682,plain,(
    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) ),
    inference(backward_demodulation,[],[f1793,f6680])).

fof(f6782,plain,(
    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) ),
    inference(backward_demodulation,[],[f4512,f6775])).

fof(f4512,plain,(
    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f4511,f1787])).

fof(f4511,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),u1_struct_0(sK0))
    | k7_lattices(sK0,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f4510,f1823])).

fof(f4510,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))
    | ~ m1_subset_1(k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f4493,f1823])).

fof(f4493,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1))
    | ~ m1_subset_1(k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1352,f572])).

fof(f1352,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,X2,k1_lattices(sK0,X2,sK1)) = X2
      | ~ m1_subset_1(k1_lattices(sK0,X2,sK1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1351,f92])).

fof(f1351,plain,(
    ! [X2] :
      ( k4_lattices(sK0,X2,k1_lattices(sK0,X2,sK1)) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_lattices(sK0,X2,sK1),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1350,f196])).

fof(f1350,plain,(
    ! [X2] :
      ( k4_lattices(sK0,X2,k1_lattices(sK0,X2,sK1)) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_lattices(sK0,X2,sK1),u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1334,f252])).

fof(f1334,plain,(
    ! [X2] :
      ( k4_lattices(sK0,X2,k1_lattices(sK0,X2,sK1)) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_lattices(sK0,X2,sK1),u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1329])).

fof(f1329,plain,(
    ! [X2] :
      ( k4_lattices(sK0,X2,k1_lattices(sK0,X2,sK1)) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_lattices(sK0,X2,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f360,f141])).

fof(f360,plain,(
    ! [X13] :
      ( k2_lattices(sK0,X13,k1_lattices(sK0,X13,sK1)) = X13
      | ~ m1_subset_1(X13,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f359,f92])).

fof(f359,plain,(
    ! [X13] :
      ( k2_lattices(sK0,X13,k1_lattices(sK0,X13,sK1)) = X13
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f358,f95])).

fof(f358,plain,(
    ! [X13] :
      ( k2_lattices(sK0,X13,k1_lattices(sK0,X13,sK1)) = X13
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f294,f202])).

fof(f294,plain,(
    ! [X13] :
      ( k2_lattices(sK0,X13,k1_lattices(sK0,X13,sK1)) = X13
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f128])).

fof(f128,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0)))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f83,f85,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0)))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:04:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (7329)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (7338)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.48  % (7337)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.48  % (7329)Refutation not found, incomplete strategy% (7329)------------------------------
% 0.20/0.48  % (7329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (7329)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (7329)Memory used [KB]: 6140
% 0.20/0.48  % (7329)Time elapsed: 0.065 s
% 0.20/0.48  % (7329)------------------------------
% 0.20/0.48  % (7329)------------------------------
% 0.20/0.49  % (7330)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.49  % (7331)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.49  % (7339)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.49  % (7327)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (7336)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (7335)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.50  % (7328)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (7343)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.51  % (7323)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (7325)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.26/0.51  % (7325)Refutation not found, incomplete strategy% (7325)------------------------------
% 1.26/0.51  % (7325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.51  % (7325)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.51  
% 1.26/0.51  % (7325)Memory used [KB]: 10618
% 1.26/0.51  % (7325)Time elapsed: 0.103 s
% 1.26/0.51  % (7325)------------------------------
% 1.26/0.51  % (7325)------------------------------
% 1.26/0.51  % (7344)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.26/0.52  % (7334)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.26/0.52  % (7322)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.26/0.52  % (7332)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.26/0.52  % (7341)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.26/0.52  % (7326)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.26/0.52  % (7332)Refutation not found, incomplete strategy% (7332)------------------------------
% 1.26/0.52  % (7332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (7332)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  
% 1.26/0.52  % (7332)Memory used [KB]: 10618
% 1.26/0.52  % (7332)Time elapsed: 0.114 s
% 1.26/0.52  % (7332)------------------------------
% 1.26/0.52  % (7332)------------------------------
% 1.37/0.52  % (7324)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.37/0.53  % (7342)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.37/0.53  % (7345)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.37/0.53  % (7345)Refutation not found, incomplete strategy% (7345)------------------------------
% 1.37/0.53  % (7345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (7345)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (7345)Memory used [KB]: 10746
% 1.37/0.53  % (7345)Time elapsed: 0.121 s
% 1.37/0.53  % (7345)------------------------------
% 1.37/0.53  % (7345)------------------------------
% 1.37/0.53  % (7333)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.37/0.54  % (7340)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.37/0.61  % (7323)Refutation not found, incomplete strategy% (7323)------------------------------
% 1.37/0.61  % (7323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.61  % (7323)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.61  
% 1.37/0.61  % (7323)Memory used [KB]: 6140
% 1.37/0.61  % (7323)Time elapsed: 0.199 s
% 1.37/0.61  % (7323)------------------------------
% 1.37/0.61  % (7323)------------------------------
% 2.19/0.63  % (7344)Refutation not found, incomplete strategy% (7344)------------------------------
% 2.19/0.63  % (7344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.63  % (7344)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.63  
% 2.19/0.63  % (7344)Memory used [KB]: 1663
% 2.19/0.63  % (7344)Time elapsed: 0.226 s
% 2.19/0.63  % (7344)------------------------------
% 2.19/0.63  % (7344)------------------------------
% 3.76/0.89  % (7333)Refutation found. Thanks to Tanya!
% 3.76/0.89  % SZS status Theorem for theBenchmark
% 3.76/0.90  % SZS output start Proof for theBenchmark
% 3.76/0.90  fof(f6916,plain,(
% 3.76/0.90    $false),
% 3.76/0.90    inference(subsumption_resolution,[],[f6915,f97])).
% 3.76/0.90  fof(f97,plain,(
% 3.76/0.90    sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 3.76/0.90    inference(cnf_transformation,[],[f75])).
% 3.76/0.90  fof(f75,plain,(
% 3.76/0.90    (sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 3.76/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f74,f73])).
% 3.76/0.90  fof(f73,plain,(
% 3.76/0.90    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k7_lattices(sK0,k7_lattices(sK0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 3.76/0.90    introduced(choice_axiom,[])).
% 3.76/0.90  fof(f74,plain,(
% 3.76/0.90    ? [X1] : (k7_lattices(sK0,k7_lattices(sK0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) => (sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 3.76/0.90    introduced(choice_axiom,[])).
% 3.76/0.90  fof(f27,plain,(
% 3.76/0.90    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.76/0.90    inference(flattening,[],[f26])).
% 3.76/0.90  fof(f26,plain,(
% 3.76/0.90    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.76/0.90    inference(ennf_transformation,[],[f25])).
% 3.76/0.90  fof(f25,negated_conjecture,(
% 3.76/0.90    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 3.76/0.90    inference(negated_conjecture,[],[f24])).
% 3.76/0.90  fof(f24,conjecture,(
% 3.76/0.90    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 3.76/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).
% 3.76/0.90  fof(f6915,plain,(
% 3.76/0.90    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 3.76/0.90    inference(backward_demodulation,[],[f6782,f6873])).
% 3.76/0.90  fof(f6873,plain,(
% 3.76/0.90    sK1 = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1)),
% 3.76/0.90    inference(backward_demodulation,[],[f6682,f6775])).
% 3.76/0.90  fof(f6775,plain,(
% 3.76/0.90    sK1 = k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))),
% 3.76/0.90    inference(backward_demodulation,[],[f3607,f6686])).
% 3.76/0.90  fof(f6686,plain,(
% 3.76/0.90    sK1 = k1_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),sK1)),
% 3.76/0.90    inference(backward_demodulation,[],[f3380,f6680])).
% 3.76/0.90  fof(f6680,plain,(
% 3.76/0.90    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))),
% 3.76/0.90    inference(forward_demodulation,[],[f6679,f6243])).
% 3.76/0.90  fof(f6243,plain,(
% 3.76/0.90    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))),
% 3.76/0.90    inference(subsumption_resolution,[],[f6242,f92])).
% 3.76/0.90  fof(f92,plain,(
% 3.76/0.90    ~v2_struct_0(sK0)),
% 3.76/0.90    inference(cnf_transformation,[],[f75])).
% 3.76/0.90  fof(f6242,plain,(
% 3.76/0.90    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) | v2_struct_0(sK0)),
% 3.76/0.90    inference(subsumption_resolution,[],[f6241,f93])).
% 3.76/0.91  fof(f93,plain,(
% 3.76/0.91    v10_lattices(sK0)),
% 3.76/0.91    inference(cnf_transformation,[],[f75])).
% 3.76/0.91  fof(f6241,plain,(
% 3.76/0.91    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f6240,f405])).
% 3.76/0.91  fof(f405,plain,(
% 3.76/0.91    v14_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f404,f95])).
% 3.76/0.91  fof(f95,plain,(
% 3.76/0.91    l3_lattices(sK0)),
% 3.76/0.91    inference(cnf_transformation,[],[f75])).
% 3.76/0.91  fof(f404,plain,(
% 3.76/0.91    v14_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f401,f92])).
% 3.76/0.91  fof(f401,plain,(
% 3.76/0.91    v14_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(resolution,[],[f188,f102])).
% 3.76/0.91  fof(f102,plain,(
% 3.76/0.91    ( ! [X0] : (v14_lattices(X0) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f30])).
% 3.76/0.91  fof(f30,plain,(
% 3.76/0.91    ! [X0] : ((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.76/0.91    inference(flattening,[],[f29])).
% 3.76/0.91  fof(f29,plain,(
% 3.76/0.91    ! [X0] : (((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | (~v15_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.76/0.91    inference(ennf_transformation,[],[f2])).
% 3.76/0.91  fof(f2,axiom,(
% 3.76/0.91    ! [X0] : (l3_lattices(X0) => ((v15_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0))))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_lattices)).
% 3.76/0.91  fof(f188,plain,(
% 3.76/0.91    v15_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f187,f95])).
% 3.76/0.91  fof(f187,plain,(
% 3.76/0.91    v15_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f146,f94])).
% 3.76/0.91  fof(f94,plain,(
% 3.76/0.91    v17_lattices(sK0)),
% 3.76/0.91    inference(cnf_transformation,[],[f75])).
% 3.76/0.91  fof(f146,plain,(
% 3.76/0.91    v15_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(resolution,[],[f92,f105])).
% 3.76/0.91  fof(f105,plain,(
% 3.76/0.91    ( ! [X0] : (v15_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f32])).
% 3.76/0.91  fof(f32,plain,(
% 3.76/0.91    ! [X0] : ((v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.76/0.91    inference(flattening,[],[f31])).
% 3.76/0.91  fof(f31,plain,(
% 3.76/0.91    ! [X0] : (((v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | (~v17_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.76/0.91    inference(ennf_transformation,[],[f3])).
% 3.76/0.91  fof(f3,axiom,(
% 3.76/0.91    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).
% 3.76/0.91  fof(f6240,plain,(
% 3.76/0.91    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) | ~v14_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f6175,f95])).
% 3.76/0.91  fof(f6175,plain,(
% 3.76/0.91    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) | ~l3_lattices(sK0) | ~v14_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(resolution,[],[f1787,f124])).
% 3.76/0.91  fof(f124,plain,(
% 3.76/0.91    ( ! [X0,X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f48])).
% 3.76/0.91  fof(f48,plain,(
% 3.76/0.91    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.91    inference(flattening,[],[f47])).
% 3.76/0.91  fof(f47,plain,(
% 3.76/0.91    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.91    inference(ennf_transformation,[],[f21])).
% 3.76/0.91  fof(f21,axiom,(
% 3.76/0.91    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).
% 3.76/0.91  fof(f1787,plain,(
% 3.76/0.91    m1_subset_1(k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),u1_struct_0(sK0))),
% 3.76/0.91    inference(resolution,[],[f572,f371])).
% 3.76/0.91  fof(f371,plain,(
% 3.76/0.91    ( ! [X16] : (~m1_subset_1(X16,u1_struct_0(sK0)) | m1_subset_1(k3_lattices(sK0,sK1,X16),u1_struct_0(sK0))) )),
% 3.76/0.91    inference(subsumption_resolution,[],[f370,f92])).
% 3.76/0.91  fof(f370,plain,(
% 3.76/0.91    ( ! [X16] : (m1_subset_1(k3_lattices(sK0,sK1,X16),u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 3.76/0.91    inference(subsumption_resolution,[],[f369,f192])).
% 3.76/0.91  fof(f192,plain,(
% 3.76/0.91    v4_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f191,f95])).
% 3.76/0.91  fof(f191,plain,(
% 3.76/0.91    v4_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f148,f93])).
% 3.76/0.91  fof(f148,plain,(
% 3.76/0.91    v4_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(resolution,[],[f92,f108])).
% 3.76/0.91  fof(f108,plain,(
% 3.76/0.91    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f34])).
% 3.76/0.91  fof(f34,plain,(
% 3.76/0.91    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.76/0.91    inference(flattening,[],[f33])).
% 3.76/0.91  fof(f33,plain,(
% 3.76/0.91    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.76/0.91    inference(ennf_transformation,[],[f1])).
% 3.76/0.91  fof(f1,axiom,(
% 3.76/0.91    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 3.76/0.91  fof(f369,plain,(
% 3.76/0.91    ( ! [X16] : (m1_subset_1(k3_lattices(sK0,sK1,X16),u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~v4_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.91    inference(subsumption_resolution,[],[f298,f253])).
% 3.76/0.91  fof(f253,plain,(
% 3.76/0.91    l2_lattices(sK0)),
% 3.76/0.91    inference(resolution,[],[f95,f99])).
% 3.76/0.91  fof(f99,plain,(
% 3.76/0.91    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f28])).
% 3.76/0.91  fof(f28,plain,(
% 3.76/0.91    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 3.76/0.91    inference(ennf_transformation,[],[f14])).
% 3.76/0.91  fof(f14,axiom,(
% 3.76/0.91    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 3.76/0.91  fof(f298,plain,(
% 3.76/0.91    ( ! [X16] : (m1_subset_1(k3_lattices(sK0,sK1,X16),u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.91    inference(resolution,[],[f96,f137])).
% 3.76/0.91  fof(f137,plain,(
% 3.76/0.91    ( ! [X2,X0,X1] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f62])).
% 3.76/0.91  fof(f62,plain,(
% 3.76/0.91    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.91    inference(flattening,[],[f61])).
% 3.76/0.91  fof(f61,plain,(
% 3.76/0.91    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.91    inference(ennf_transformation,[],[f9])).
% 3.76/0.91  fof(f9,axiom,(
% 3.76/0.91    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).
% 3.76/0.91  fof(f96,plain,(
% 3.76/0.91    m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.76/0.91    inference(cnf_transformation,[],[f75])).
% 3.76/0.91  fof(f572,plain,(
% 3.76/0.91    m1_subset_1(k7_lattices(sK0,k7_lattices(sK0,sK1)),u1_struct_0(sK0))),
% 3.76/0.91    inference(subsumption_resolution,[],[f571,f92])).
% 3.76/0.91  fof(f571,plain,(
% 3.76/0.91    m1_subset_1(k7_lattices(sK0,k7_lattices(sK0,sK1)),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f499,f95])).
% 3.76/0.91  fof(f499,plain,(
% 3.76/0.91    m1_subset_1(k7_lattices(sK0,k7_lattices(sK0,sK1)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(resolution,[],[f368,f136])).
% 3.76/0.91  fof(f136,plain,(
% 3.76/0.91    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f60])).
% 3.76/0.91  fof(f60,plain,(
% 3.76/0.91    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.91    inference(flattening,[],[f59])).
% 3.76/0.91  fof(f59,plain,(
% 3.76/0.91    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.91    inference(ennf_transformation,[],[f13])).
% 3.76/0.91  fof(f13,axiom,(
% 3.76/0.91    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).
% 3.76/0.91  fof(f368,plain,(
% 3.76/0.91    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 3.76/0.91    inference(subsumption_resolution,[],[f367,f92])).
% 3.76/0.91  fof(f367,plain,(
% 3.76/0.91    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f297,f95])).
% 3.76/0.91  fof(f297,plain,(
% 3.76/0.91    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(resolution,[],[f96,f136])).
% 3.76/0.91  fof(f6679,plain,(
% 3.76/0.91    k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))),
% 3.76/0.91    inference(forward_demodulation,[],[f6678,f6367])).
% 3.76/0.91  fof(f6367,plain,(
% 3.76/0.91    k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))),
% 3.76/0.91    inference(resolution,[],[f1791,f453])).
% 3.76/0.91  fof(f453,plain,(
% 3.76/0.91    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k3_lattices(sK0,k5_lattices(sK0),X0) = X0) )),
% 3.76/0.91    inference(subsumption_resolution,[],[f452,f92])).
% 3.76/0.91  fof(f452,plain,(
% 3.76/0.91    ( ! [X0] : (k3_lattices(sK0,k5_lattices(sK0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 3.76/0.91    inference(subsumption_resolution,[],[f451,f93])).
% 3.76/0.91  fof(f451,plain,(
% 3.76/0.91    ( ! [X0] : (k3_lattices(sK0,k5_lattices(sK0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.91    inference(subsumption_resolution,[],[f450,f95])).
% 3.76/0.91  fof(f450,plain,(
% 3.76/0.91    ( ! [X0] : (k3_lattices(sK0,k5_lattices(sK0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.91    inference(resolution,[],[f403,f123])).
% 3.76/0.91  fof(f123,plain,(
% 3.76/0.91    ( ! [X0,X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f46])).
% 3.76/0.91  fof(f46,plain,(
% 3.76/0.91    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.91    inference(flattening,[],[f45])).
% 3.76/0.91  fof(f45,plain,(
% 3.76/0.91    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.91    inference(ennf_transformation,[],[f20])).
% 3.76/0.91  fof(f20,axiom,(
% 3.76/0.91    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).
% 3.76/0.91  fof(f403,plain,(
% 3.76/0.91    v13_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f402,f95])).
% 3.76/0.91  fof(f402,plain,(
% 3.76/0.91    v13_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f400,f92])).
% 3.76/0.91  fof(f400,plain,(
% 3.76/0.91    v13_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(resolution,[],[f188,f101])).
% 3.76/0.91  fof(f101,plain,(
% 3.76/0.91    ( ! [X0] : (v13_lattices(X0) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f30])).
% 3.76/0.91  fof(f1791,plain,(
% 3.76/0.91    m1_subset_1(k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),u1_struct_0(sK0))),
% 3.76/0.91    inference(resolution,[],[f572,f386])).
% 3.76/0.91  fof(f386,plain,(
% 3.76/0.91    ( ! [X22] : (~m1_subset_1(X22,u1_struct_0(sK0)) | m1_subset_1(k4_lattices(sK0,sK1,X22),u1_struct_0(sK0))) )),
% 3.76/0.91    inference(subsumption_resolution,[],[f385,f92])).
% 3.76/0.91  fof(f385,plain,(
% 3.76/0.91    ( ! [X22] : (m1_subset_1(k4_lattices(sK0,sK1,X22),u1_struct_0(sK0)) | ~m1_subset_1(X22,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 3.76/0.91    inference(subsumption_resolution,[],[f384,f196])).
% 3.76/0.91  fof(f196,plain,(
% 3.76/0.91    v6_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f195,f95])).
% 3.76/0.91  fof(f195,plain,(
% 3.76/0.91    v6_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f150,f93])).
% 3.76/0.91  fof(f150,plain,(
% 3.76/0.91    v6_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(resolution,[],[f92,f110])).
% 3.76/0.91  fof(f110,plain,(
% 3.76/0.91    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f34])).
% 3.76/0.91  fof(f384,plain,(
% 3.76/0.91    ( ! [X22] : (m1_subset_1(k4_lattices(sK0,sK1,X22),u1_struct_0(sK0)) | ~m1_subset_1(X22,u1_struct_0(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.91    inference(subsumption_resolution,[],[f304,f252])).
% 3.76/0.91  fof(f252,plain,(
% 3.76/0.91    l1_lattices(sK0)),
% 3.76/0.91    inference(resolution,[],[f95,f98])).
% 3.76/0.91  fof(f98,plain,(
% 3.76/0.91    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f28])).
% 3.76/0.91  fof(f304,plain,(
% 3.76/0.91    ( ! [X22] : (m1_subset_1(k4_lattices(sK0,sK1,X22),u1_struct_0(sK0)) | ~m1_subset_1(X22,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.91    inference(resolution,[],[f96,f140])).
% 3.76/0.91  fof(f140,plain,(
% 3.76/0.91    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f68])).
% 3.76/0.91  fof(f68,plain,(
% 3.76/0.91    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.91    inference(flattening,[],[f67])).
% 3.76/0.91  fof(f67,plain,(
% 3.76/0.91    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.91    inference(ennf_transformation,[],[f10])).
% 3.76/0.91  fof(f10,axiom,(
% 3.76/0.91    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).
% 3.76/0.91  fof(f6678,plain,(
% 3.76/0.91    k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))),
% 3.76/0.91    inference(forward_demodulation,[],[f6677,f772])).
% 3.76/0.91  fof(f772,plain,(
% 3.76/0.91    k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))),
% 3.76/0.91    inference(subsumption_resolution,[],[f771,f92])).
% 3.76/0.91  fof(f771,plain,(
% 3.76/0.91    k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f770,f196])).
% 3.76/0.91  fof(f770,plain,(
% 3.76/0.91    k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f769,f200])).
% 3.76/0.91  fof(f200,plain,(
% 3.76/0.91    v8_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f199,f95])).
% 3.76/0.91  fof(f199,plain,(
% 3.76/0.91    v8_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f152,f93])).
% 3.76/0.91  fof(f152,plain,(
% 3.76/0.91    v8_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(resolution,[],[f92,f112])).
% 3.76/0.91  fof(f112,plain,(
% 3.76/0.91    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f34])).
% 3.76/0.91  fof(f769,plain,(
% 3.76/0.91    k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f768,f202])).
% 3.76/0.91  fof(f202,plain,(
% 3.76/0.91    v9_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f201,f95])).
% 3.76/0.91  fof(f201,plain,(
% 3.76/0.91    v9_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f153,f93])).
% 3.76/0.91  fof(f153,plain,(
% 3.76/0.91    v9_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.91    inference(resolution,[],[f92,f113])).
% 3.76/0.91  fof(f113,plain,(
% 3.76/0.91    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f34])).
% 3.76/0.91  fof(f768,plain,(
% 3.76/0.91    k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f735,f95])).
% 3.76/0.91  fof(f735,plain,(
% 3.76/0.91    k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(resolution,[],[f441,f116])).
% 3.76/0.91  fof(f116,plain,(
% 3.76/0.91    ( ! [X0,X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f40])).
% 3.76/0.91  fof(f40,plain,(
% 3.76/0.91    ! [X0] : (! [X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.91    inference(flattening,[],[f39])).
% 3.76/0.91  fof(f39,plain,(
% 3.76/0.91    ! [X0] : (! [X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.91    inference(ennf_transformation,[],[f18])).
% 3.76/0.91  fof(f18,axiom,(
% 3.76/0.91    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,X1,X1) = X1))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattices)).
% 3.76/0.91  fof(f441,plain,(
% 3.76/0.91    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 3.76/0.91    inference(subsumption_resolution,[],[f432,f92])).
% 3.76/0.91  fof(f432,plain,(
% 3.76/0.91    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 3.76/0.91    inference(resolution,[],[f253,f117])).
% 3.76/0.91  fof(f117,plain,(
% 3.76/0.91    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f42])).
% 3.76/0.91  fof(f42,plain,(
% 3.76/0.91    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.91    inference(flattening,[],[f41])).
% 3.76/0.91  fof(f41,plain,(
% 3.76/0.91    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.91    inference(ennf_transformation,[],[f12])).
% 3.76/0.91  fof(f12,axiom,(
% 3.76/0.91    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).
% 3.76/0.91  fof(f6677,plain,(
% 3.76/0.91    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) = k4_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))),
% 3.76/0.91    inference(forward_demodulation,[],[f6676,f554])).
% 3.76/0.91  fof(f554,plain,(
% 3.76/0.91    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))),
% 3.76/0.91    inference(subsumption_resolution,[],[f553,f92])).
% 3.76/0.91  fof(f553,plain,(
% 3.76/0.91    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f552,f93])).
% 3.76/0.91  fof(f552,plain,(
% 3.76/0.91    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f551,f94])).
% 3.76/0.91  fof(f551,plain,(
% 3.76/0.91    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f493,f95])).
% 3.76/0.91  fof(f493,plain,(
% 3.76/0.91    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(resolution,[],[f368,f126])).
% 3.76/0.91  fof(f126,plain,(
% 3.76/0.91    ( ! [X0,X1] : (k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f52])).
% 3.76/0.91  fof(f52,plain,(
% 3.76/0.91    ! [X0] : (! [X1] : (k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.91    inference(flattening,[],[f51])).
% 3.76/0.91  fof(f51,plain,(
% 3.76/0.91    ! [X0] : (! [X1] : (k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.91    inference(ennf_transformation,[],[f23])).
% 3.76/0.91  fof(f23,axiom,(
% 3.76/0.91    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattices)).
% 3.76/0.91  fof(f6676,plain,(
% 3.76/0.91    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))),
% 3.76/0.91    inference(forward_demodulation,[],[f6675,f656])).
% 3.76/0.91  fof(f656,plain,(
% 3.76/0.91    k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))),
% 3.76/0.91    inference(subsumption_resolution,[],[f655,f92])).
% 3.76/0.91  fof(f655,plain,(
% 3.76/0.91    k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f654,f93])).
% 3.76/0.91  fof(f654,plain,(
% 3.76/0.91    k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f653,f403])).
% 3.76/0.91  fof(f653,plain,(
% 3.76/0.91    k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f610,f95])).
% 3.76/0.91  fof(f610,plain,(
% 3.76/0.91    k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(resolution,[],[f431,f123])).
% 3.76/0.91  fof(f431,plain,(
% 3.76/0.91    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 3.76/0.91    inference(subsumption_resolution,[],[f424,f92])).
% 3.76/0.91  fof(f424,plain,(
% 3.76/0.91    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 3.76/0.91    inference(resolution,[],[f252,f114])).
% 3.76/0.91  fof(f114,plain,(
% 3.76/0.91    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.91    inference(cnf_transformation,[],[f36])).
% 3.76/0.91  fof(f36,plain,(
% 3.76/0.91    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.91    inference(flattening,[],[f35])).
% 3.76/0.91  fof(f35,plain,(
% 3.76/0.91    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.91    inference(ennf_transformation,[],[f11])).
% 3.76/0.91  fof(f11,axiom,(
% 3.76/0.91    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 3.76/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 3.76/0.91  fof(f6675,plain,(
% 3.76/0.91    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) = k3_lattices(sK0,k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)),k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))),
% 3.76/0.91    inference(forward_demodulation,[],[f6638,f558])).
% 3.76/0.91  fof(f558,plain,(
% 3.76/0.91    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1))),
% 3.76/0.91    inference(subsumption_resolution,[],[f557,f92])).
% 3.76/0.91  fof(f557,plain,(
% 3.76/0.91    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f556,f93])).
% 3.76/0.91  fof(f556,plain,(
% 3.76/0.91    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f555,f94])).
% 3.76/0.91  fof(f555,plain,(
% 3.76/0.91    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.91    inference(subsumption_resolution,[],[f494,f95])).
% 3.76/0.92  fof(f494,plain,(
% 3.76/0.92    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.92    inference(resolution,[],[f368,f127])).
% 3.76/0.92  fof(f127,plain,(
% 3.76/0.92    ( ! [X0,X1] : (k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.92    inference(cnf_transformation,[],[f54])).
% 3.76/0.92  fof(f54,plain,(
% 3.76/0.92    ! [X0] : (! [X1] : (k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(flattening,[],[f53])).
% 3.76/0.92  fof(f53,plain,(
% 3.76/0.92    ! [X0] : (! [X1] : (k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.92    inference(ennf_transformation,[],[f22])).
% 3.76/0.92  fof(f22,axiom,(
% 3.76/0.92    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)))),
% 3.76/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattices)).
% 3.76/0.92  fof(f6638,plain,(
% 3.76/0.92    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK1)),k5_lattices(sK0)),k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))),
% 3.76/0.92    inference(resolution,[],[f876,f572])).
% 3.76/0.92  fof(f876,plain,(
% 3.76/0.92    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k5_lattices(sK0)),k4_lattices(sK0,sK1,X1))) )),
% 3.76/0.92    inference(forward_demodulation,[],[f875,f354])).
% 3.76/0.92  fof(f354,plain,(
% 3.76/0.92    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 3.76/0.92    inference(subsumption_resolution,[],[f353,f92])).
% 3.76/0.92  fof(f353,plain,(
% 3.76/0.92    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) | v2_struct_0(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f352,f93])).
% 3.76/0.92  fof(f352,plain,(
% 3.76/0.92    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f351,f94])).
% 3.76/0.92  fof(f351,plain,(
% 3.76/0.92    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f292,f95])).
% 3.76/0.92  fof(f292,plain,(
% 3.76/0.92    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.92    inference(resolution,[],[f96,f127])).
% 3.76/0.92  fof(f875,plain,(
% 3.76/0.92    ( ! [X1] : (k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f874,f92])).
% 3.76/0.92  fof(f874,plain,(
% 3.76/0.92    ( ! [X1] : (k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f873,f93])).
% 3.76/0.92  fof(f873,plain,(
% 3.76/0.92    ( ! [X1] : (k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f872,f186])).
% 3.76/0.92  fof(f186,plain,(
% 3.76/0.92    v11_lattices(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f185,f95])).
% 3.76/0.92  fof(f185,plain,(
% 3.76/0.92    v11_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f145,f94])).
% 3.76/0.92  fof(f145,plain,(
% 3.76/0.92    v11_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.92    inference(resolution,[],[f92,f104])).
% 3.76/0.92  fof(f104,plain,(
% 3.76/0.92    ( ! [X0] : (v11_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.76/0.92    inference(cnf_transformation,[],[f32])).
% 3.76/0.92  fof(f872,plain,(
% 3.76/0.92    ( ! [X1] : (k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f871,f95])).
% 3.76/0.92  fof(f871,plain,(
% 3.76/0.92    ( ! [X1] : (k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f870,f368])).
% 3.76/0.92  fof(f870,plain,(
% 3.76/0.92    ( ! [X1] : (k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f856,f96])).
% 3.76/0.92  fof(f856,plain,(
% 3.76/0.92    ( ! [X1] : (k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),k4_lattices(sK0,sK1,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,k7_lattices(sK0,sK1)),k6_lattices(sK0)),k3_lattices(sK0,sK1,X1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(superposition,[],[f125,f350])).
% 3.76/0.92  fof(f350,plain,(
% 3.76/0.92    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 3.76/0.92    inference(subsumption_resolution,[],[f349,f92])).
% 3.76/0.92  fof(f349,plain,(
% 3.76/0.92    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) | v2_struct_0(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f348,f93])).
% 3.76/0.92  fof(f348,plain,(
% 3.76/0.92    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f347,f94])).
% 3.76/0.92  fof(f347,plain,(
% 3.76/0.92    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f291,f95])).
% 3.76/0.92  fof(f291,plain,(
% 3.76/0.92    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.92    inference(resolution,[],[f96,f126])).
% 3.76/0.92  fof(f125,plain,(
% 3.76/0.92    ( ! [X2,X0,X3,X1] : (k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) = k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.92    inference(cnf_transformation,[],[f50])).
% 3.76/0.92  fof(f50,plain,(
% 3.76/0.92    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) = k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(flattening,[],[f49])).
% 3.76/0.92  fof(f49,plain,(
% 3.76/0.92    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) = k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.92    inference(ennf_transformation,[],[f19])).
% 3.76/0.92  fof(f19,axiom,(
% 3.76/0.92    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) = k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1))))))),
% 3.76/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattices)).
% 3.76/0.92  fof(f3380,plain,(
% 3.76/0.92    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),sK1)),
% 3.76/0.92    inference(forward_demodulation,[],[f3363,f1793])).
% 3.76/0.92  fof(f1793,plain,(
% 3.76/0.92    k4_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1)),
% 3.76/0.92    inference(resolution,[],[f572,f398])).
% 3.76/0.92  fof(f398,plain,(
% 3.76/0.92    ( ! [X26] : (~m1_subset_1(X26,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X26) = k4_lattices(sK0,X26,sK1)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f397,f92])).
% 3.76/0.92  fof(f397,plain,(
% 3.76/0.92    ( ! [X26] : (k4_lattices(sK0,sK1,X26) = k4_lattices(sK0,X26,sK1) | ~m1_subset_1(X26,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f396,f196])).
% 3.76/0.92  fof(f396,plain,(
% 3.76/0.92    ( ! [X26] : (k4_lattices(sK0,sK1,X26) = k4_lattices(sK0,X26,sK1) | ~m1_subset_1(X26,u1_struct_0(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f308,f252])).
% 3.76/0.92  fof(f308,plain,(
% 3.76/0.92    ( ! [X26] : (k4_lattices(sK0,sK1,X26) = k4_lattices(sK0,X26,sK1) | ~m1_subset_1(X26,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(resolution,[],[f96,f142])).
% 3.76/0.92  fof(f142,plain,(
% 3.76/0.92    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.92    inference(cnf_transformation,[],[f72])).
% 3.76/0.92  fof(f72,plain,(
% 3.76/0.92    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(flattening,[],[f71])).
% 3.76/0.92  fof(f71,plain,(
% 3.76/0.92    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.92    inference(ennf_transformation,[],[f5])).
% 3.76/0.92  fof(f5,axiom,(
% 3.76/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 3.76/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 3.76/0.92  fof(f3363,plain,(
% 3.76/0.92    sK1 = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1),sK1)),
% 3.76/0.92    inference(resolution,[],[f1406,f572])).
% 3.76/0.92  fof(f1406,plain,(
% 3.76/0.92    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k4_lattices(sK0,X0,sK1),sK1)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f1405,f92])).
% 3.76/0.92  fof(f1405,plain,(
% 3.76/0.92    ( ! [X0] : (sK1 = k1_lattices(sK0,k4_lattices(sK0,X0,sK1),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f1404,f196])).
% 3.76/0.92  fof(f1404,plain,(
% 3.76/0.92    ( ! [X0] : (sK1 = k1_lattices(sK0,k4_lattices(sK0,X0,sK1),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f1403,f252])).
% 3.76/0.92  fof(f1403,plain,(
% 3.76/0.92    ( ! [X0] : (sK1 = k1_lattices(sK0,k4_lattices(sK0,X0,sK1),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f1402,f96])).
% 3.76/0.92  fof(f1402,plain,(
% 3.76/0.92    ( ! [X0] : (sK1 = k1_lattices(sK0,k4_lattices(sK0,X0,sK1),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(duplicate_literal_removal,[],[f1396])).
% 3.76/0.92  fof(f1396,plain,(
% 3.76/0.92    ( ! [X0] : (sK1 = k1_lattices(sK0,k4_lattices(sK0,X0,sK1),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(superposition,[],[f366,f141])).
% 3.76/0.92  fof(f141,plain,(
% 3.76/0.92    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.92    inference(cnf_transformation,[],[f70])).
% 3.76/0.92  fof(f70,plain,(
% 3.76/0.92    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(flattening,[],[f69])).
% 3.76/0.92  fof(f69,plain,(
% 3.76/0.92    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.92    inference(ennf_transformation,[],[f16])).
% 3.76/0.92  fof(f16,axiom,(
% 3.76/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 3.76/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 3.76/0.92  fof(f366,plain,(
% 3.76/0.92    ( ! [X15] : (sK1 = k1_lattices(sK0,k2_lattices(sK0,X15,sK1),sK1) | ~m1_subset_1(X15,u1_struct_0(sK0))) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f365,f92])).
% 3.76/0.92  fof(f365,plain,(
% 3.76/0.92    ( ! [X15] : (sK1 = k1_lattices(sK0,k2_lattices(sK0,X15,sK1),sK1) | ~m1_subset_1(X15,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f364,f95])).
% 3.76/0.92  fof(f364,plain,(
% 3.76/0.92    ( ! [X15] : (sK1 = k1_lattices(sK0,k2_lattices(sK0,X15,sK1),sK1) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f296,f200])).
% 3.76/0.92  fof(f296,plain,(
% 3.76/0.92    ( ! [X15] : (sK1 = k1_lattices(sK0,k2_lattices(sK0,X15,sK1),sK1) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(resolution,[],[f96,f132])).
% 3.76/0.92  fof(f132,plain,(
% 3.76/0.92    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.92    inference(cnf_transformation,[],[f91])).
% 3.76/0.92  fof(f91,plain,(
% 3.76/0.92    ! [X0] : (((v8_lattices(X0) | ((sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0)) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f88,f90,f89])).
% 3.76/0.92  fof(f89,plain,(
% 3.76/0.92    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 3.76/0.92    introduced(choice_axiom,[])).
% 3.76/0.92  fof(f90,plain,(
% 3.76/0.92    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0)) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 3.76/0.92    introduced(choice_axiom,[])).
% 3.76/0.92  fof(f88,plain,(
% 3.76/0.92    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(rectify,[],[f87])).
% 3.76/0.92  fof(f87,plain,(
% 3.76/0.92    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(nnf_transformation,[],[f58])).
% 3.76/0.92  fof(f58,plain,(
% 3.76/0.92    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(flattening,[],[f57])).
% 3.76/0.92  fof(f57,plain,(
% 3.76/0.92    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.92    inference(ennf_transformation,[],[f7])).
% 3.76/0.92  fof(f7,axiom,(
% 3.76/0.92    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 3.76/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).
% 3.76/0.92  fof(f3607,plain,(
% 3.76/0.92    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k1_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),sK1)),
% 3.76/0.92    inference(forward_demodulation,[],[f3590,f1823])).
% 3.76/0.92  fof(f1823,plain,(
% 3.76/0.92    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1)),
% 3.76/0.92    inference(backward_demodulation,[],[f1789,f1790])).
% 3.76/0.92  fof(f1790,plain,(
% 3.76/0.92    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1)),
% 3.76/0.92    inference(resolution,[],[f572,f383])).
% 3.76/0.92  fof(f383,plain,(
% 3.76/0.92    ( ! [X20] : (~m1_subset_1(X20,u1_struct_0(sK0)) | k3_lattices(sK0,sK1,X20) = k3_lattices(sK0,X20,sK1)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f382,f92])).
% 3.76/0.92  fof(f382,plain,(
% 3.76/0.92    ( ! [X20] : (k3_lattices(sK0,sK1,X20) = k3_lattices(sK0,X20,sK1) | ~m1_subset_1(X20,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f381,f192])).
% 3.76/0.92  fof(f381,plain,(
% 3.76/0.92    ( ! [X20] : (k3_lattices(sK0,sK1,X20) = k3_lattices(sK0,X20,sK1) | ~m1_subset_1(X20,u1_struct_0(sK0)) | ~v4_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f302,f253])).
% 3.76/0.92  fof(f302,plain,(
% 3.76/0.92    ( ! [X20] : (k3_lattices(sK0,sK1,X20) = k3_lattices(sK0,X20,sK1) | ~m1_subset_1(X20,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(resolution,[],[f96,f139])).
% 3.76/0.92  fof(f139,plain,(
% 3.76/0.92    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.92    inference(cnf_transformation,[],[f66])).
% 3.76/0.92  fof(f66,plain,(
% 3.76/0.92    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(flattening,[],[f65])).
% 3.76/0.92  fof(f65,plain,(
% 3.76/0.92    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.92    inference(ennf_transformation,[],[f4])).
% 3.76/0.92  fof(f4,axiom,(
% 3.76/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 3.76/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 3.76/0.92  fof(f1789,plain,(
% 3.76/0.92    k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) = k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1)),
% 3.76/0.92    inference(resolution,[],[f572,f380])).
% 3.76/0.92  fof(f380,plain,(
% 3.76/0.92    ( ! [X19] : (~m1_subset_1(X19,u1_struct_0(sK0)) | k3_lattices(sK0,X19,sK1) = k1_lattices(sK0,X19,sK1)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f379,f92])).
% 3.76/0.92  fof(f379,plain,(
% 3.76/0.92    ( ! [X19] : (k3_lattices(sK0,X19,sK1) = k1_lattices(sK0,X19,sK1) | ~m1_subset_1(X19,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f378,f192])).
% 3.76/0.92  fof(f378,plain,(
% 3.76/0.92    ( ! [X19] : (k3_lattices(sK0,X19,sK1) = k1_lattices(sK0,X19,sK1) | ~m1_subset_1(X19,u1_struct_0(sK0)) | ~v4_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f301,f253])).
% 3.76/0.92  fof(f301,plain,(
% 3.76/0.92    ( ! [X19] : (k3_lattices(sK0,X19,sK1) = k1_lattices(sK0,X19,sK1) | ~m1_subset_1(X19,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(resolution,[],[f96,f138])).
% 3.76/0.92  fof(f138,plain,(
% 3.76/0.92    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.92    inference(cnf_transformation,[],[f64])).
% 3.76/0.92  fof(f64,plain,(
% 3.76/0.92    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(flattening,[],[f63])).
% 3.76/0.92  fof(f63,plain,(
% 3.76/0.92    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.92    inference(ennf_transformation,[],[f15])).
% 3.76/0.92  fof(f15,axiom,(
% 3.76/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 3.76/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 3.76/0.92  fof(f3590,plain,(
% 3.76/0.92    k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1) = k1_lattices(sK0,k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1),sK1)),
% 3.76/0.92    inference(resolution,[],[f1971,f572])).
% 3.76/0.92  fof(f1971,plain,(
% 3.76/0.92    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | k1_lattices(sK0,X6,sK1) = k1_lattices(sK0,k1_lattices(sK0,X6,sK1),sK1)) )),
% 3.76/0.92    inference(forward_demodulation,[],[f1958,f314])).
% 3.76/0.92  fof(f314,plain,(
% 3.76/0.92    sK1 = k1_lattices(sK0,sK1,sK1)),
% 3.76/0.92    inference(subsumption_resolution,[],[f313,f92])).
% 3.76/0.92  fof(f313,plain,(
% 3.76/0.92    sK1 = k1_lattices(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f312,f196])).
% 3.76/0.92  fof(f312,plain,(
% 3.76/0.92    sK1 = k1_lattices(sK0,sK1,sK1) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f311,f200])).
% 3.76/0.92  fof(f311,plain,(
% 3.76/0.92    sK1 = k1_lattices(sK0,sK1,sK1) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f310,f202])).
% 3.76/0.92  fof(f310,plain,(
% 3.76/0.92    sK1 = k1_lattices(sK0,sK1,sK1) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f281,f95])).
% 3.76/0.92  fof(f281,plain,(
% 3.76/0.92    sK1 = k1_lattices(sK0,sK1,sK1) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 3.76/0.92    inference(resolution,[],[f96,f115])).
% 3.76/0.92  fof(f115,plain,(
% 3.76/0.92    ( ! [X0,X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.92    inference(cnf_transformation,[],[f38])).
% 3.76/0.92  fof(f38,plain,(
% 3.76/0.92    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(flattening,[],[f37])).
% 3.76/0.92  fof(f37,plain,(
% 3.76/0.92    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.92    inference(ennf_transformation,[],[f17])).
% 3.76/0.92  fof(f17,axiom,(
% 3.76/0.92    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 3.76/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).
% 3.76/0.92  fof(f1958,plain,(
% 3.76/0.92    ( ! [X6] : (k1_lattices(sK0,X6,k1_lattices(sK0,sK1,sK1)) = k1_lattices(sK0,k1_lattices(sK0,X6,sK1),sK1) | ~m1_subset_1(X6,u1_struct_0(sK0))) )),
% 3.76/0.92    inference(resolution,[],[f325,f96])).
% 3.76/0.92  fof(f325,plain,(
% 3.76/0.92    ( ! [X2,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k1_lattices(sK0,X2,k1_lattices(sK0,sK1,X3)) = k1_lattices(sK0,k1_lattices(sK0,X2,sK1),X3) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f324,f92])).
% 3.76/0.92  fof(f324,plain,(
% 3.76/0.92    ( ! [X2,X3] : (k1_lattices(sK0,X2,k1_lattices(sK0,sK1,X3)) = k1_lattices(sK0,k1_lattices(sK0,X2,sK1),X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f323,f253])).
% 3.76/0.92  fof(f323,plain,(
% 3.76/0.92    ( ! [X2,X3] : (k1_lattices(sK0,X2,k1_lattices(sK0,sK1,X3)) = k1_lattices(sK0,k1_lattices(sK0,X2,sK1),X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f284,f194])).
% 3.76/0.92  fof(f194,plain,(
% 3.76/0.92    v5_lattices(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f193,f95])).
% 3.76/0.92  fof(f193,plain,(
% 3.76/0.92    v5_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.92    inference(subsumption_resolution,[],[f149,f93])).
% 3.76/0.92  fof(f149,plain,(
% 3.76/0.92    v5_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 3.76/0.92    inference(resolution,[],[f92,f109])).
% 3.76/0.92  fof(f109,plain,(
% 3.76/0.92    ( ! [X0] : (v5_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.76/0.92    inference(cnf_transformation,[],[f34])).
% 3.76/0.92  fof(f284,plain,(
% 3.76/0.92    ( ! [X2,X3] : (k1_lattices(sK0,X2,k1_lattices(sK0,sK1,X3)) = k1_lattices(sK0,k1_lattices(sK0,X2,sK1),X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v5_lattices(sK0) | ~l2_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(resolution,[],[f96,f118])).
% 3.76/0.92  fof(f118,plain,(
% 3.76/0.92    ( ! [X6,X4,X0,X5] : (k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v5_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.92    inference(cnf_transformation,[],[f81])).
% 3.76/0.92  fof(f81,plain,(
% 3.76/0.92    ! [X0] : (((v5_lattices(X0) | (((k1_lattices(X0,sK2(X0),k1_lattices(X0,sK3(X0),sK4(X0))) != k1_lattices(X0,k1_lattices(X0,sK2(X0),sK3(X0)),sK4(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v5_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f77,f80,f79,f78])).
% 3.76/0.92  fof(f78,plain,(
% 3.76/0.92    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_lattices(X0,sK2(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK2(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 3.76/0.92    introduced(choice_axiom,[])).
% 3.76/0.92  fof(f79,plain,(
% 3.76/0.92    ! [X0] : (? [X2] : (? [X3] : (k1_lattices(X0,sK2(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK2(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k1_lattices(X0,sK2(X0),k1_lattices(X0,sK3(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK2(X0),sK3(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 3.76/0.92    introduced(choice_axiom,[])).
% 3.76/0.92  fof(f80,plain,(
% 3.76/0.92    ! [X0] : (? [X3] : (k1_lattices(X0,sK2(X0),k1_lattices(X0,sK3(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK2(X0),sK3(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_lattices(X0,sK2(X0),k1_lattices(X0,sK3(X0),sK4(X0))) != k1_lattices(X0,k1_lattices(X0,sK2(X0),sK3(X0)),sK4(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 3.76/0.92    introduced(choice_axiom,[])).
% 3.76/0.92  fof(f77,plain,(
% 3.76/0.92    ! [X0] : (((v5_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v5_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(rectify,[],[f76])).
% 3.76/0.92  fof(f76,plain,(
% 3.76/0.92    ! [X0] : (((v5_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v5_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(nnf_transformation,[],[f44])).
% 3.76/0.92  fof(f44,plain,(
% 3.76/0.92    ! [X0] : ((v5_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(flattening,[],[f43])).
% 3.76/0.92  fof(f43,plain,(
% 3.76/0.92    ! [X0] : ((v5_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.92    inference(ennf_transformation,[],[f6])).
% 3.76/0.92  fof(f6,axiom,(
% 3.76/0.92    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v5_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3))))))),
% 3.76/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattices)).
% 3.76/0.92  fof(f6682,plain,(
% 3.76/0.92    k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1)),
% 3.76/0.92    inference(backward_demodulation,[],[f1793,f6680])).
% 3.76/0.92  fof(f6782,plain,(
% 3.76/0.92    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1)),
% 3.76/0.92    inference(backward_demodulation,[],[f4512,f6775])).
% 3.76/0.92  fof(f4512,plain,(
% 3.76/0.92    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))),
% 3.76/0.92    inference(subsumption_resolution,[],[f4511,f1787])).
% 3.76/0.92  fof(f4511,plain,(
% 3.76/0.92    ~m1_subset_1(k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))),u1_struct_0(sK0)) | k7_lattices(sK0,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1))))),
% 3.76/0.92    inference(forward_demodulation,[],[f4510,f1823])).
% 3.76/0.92  fof(f4510,plain,(
% 3.76/0.92    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK1,k7_lattices(sK0,k7_lattices(sK0,sK1)))) | ~m1_subset_1(k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1),u1_struct_0(sK0))),
% 3.76/0.92    inference(forward_demodulation,[],[f4493,f1823])).
% 3.76/0.92  fof(f4493,plain,(
% 3.76/0.92    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1)) | ~m1_subset_1(k1_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK1),u1_struct_0(sK0))),
% 3.76/0.92    inference(resolution,[],[f1352,f572])).
% 3.76/0.92  fof(f1352,plain,(
% 3.76/0.92    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k4_lattices(sK0,X2,k1_lattices(sK0,X2,sK1)) = X2 | ~m1_subset_1(k1_lattices(sK0,X2,sK1),u1_struct_0(sK0))) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f1351,f92])).
% 3.76/0.92  fof(f1351,plain,(
% 3.76/0.92    ( ! [X2] : (k4_lattices(sK0,X2,k1_lattices(sK0,X2,sK1)) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(k1_lattices(sK0,X2,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f1350,f196])).
% 3.76/0.92  fof(f1350,plain,(
% 3.76/0.92    ( ! [X2] : (k4_lattices(sK0,X2,k1_lattices(sK0,X2,sK1)) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(k1_lattices(sK0,X2,sK1),u1_struct_0(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f1334,f252])).
% 3.76/0.92  fof(f1334,plain,(
% 3.76/0.92    ( ! [X2] : (k4_lattices(sK0,X2,k1_lattices(sK0,X2,sK1)) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(k1_lattices(sK0,X2,sK1),u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(duplicate_literal_removal,[],[f1329])).
% 3.76/0.92  fof(f1329,plain,(
% 3.76/0.92    ( ! [X2] : (k4_lattices(sK0,X2,k1_lattices(sK0,X2,sK1)) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(k1_lattices(sK0,X2,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(superposition,[],[f360,f141])).
% 3.76/0.92  fof(f360,plain,(
% 3.76/0.92    ( ! [X13] : (k2_lattices(sK0,X13,k1_lattices(sK0,X13,sK1)) = X13 | ~m1_subset_1(X13,u1_struct_0(sK0))) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f359,f92])).
% 3.76/0.92  fof(f359,plain,(
% 3.76/0.92    ( ! [X13] : (k2_lattices(sK0,X13,k1_lattices(sK0,X13,sK1)) = X13 | ~m1_subset_1(X13,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f358,f95])).
% 3.76/0.92  fof(f358,plain,(
% 3.76/0.92    ( ! [X13] : (k2_lattices(sK0,X13,k1_lattices(sK0,X13,sK1)) = X13 | ~m1_subset_1(X13,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(subsumption_resolution,[],[f294,f202])).
% 3.76/0.92  fof(f294,plain,(
% 3.76/0.92    ( ! [X13] : (k2_lattices(sK0,X13,k1_lattices(sK0,X13,sK1)) = X13 | ~m1_subset_1(X13,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 3.76/0.92    inference(resolution,[],[f96,f128])).
% 3.76/0.92  fof(f128,plain,(
% 3.76/0.92    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/0.92    inference(cnf_transformation,[],[f86])).
% 3.76/0.92  fof(f86,plain,(
% 3.76/0.92    ! [X0] : (((v9_lattices(X0) | ((sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f83,f85,f84])).
% 3.76/0.92  fof(f84,plain,(
% 3.76/0.92    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 3.76/0.92    introduced(choice_axiom,[])).
% 3.76/0.92  fof(f85,plain,(
% 3.76/0.92    ! [X0] : (? [X2] : (sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 3.76/0.92    introduced(choice_axiom,[])).
% 3.76/0.92  fof(f83,plain,(
% 3.76/0.92    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(rectify,[],[f82])).
% 3.76/0.92  fof(f82,plain,(
% 3.76/0.92    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(nnf_transformation,[],[f56])).
% 3.76/0.92  fof(f56,plain,(
% 3.76/0.92    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/0.92    inference(flattening,[],[f55])).
% 3.76/0.92  fof(f55,plain,(
% 3.76/0.92    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.76/0.92    inference(ennf_transformation,[],[f8])).
% 3.76/0.92  fof(f8,axiom,(
% 3.76/0.92    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 3.76/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 3.76/0.92  % SZS output end Proof for theBenchmark
% 3.76/0.92  % (7333)------------------------------
% 3.76/0.92  % (7333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.76/0.92  % (7333)Termination reason: Refutation
% 3.76/0.92  
% 3.76/0.92  % (7333)Memory used [KB]: 5245
% 3.76/0.92  % (7333)Time elapsed: 0.491 s
% 3.76/0.92  % (7333)------------------------------
% 3.76/0.92  % (7333)------------------------------
% 3.76/0.92  % (7321)Success in time 0.57 s
%------------------------------------------------------------------------------

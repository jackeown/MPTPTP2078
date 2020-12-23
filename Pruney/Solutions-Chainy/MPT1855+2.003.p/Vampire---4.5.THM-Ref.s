%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:50 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :  224 (14819 expanded)
%              Number of leaves         :   18 (4480 expanded)
%              Depth                    :   32
%              Number of atoms          :  683 (87001 expanded)
%              Number of equality atoms :  148 (12265 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1522,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1515,f1508])).

fof(f1508,plain,(
    k1_tex_2(sK0,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK2(sK1)))) ),
    inference(backward_demodulation,[],[f1138,f1483])).

fof(f1483,plain,(
    k1_tex_2(sK1,sK2(sK1)) = k1_tex_2(sK0,sK2(sK1)) ),
    inference(backward_demodulation,[],[f1105,f1482])).

fof(f1482,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1)) ),
    inference(trivial_inequality_removal,[],[f1475])).

fof(f1475,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1)) ),
    inference(backward_demodulation,[],[f1150,f1465])).

fof(f1465,plain,(
    u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK2(sK1))) ),
    inference(subsumption_resolution,[],[f1464,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2))) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    & m1_pre_topc(sK1,sK0)
    & v7_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_pre_topc(X1,sK0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2)))
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_pre_topc(X1,sK0)
        & v7_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2))) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_pre_topc(sK1,sK0)
      & v7_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tex_2)).

fof(f1464,plain,
    ( u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1463,f84])).

fof(f84,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f58,f52])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f1463,plain,
    ( u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f644,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f644,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK2(sK1))) ),
    inference(backward_demodulation,[],[f536,f643])).

fof(f643,plain,(
    u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) ),
    inference(subsumption_resolution,[],[f642,f51])).

fof(f642,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f641,f52])).

fof(f641,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f640,f472])).

fof(f472,plain,(
    m1_subset_1(sK2(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f471,f51])).

fof(f471,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f464,f52])).

fof(f464,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f169,f55])).

fof(f55,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f169,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | m1_subset_1(sK2(sK1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f163,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f163,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK1),u1_struct_0(X0))
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f116,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f116,plain,(
    m1_subset_1(sK2(sK1),u1_struct_0(sK1)) ),
    inference(resolution,[],[f94,f96])).

fof(f96,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f87,f58])).

fof(f87,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f86,f52])).

fof(f86,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f62,f55])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f94,plain,
    ( ~ l1_struct_0(sK1)
    | m1_subset_1(sK2(sK1),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f93,f53])).

fof(f93,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f67,f54])).

fof(f54,plain,(
    v7_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK2(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK2(X0))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f44])).

% (15457)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
fof(f44,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_1)).

fof(f640,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f639,f522])).

fof(f522,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK2(sK1))) ),
    inference(subsumption_resolution,[],[f521,f51])).

fof(f521,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f511,f52])).

fof(f511,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f472,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f639,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | v2_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f637,f526])).

fof(f526,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f525,f51])).

fof(f525,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f513,f52])).

fof(f513,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f472,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f637,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0)
    | u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | v2_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f524,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(X2) )
                & ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

fof(f524,plain,(
    v1_pre_topc(k1_tex_2(sK0,sK2(sK1))) ),
    inference(subsumption_resolution,[],[f523,f51])).

fof(f523,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK2(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f512,f52])).

fof(f512,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK2(sK1)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f472,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_pre_topc(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f536,plain,
    ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f517,f298])).

fof(f298,plain,(
    u1_struct_0(sK1) = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f297,f53])).

fof(f297,plain,
    ( u1_struct_0(sK1) = k1_tarski(sK2(sK1))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f296,f96])).

fof(f296,plain,
    ( u1_struct_0(sK1) = k1_tarski(sK2(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f176,f66])).

fof(f176,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK1) = k1_tarski(sK2(sK1)) ),
    inference(forward_demodulation,[],[f168,f104])).

fof(f104,plain,(
    u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1)) ),
    inference(subsumption_resolution,[],[f103,f53])).

fof(f103,plain,
    ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f102,f96])).

fof(f102,plain,
    ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f68,f54])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK2(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f168,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f116,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f517,plain,
    ( k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f472,f74])).

fof(f1150,plain,
    ( u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1)) ),
    inference(subsumption_resolution,[],[f1126,f175])).

fof(f175,plain,(
    ~ v2_struct_0(k1_tex_2(sK1,sK2(sK1))) ),
    inference(subsumption_resolution,[],[f174,f53])).

fof(f174,plain,
    ( ~ v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f167,f87])).

fof(f167,plain,
    ( ~ v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f116,f75])).

fof(f1126,plain,
    ( v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1)) ),
    inference(backward_demodulation,[],[f647,f1105])).

fof(f647,plain,
    ( u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK0,sK2(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(backward_demodulation,[],[f529,f643])).

fof(f529,plain,
    ( u1_struct_0(sK1) != k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f528,f51])).

fof(f528,plain,
    ( u1_struct_0(sK1) != k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f527,f52])).

fof(f527,plain,
    ( u1_struct_0(sK1) != k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f514,f98])).

fof(f98,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f97,f52])).

fof(f97,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f65,f55])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f514,plain,
    ( u1_struct_0(sK1) != k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f472,f302])).

fof(f302,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(sK1)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
      | k1_tex_2(X0,X1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(backward_demodulation,[],[f115,f301])).

fof(f301,plain,(
    u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f300,f225])).

fof(f225,plain,(
    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f222,f87])).

fof(f222,plain,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f134,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f134,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) ),
    inference(subsumption_resolution,[],[f128,f87])).

fof(f128,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f95,f65])).

fof(f95,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f87,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f300,plain,
    ( u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK1)) ),
    inference(resolution,[],[f218,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f218,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f213,f126])).

fof(f126,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f121,f52])).

fof(f121,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f98,f62])).

fof(f213,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f133,f63])).

fof(f133,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f132,f87])).

fof(f132,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f95,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
      | k1_tex_2(X0,X1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f92,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(X2)
      | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | k1_tex_2(X0,X1) = X2
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f92,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f91,f52])).

fof(f91,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f64,f55])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1105,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1)) ),
    inference(resolution,[],[f624,f695])).

fof(f695,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f694,f175])).

fof(f694,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(k1_tex_2(sK1,sK2(sK1))) ),
    inference(subsumption_resolution,[],[f682,f352])).

fof(f352,plain,(
    l1_struct_0(k1_tex_2(sK1,sK2(sK1))) ),
    inference(resolution,[],[f286,f58])).

fof(f286,plain,(
    l1_pre_topc(k1_tex_2(sK1,sK2(sK1))) ),
    inference(subsumption_resolution,[],[f278,f87])).

fof(f278,plain,
    ( l1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f171,f62])).

fof(f171,plain,(
    m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1) ),
    inference(subsumption_resolution,[],[f170,f53])).

fof(f170,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f165,f87])).

fof(f165,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f116,f77])).

fof(f682,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | v2_struct_0(k1_tex_2(sK1,sK2(sK1))) ),
    inference(superposition,[],[f66,f201])).

fof(f201,plain,(
    u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) ),
    inference(forward_demodulation,[],[f200,f104])).

fof(f200,plain,(
    k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) ),
    inference(subsumption_resolution,[],[f199,f53])).

fof(f199,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f198,f87])).

fof(f198,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f197,f116])).

fof(f197,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f196,f175])).

fof(f196,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f194,f171])).

fof(f194,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1)
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | v2_struct_0(k1_tex_2(sK1,sK2(sK1)))
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f173,f81])).

fof(f173,plain,(
    v1_pre_topc(k1_tex_2(sK1,sK2(sK1))) ),
    inference(subsumption_resolution,[],[f172,f53])).

fof(f172,plain,
    ( v1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f166,f87])).

fof(f166,plain,
    ( v1_pre_topc(k1_tex_2(sK1,sK2(sK1)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f116,f76])).

fof(f624,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1)) ),
    inference(forward_demodulation,[],[f623,f301])).

fof(f623,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f622,f144])).

fof(f144,plain,(
    l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f126,f58])).

fof(f622,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(resolution,[],[f332,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f332,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1)) ),
    inference(trivial_inequality_removal,[],[f313])).

fof(f313,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(backward_demodulation,[],[f193,f301])).

fof(f193,plain,
    ( u1_struct_0(sK1) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f192,f104])).

fof(f192,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f191,f53])).

fof(f191,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f190,f87])).

fof(f190,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f189,f134])).

fof(f189,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f115,f116])).

fof(f1138,plain,(
    k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK1,sK2(sK1)))) ),
    inference(backward_demodulation,[],[f889,f1105])).

fof(f889,plain,(
    k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(subsumption_resolution,[],[f888,f695])).

fof(f888,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f887,f782])).

fof(f782,plain,(
    u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(subsumption_resolution,[],[f781,f463])).

fof(f463,plain,(
    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f460,f87])).

fof(f460,plain,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f316,f63])).

fof(f316,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK1) ),
    inference(backward_demodulation,[],[f224,f301])).

fof(f224,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK1) ),
    inference(subsumption_resolution,[],[f220,f87])).

fof(f220,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f134,f65])).

fof(f781,plain,
    ( u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_struct_0(sK1)) ),
    inference(resolution,[],[f456,f80])).

fof(f456,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(subsumption_resolution,[],[f452,f312])).

fof(f312,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(backward_demodulation,[],[f187,f301])).

fof(f187,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(subsumption_resolution,[],[f182,f52])).

fof(f182,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f123,f62])).

fof(f123,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK0) ),
    inference(subsumption_resolution,[],[f118,f52])).

fof(f118,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f98,f65])).

fof(f452,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(resolution,[],[f314,f63])).

fof(f314,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(backward_demodulation,[],[f217,f301])).

fof(f217,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(subsumption_resolution,[],[f216,f87])).

fof(f216,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f210,f126])).

fof(f210,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f133,f60])).

fof(f887,plain,
    ( k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(subsumption_resolution,[],[f886,f323])).

fof(f323,plain,(
    l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(backward_demodulation,[],[f248,f301])).

fof(f248,plain,(
    l1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(resolution,[],[f187,f58])).

fof(f886,plain,
    ( k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(resolution,[],[f823,f73])).

fof(f823,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(trivial_inequality_removal,[],[f794])).

fof(f794,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(backward_demodulation,[],[f344,f782])).

fof(f344,plain,
    ( u1_struct_0(sK1) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(forward_demodulation,[],[f343,f301])).

fof(f343,plain,
    ( u1_struct_0(sK1) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1)) ),
    inference(forward_demodulation,[],[f331,f301])).

fof(f331,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | u1_struct_0(sK1) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1)) ),
    inference(backward_demodulation,[],[f295,f301])).

fof(f295,plain,
    ( u1_struct_0(sK1) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(forward_demodulation,[],[f294,f104])).

fof(f294,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(subsumption_resolution,[],[f293,f53])).

fof(f293,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f292,f87])).

fof(f292,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f291,f224])).

fof(f291,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK1)
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1))
    | v2_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f177,f116])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),X0)
      | k1_tex_2(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      | v2_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f124,f71])).

fof(f124,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(subsumption_resolution,[],[f119,f52])).

fof(f119,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f98,f64])).

fof(f1515,plain,(
    k1_tex_2(sK0,sK2(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK2(sK1)))) ),
    inference(backward_demodulation,[],[f1474,f1483])).

fof(f1474,plain,(
    k1_tex_2(sK1,sK2(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK2(sK1)))) ),
    inference(backward_demodulation,[],[f1124,f1465])).

fof(f1124,plain,(
    k1_tex_2(sK1,sK2(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK2(sK1))),u1_pre_topc(k1_tex_2(sK0,sK2(sK1)))) ),
    inference(backward_demodulation,[],[f508,f1105])).

fof(f508,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK2(sK1))),u1_pre_topc(k1_tex_2(sK0,sK2(sK1)))) ),
    inference(resolution,[],[f472,f56])).

fof(f56,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2))) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:16:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.15/0.51  % (15410)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.15/0.52  % (15423)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.15/0.53  % (15417)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.27/0.53  % (15414)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.27/0.54  % (15428)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.54  % (15420)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.27/0.54  % (15408)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.27/0.54  % (15407)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.54  % (15411)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.55  % (15430)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.27/0.55  % (15412)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.27/0.55  % (15409)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.27/0.55  % (15405)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.55  % (15415)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.27/0.55  % (15431)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.27/0.55  % (15418)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.27/0.56  % (15433)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.27/0.56  % (15422)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.27/0.56  % (15429)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.27/0.56  % (15419)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.56  % (15432)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.27/0.56  % (15425)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.27/0.56  % (15416)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.27/0.56  % (15427)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.56  % (15424)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.27/0.57  % (15426)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.27/0.57  % (15406)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.57  % (15413)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.27/0.57  % (15415)Refutation not found, incomplete strategy% (15415)------------------------------
% 1.27/0.57  % (15415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.57  % (15415)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.57  
% 1.27/0.57  % (15415)Memory used [KB]: 10746
% 1.27/0.57  % (15415)Time elapsed: 0.138 s
% 1.27/0.57  % (15415)------------------------------
% 1.27/0.57  % (15415)------------------------------
% 1.27/0.58  % (15434)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.27/0.59  % (15421)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.27/0.60  % (15421)Refutation not found, incomplete strategy% (15421)------------------------------
% 1.27/0.60  % (15421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.60  % (15421)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.60  
% 1.27/0.60  % (15421)Memory used [KB]: 10618
% 1.27/0.60  % (15421)Time elapsed: 0.153 s
% 1.27/0.60  % (15421)------------------------------
% 1.27/0.60  % (15421)------------------------------
% 1.98/0.68  % (15412)Refutation found. Thanks to Tanya!
% 1.98/0.68  % SZS status Theorem for theBenchmark
% 1.98/0.68  % SZS output start Proof for theBenchmark
% 1.98/0.68  fof(f1522,plain,(
% 1.98/0.68    $false),
% 1.98/0.68    inference(subsumption_resolution,[],[f1515,f1508])).
% 1.98/0.68  fof(f1508,plain,(
% 1.98/0.68    k1_tex_2(sK0,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK2(sK1))))),
% 1.98/0.68    inference(backward_demodulation,[],[f1138,f1483])).
% 1.98/0.68  fof(f1483,plain,(
% 1.98/0.68    k1_tex_2(sK1,sK2(sK1)) = k1_tex_2(sK0,sK2(sK1))),
% 1.98/0.68    inference(backward_demodulation,[],[f1105,f1482])).
% 1.98/0.68  fof(f1482,plain,(
% 1.98/0.68    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1))),
% 1.98/0.68    inference(trivial_inequality_removal,[],[f1475])).
% 1.98/0.68  fof(f1475,plain,(
% 1.98/0.68    u1_struct_0(sK1) != u1_struct_0(sK1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1))),
% 1.98/0.68    inference(backward_demodulation,[],[f1150,f1465])).
% 1.98/0.68  fof(f1465,plain,(
% 1.98/0.68    u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK2(sK1)))),
% 1.98/0.68    inference(subsumption_resolution,[],[f1464,f51])).
% 1.98/0.68  fof(f51,plain,(
% 1.98/0.68    ~v2_struct_0(sK0)),
% 1.98/0.68    inference(cnf_transformation,[],[f42])).
% 1.98/0.68  fof(f42,plain,(
% 1.98/0.68    (! [X2] : (g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2))) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_pre_topc(sK1,sK0) & v7_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.98/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f41,f40])).
% 1.98/0.68  fof(f40,plain,(
% 1.98/0.68    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2))) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_pre_topc(X1,sK0) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.98/0.68    introduced(choice_axiom,[])).
% 1.98/0.68  fof(f41,plain,(
% 1.98/0.68    ? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2))) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_pre_topc(X1,sK0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (! [X2] : (g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2))) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_pre_topc(sK1,sK0) & v7_struct_0(sK1) & ~v2_struct_0(sK1))),
% 1.98/0.68    introduced(choice_axiom,[])).
% 1.98/0.68  fof(f19,plain,(
% 1.98/0.68    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.98/0.68    inference(flattening,[],[f18])).
% 1.98/0.68  fof(f18,plain,(
% 1.98/0.68    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & (m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.98/0.68    inference(ennf_transformation,[],[f17])).
% 1.98/0.68  fof(f17,negated_conjecture,(
% 1.98/0.68    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => ? [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.98/0.68    inference(negated_conjecture,[],[f16])).
% 1.98/0.68  fof(f16,conjecture,(
% 1.98/0.68    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => ? [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.98/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tex_2)).
% 1.98/0.68  fof(f1464,plain,(
% 1.98/0.68    u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK2(sK1))) | v2_struct_0(sK0)),
% 1.98/0.68    inference(subsumption_resolution,[],[f1463,f84])).
% 1.98/0.68  fof(f84,plain,(
% 1.98/0.68    l1_struct_0(sK0)),
% 1.98/0.68    inference(resolution,[],[f58,f52])).
% 1.98/0.68  fof(f52,plain,(
% 1.98/0.68    l1_pre_topc(sK0)),
% 1.98/0.68    inference(cnf_transformation,[],[f42])).
% 1.98/0.68  fof(f58,plain,(
% 1.98/0.68    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.98/0.68    inference(cnf_transformation,[],[f20])).
% 1.98/0.68  fof(f20,plain,(
% 1.98/0.68    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.98/0.68    inference(ennf_transformation,[],[f3])).
% 1.98/0.68  fof(f3,axiom,(
% 1.98/0.68    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.98/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.98/0.68  fof(f1463,plain,(
% 1.98/0.68    u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK2(sK1))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.98/0.68    inference(resolution,[],[f644,f66])).
% 1.98/0.68  fof(f66,plain,(
% 1.98/0.68    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.98/0.68    inference(cnf_transformation,[],[f27])).
% 1.98/0.68  fof(f27,plain,(
% 1.98/0.68    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.98/0.68    inference(flattening,[],[f26])).
% 1.98/0.68  fof(f26,plain,(
% 1.98/0.68    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.98/0.68    inference(ennf_transformation,[],[f6])).
% 1.98/0.68  fof(f6,axiom,(
% 1.98/0.68    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.98/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.98/0.68  fof(f644,plain,(
% 1.98/0.68    v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK2(sK1)))),
% 1.98/0.68    inference(backward_demodulation,[],[f536,f643])).
% 1.98/0.68  fof(f643,plain,(
% 1.98/0.68    u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))),
% 1.98/0.68    inference(subsumption_resolution,[],[f642,f51])).
% 1.98/0.68  fof(f642,plain,(
% 1.98/0.68    u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | v2_struct_0(sK0)),
% 1.98/0.68    inference(subsumption_resolution,[],[f641,f52])).
% 1.98/0.68  fof(f641,plain,(
% 1.98/0.68    u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.98/0.68    inference(subsumption_resolution,[],[f640,f472])).
% 1.98/0.68  fof(f472,plain,(
% 1.98/0.68    m1_subset_1(sK2(sK1),u1_struct_0(sK0))),
% 1.98/0.68    inference(subsumption_resolution,[],[f471,f51])).
% 1.98/0.68  fof(f471,plain,(
% 1.98/0.68    m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.98/0.68    inference(subsumption_resolution,[],[f464,f52])).
% 1.98/0.68  fof(f464,plain,(
% 1.98/0.68    m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.98/0.68    inference(resolution,[],[f169,f55])).
% 1.98/0.68  fof(f55,plain,(
% 1.98/0.68    m1_pre_topc(sK1,sK0)),
% 1.98/0.68    inference(cnf_transformation,[],[f42])).
% 1.98/0.68  fof(f169,plain,(
% 1.98/0.68    ( ! [X0] : (~m1_pre_topc(sK1,X0) | m1_subset_1(sK2(sK1),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.98/0.68    inference(subsumption_resolution,[],[f163,f53])).
% 1.98/0.68  fof(f53,plain,(
% 1.98/0.68    ~v2_struct_0(sK1)),
% 1.98/0.68    inference(cnf_transformation,[],[f42])).
% 1.98/0.68  fof(f163,plain,(
% 1.98/0.68    ( ! [X0] : (m1_subset_1(sK2(sK1),u1_struct_0(X0)) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.98/0.68    inference(resolution,[],[f116,f72])).
% 1.98/0.68  fof(f72,plain,(
% 1.98/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.98/0.68    inference(cnf_transformation,[],[f33])).
% 1.98/0.68  fof(f33,plain,(
% 1.98/0.68    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.98/0.68    inference(flattening,[],[f32])).
% 1.98/0.68  fof(f32,plain,(
% 1.98/0.68    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.98/0.68    inference(ennf_transformation,[],[f7])).
% 1.98/0.68  fof(f7,axiom,(
% 1.98/0.68    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.98/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.98/0.68  fof(f116,plain,(
% 1.98/0.68    m1_subset_1(sK2(sK1),u1_struct_0(sK1))),
% 1.98/0.68    inference(resolution,[],[f94,f96])).
% 1.98/0.68  fof(f96,plain,(
% 1.98/0.68    l1_struct_0(sK1)),
% 1.98/0.68    inference(resolution,[],[f87,f58])).
% 1.98/0.68  fof(f87,plain,(
% 1.98/0.68    l1_pre_topc(sK1)),
% 1.98/0.68    inference(subsumption_resolution,[],[f86,f52])).
% 1.98/0.68  fof(f86,plain,(
% 1.98/0.68    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.98/0.68    inference(resolution,[],[f62,f55])).
% 1.98/0.68  fof(f62,plain,(
% 1.98/0.68    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.98/0.68    inference(cnf_transformation,[],[f23])).
% 1.98/0.68  fof(f23,plain,(
% 1.98/0.68    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.98/0.68    inference(ennf_transformation,[],[f4])).
% 1.98/0.68  fof(f4,axiom,(
% 1.98/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.98/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.98/0.68  fof(f94,plain,(
% 1.98/0.68    ~l1_struct_0(sK1) | m1_subset_1(sK2(sK1),u1_struct_0(sK1))),
% 1.98/0.68    inference(subsumption_resolution,[],[f93,f53])).
% 1.98/0.68  fof(f93,plain,(
% 1.98/0.68    m1_subset_1(sK2(sK1),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.98/0.68    inference(resolution,[],[f67,f54])).
% 1.98/0.68  fof(f54,plain,(
% 1.98/0.68    v7_struct_0(sK1)),
% 1.98/0.68    inference(cnf_transformation,[],[f42])).
% 1.98/0.68  fof(f67,plain,(
% 1.98/0.68    ( ! [X0] : (~v7_struct_0(X0) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.98/0.68    inference(cnf_transformation,[],[f47])).
% 1.98/0.68  fof(f47,plain,(
% 1.98/0.68    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK2(X0)) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.98/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 1.98/0.68  fof(f46,plain,(
% 1.98/0.68    ! [X0] : (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) => (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK2(X0)) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 1.98/0.68    introduced(choice_axiom,[])).
% 1.98/0.68  fof(f45,plain,(
% 1.98/0.68    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.98/0.68    inference(rectify,[],[f44])).
% 1.98/0.69  % (15457)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.98/0.69  fof(f44,plain,(
% 1.98/0.69    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.98/0.69    inference(nnf_transformation,[],[f29])).
% 1.98/0.69  fof(f29,plain,(
% 1.98/0.69    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.98/0.69    inference(flattening,[],[f28])).
% 1.98/0.69  fof(f28,plain,(
% 1.98/0.69    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.98/0.69    inference(ennf_transformation,[],[f13])).
% 1.98/0.69  fof(f13,axiom,(
% 1.98/0.69    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 1.98/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_1)).
% 1.98/0.69  fof(f640,plain,(
% 1.98/0.69    u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.98/0.69    inference(subsumption_resolution,[],[f639,f522])).
% 1.98/0.69  fof(f522,plain,(
% 1.98/0.69    ~v2_struct_0(k1_tex_2(sK0,sK2(sK1)))),
% 1.98/0.69    inference(subsumption_resolution,[],[f521,f51])).
% 1.98/0.69  fof(f521,plain,(
% 1.98/0.69    ~v2_struct_0(k1_tex_2(sK0,sK2(sK1))) | v2_struct_0(sK0)),
% 1.98/0.69    inference(subsumption_resolution,[],[f511,f52])).
% 1.98/0.69  fof(f511,plain,(
% 1.98/0.69    ~v2_struct_0(k1_tex_2(sK0,sK2(sK1))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.98/0.69    inference(resolution,[],[f472,f75])).
% 1.98/0.69  fof(f75,plain,(
% 1.98/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.98/0.69    inference(cnf_transformation,[],[f39])).
% 1.98/0.69  fof(f39,plain,(
% 1.98/0.69    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.98/0.69    inference(flattening,[],[f38])).
% 1.98/0.69  fof(f38,plain,(
% 1.98/0.69    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.98/0.69    inference(ennf_transformation,[],[f15])).
% 1.98/0.69  fof(f15,axiom,(
% 1.98/0.69    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.98/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 1.98/0.69  fof(f639,plain,(
% 1.98/0.69    u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | v2_struct_0(k1_tex_2(sK0,sK2(sK1))) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.98/0.69    inference(subsumption_resolution,[],[f637,f526])).
% 1.98/0.69  fof(f526,plain,(
% 1.98/0.69    m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0)),
% 1.98/0.69    inference(subsumption_resolution,[],[f525,f51])).
% 1.98/0.69  fof(f525,plain,(
% 1.98/0.69    m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0) | v2_struct_0(sK0)),
% 1.98/0.69    inference(subsumption_resolution,[],[f513,f52])).
% 1.98/0.69  fof(f513,plain,(
% 1.98/0.69    m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.98/0.69    inference(resolution,[],[f472,f77])).
% 1.98/0.69  fof(f77,plain,(
% 1.98/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.98/0.69    inference(cnf_transformation,[],[f39])).
% 1.98/0.69  fof(f637,plain,(
% 1.98/0.69    ~m1_pre_topc(k1_tex_2(sK0,sK2(sK1)),sK0) | u1_struct_0(k1_tex_2(sK0,sK2(sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | v2_struct_0(k1_tex_2(sK0,sK2(sK1))) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.98/0.69    inference(resolution,[],[f524,f81])).
% 1.98/0.69  fof(f81,plain,(
% 1.98/0.69    ( ! [X0,X1] : (~v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.98/0.69    inference(equality_resolution,[],[f70])).
% 1.98/0.69  fof(f70,plain,(
% 1.98/0.69    ( ! [X2,X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.98/0.69    inference(cnf_transformation,[],[f48])).
% 1.98/0.69  fof(f48,plain,(
% 1.98/0.69    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(X2)) & (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.98/0.69    inference(nnf_transformation,[],[f31])).
% 1.98/0.69  fof(f31,plain,(
% 1.98/0.69    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.98/0.69    inference(flattening,[],[f30])).
% 1.98/0.69  fof(f30,plain,(
% 1.98/0.69    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.98/0.69    inference(ennf_transformation,[],[f14])).
% 1.98/0.69  fof(f14,axiom,(
% 1.98/0.69    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(X2)))))),
% 1.98/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).
% 1.98/0.69  fof(f524,plain,(
% 1.98/0.69    v1_pre_topc(k1_tex_2(sK0,sK2(sK1)))),
% 1.98/0.69    inference(subsumption_resolution,[],[f523,f51])).
% 1.98/0.69  fof(f523,plain,(
% 1.98/0.69    v1_pre_topc(k1_tex_2(sK0,sK2(sK1))) | v2_struct_0(sK0)),
% 1.98/0.69    inference(subsumption_resolution,[],[f512,f52])).
% 1.98/0.69  fof(f512,plain,(
% 1.98/0.69    v1_pre_topc(k1_tex_2(sK0,sK2(sK1))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.98/0.69    inference(resolution,[],[f472,f76])).
% 2.48/0.70  fof(f76,plain,(
% 2.48/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v1_pre_topc(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/0.70    inference(cnf_transformation,[],[f39])).
% 2.48/0.70  fof(f536,plain,(
% 2.48/0.70    u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 2.48/0.70    inference(forward_demodulation,[],[f517,f298])).
% 2.48/0.70  fof(f298,plain,(
% 2.48/0.70    u1_struct_0(sK1) = k1_tarski(sK2(sK1))),
% 2.48/0.70    inference(subsumption_resolution,[],[f297,f53])).
% 2.48/0.70  fof(f297,plain,(
% 2.48/0.70    u1_struct_0(sK1) = k1_tarski(sK2(sK1)) | v2_struct_0(sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f296,f96])).
% 2.48/0.70  fof(f296,plain,(
% 2.48/0.70    u1_struct_0(sK1) = k1_tarski(sK2(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 2.48/0.70    inference(resolution,[],[f176,f66])).
% 2.48/0.70  fof(f176,plain,(
% 2.48/0.70    v1_xboole_0(u1_struct_0(sK1)) | u1_struct_0(sK1) = k1_tarski(sK2(sK1))),
% 2.48/0.70    inference(forward_demodulation,[],[f168,f104])).
% 2.48/0.70  fof(f104,plain,(
% 2.48/0.70    u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1))),
% 2.48/0.70    inference(subsumption_resolution,[],[f103,f53])).
% 2.48/0.70  fof(f103,plain,(
% 2.48/0.70    u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1)) | v2_struct_0(sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f102,f96])).
% 2.48/0.70  fof(f102,plain,(
% 2.48/0.70    u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 2.48/0.70    inference(resolution,[],[f68,f54])).
% 2.48/0.70  fof(f68,plain,(
% 2.48/0.70    ( ! [X0] : (~v7_struct_0(X0) | u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK2(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.48/0.70    inference(cnf_transformation,[],[f47])).
% 2.48/0.70  fof(f168,plain,(
% 2.48/0.70    k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(u1_struct_0(sK1))),
% 2.48/0.70    inference(resolution,[],[f116,f74])).
% 2.48/0.70  fof(f74,plain,(
% 2.48/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 2.48/0.70    inference(cnf_transformation,[],[f37])).
% 2.48/0.70  fof(f37,plain,(
% 2.48/0.70    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.48/0.70    inference(flattening,[],[f36])).
% 2.48/0.70  fof(f36,plain,(
% 2.48/0.70    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.48/0.70    inference(ennf_transformation,[],[f9])).
% 2.48/0.70  fof(f9,axiom,(
% 2.48/0.70    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 2.48/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 2.48/0.70  fof(f517,plain,(
% 2.48/0.70    k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 2.48/0.70    inference(resolution,[],[f472,f74])).
% 2.48/0.70  fof(f1150,plain,(
% 2.48/0.70    u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK0,sK2(sK1))) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1))),
% 2.48/0.70    inference(subsumption_resolution,[],[f1126,f175])).
% 2.48/0.70  fof(f175,plain,(
% 2.48/0.70    ~v2_struct_0(k1_tex_2(sK1,sK2(sK1)))),
% 2.48/0.70    inference(subsumption_resolution,[],[f174,f53])).
% 2.48/0.70  fof(f174,plain,(
% 2.48/0.70    ~v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | v2_struct_0(sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f167,f87])).
% 2.48/0.70  fof(f167,plain,(
% 2.48/0.70    ~v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.48/0.70    inference(resolution,[],[f116,f75])).
% 2.48/0.70  fof(f1126,plain,(
% 2.48/0.70    v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK0,sK2(sK1))) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1))),
% 2.48/0.70    inference(backward_demodulation,[],[f647,f1105])).
% 2.48/0.70  fof(f647,plain,(
% 2.48/0.70    u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK0,sK2(sK1))) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.48/0.70    inference(backward_demodulation,[],[f529,f643])).
% 2.48/0.70  fof(f529,plain,(
% 2.48/0.70    u1_struct_0(sK1) != k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.48/0.70    inference(subsumption_resolution,[],[f528,f51])).
% 2.48/0.70  fof(f528,plain,(
% 2.48/0.70    u1_struct_0(sK1) != k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v2_struct_0(sK0)),
% 2.48/0.70    inference(subsumption_resolution,[],[f527,f52])).
% 2.48/0.70  fof(f527,plain,(
% 2.48/0.70    u1_struct_0(sK1) != k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.48/0.70    inference(subsumption_resolution,[],[f514,f98])).
% 2.48/0.70  fof(f98,plain,(
% 2.48/0.70    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)),
% 2.48/0.70    inference(subsumption_resolution,[],[f97,f52])).
% 2.48/0.70  fof(f97,plain,(
% 2.48/0.70    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(sK0)),
% 2.48/0.70    inference(resolution,[],[f65,f55])).
% 2.48/0.70  fof(f65,plain,(
% 2.48/0.70    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(X0)) )),
% 2.48/0.70    inference(cnf_transformation,[],[f25])).
% 2.48/0.70  fof(f25,plain,(
% 2.48/0.70    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.48/0.70    inference(ennf_transformation,[],[f10])).
% 2.48/0.70  fof(f10,axiom,(
% 2.48/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.48/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).
% 2.48/0.70  fof(f514,plain,(
% 2.48/0.70    u1_struct_0(sK1) != k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK0,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.48/0.70    inference(resolution,[],[f472,f302])).
% 2.48/0.70  fof(f302,plain,(
% 2.48/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(sK1) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) | k1_tex_2(X0,X1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/0.70    inference(backward_demodulation,[],[f115,f301])).
% 2.48/0.70  fof(f301,plain,(
% 2.48/0.70    u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.48/0.70    inference(subsumption_resolution,[],[f300,f225])).
% 2.48/0.70  fof(f225,plain,(
% 2.48/0.70    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK1))),
% 2.48/0.70    inference(subsumption_resolution,[],[f222,f87])).
% 2.48/0.70  fof(f222,plain,(
% 2.48/0.70    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 2.48/0.70    inference(resolution,[],[f134,f63])).
% 2.48/0.70  fof(f63,plain,(
% 2.48/0.70    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 2.48/0.70    inference(cnf_transformation,[],[f24])).
% 2.48/0.70  fof(f24,plain,(
% 2.48/0.70    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.48/0.70    inference(ennf_transformation,[],[f12])).
% 2.48/0.70  fof(f12,axiom,(
% 2.48/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 2.48/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 2.48/0.70  fof(f134,plain,(
% 2.48/0.70    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f128,f87])).
% 2.48/0.70  fof(f128,plain,(
% 2.48/0.70    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) | ~l1_pre_topc(sK1)),
% 2.48/0.70    inference(resolution,[],[f95,f65])).
% 2.48/0.70  fof(f95,plain,(
% 2.48/0.70    m1_pre_topc(sK1,sK1)),
% 2.48/0.70    inference(resolution,[],[f87,f59])).
% 2.48/0.70  fof(f59,plain,(
% 2.48/0.70    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 2.48/0.70    inference(cnf_transformation,[],[f21])).
% 2.48/0.70  fof(f21,plain,(
% 2.48/0.70    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.48/0.70    inference(ennf_transformation,[],[f11])).
% 2.48/0.70  fof(f11,axiom,(
% 2.48/0.70    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.48/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.48/0.70  fof(f300,plain,(
% 2.48/0.70    u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK1))),
% 2.48/0.70    inference(resolution,[],[f218,f80])).
% 2.48/0.70  fof(f80,plain,(
% 2.48/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.48/0.70    inference(cnf_transformation,[],[f50])).
% 2.48/0.70  fof(f50,plain,(
% 2.48/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.48/0.70    inference(flattening,[],[f49])).
% 2.48/0.70  fof(f49,plain,(
% 2.48/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.48/0.70    inference(nnf_transformation,[],[f1])).
% 2.48/0.70  fof(f1,axiom,(
% 2.48/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.48/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.48/0.70  fof(f218,plain,(
% 2.48/0.70    r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.48/0.70    inference(subsumption_resolution,[],[f213,f126])).
% 2.48/0.70  fof(f126,plain,(
% 2.48/0.70    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.48/0.70    inference(subsumption_resolution,[],[f121,f52])).
% 2.48/0.70  fof(f121,plain,(
% 2.48/0.70    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0)),
% 2.48/0.70    inference(resolution,[],[f98,f62])).
% 2.48/0.70  fof(f213,plain,(
% 2.48/0.70    r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.48/0.70    inference(resolution,[],[f133,f63])).
% 2.48/0.70  fof(f133,plain,(
% 2.48/0.70    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.48/0.70    inference(subsumption_resolution,[],[f132,f87])).
% 2.48/0.70  fof(f132,plain,(
% 2.48/0.70    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1)),
% 2.48/0.70    inference(duplicate_literal_removal,[],[f127])).
% 2.48/0.70  fof(f127,plain,(
% 2.48/0.70    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK1)),
% 2.48/0.70    inference(resolution,[],[f95,f60])).
% 2.48/0.70  fof(f60,plain,(
% 2.48/0.70    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.48/0.70    inference(cnf_transformation,[],[f43])).
% 2.48/0.70  fof(f43,plain,(
% 2.48/0.70    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.48/0.70    inference(nnf_transformation,[],[f22])).
% 2.48/0.70  fof(f22,plain,(
% 2.48/0.70    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.48/0.70    inference(ennf_transformation,[],[f8])).
% 2.48/0.70  fof(f8,axiom,(
% 2.48/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.48/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 2.48/0.70  fof(f115,plain,(
% 2.48/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) | k1_tex_2(X0,X1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/0.70    inference(resolution,[],[f92,f71])).
% 2.48/0.70  fof(f71,plain,(
% 2.48/0.70    ( ! [X2,X0,X1] : (~v1_pre_topc(X2) | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(X2) | ~m1_pre_topc(X2,X0) | k1_tex_2(X0,X1) = X2 | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/0.70    inference(cnf_transformation,[],[f48])).
% 2.48/0.70  fof(f92,plain,(
% 2.48/0.70    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.48/0.70    inference(subsumption_resolution,[],[f91,f52])).
% 2.48/0.70  fof(f91,plain,(
% 2.48/0.70    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0)),
% 2.48/0.70    inference(resolution,[],[f64,f55])).
% 2.48/0.70  fof(f64,plain,(
% 2.48/0.70    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 2.48/0.70    inference(cnf_transformation,[],[f25])).
% 2.48/0.70  fof(f1105,plain,(
% 2.48/0.70    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1))),
% 2.48/0.70    inference(resolution,[],[f624,f695])).
% 2.48/0.70  fof(f695,plain,(
% 2.48/0.70    ~v1_xboole_0(u1_struct_0(sK1))),
% 2.48/0.70    inference(subsumption_resolution,[],[f694,f175])).
% 2.48/0.70  fof(f694,plain,(
% 2.48/0.70    ~v1_xboole_0(u1_struct_0(sK1)) | v2_struct_0(k1_tex_2(sK1,sK2(sK1)))),
% 2.48/0.70    inference(subsumption_resolution,[],[f682,f352])).
% 2.48/0.70  fof(f352,plain,(
% 2.48/0.70    l1_struct_0(k1_tex_2(sK1,sK2(sK1)))),
% 2.48/0.70    inference(resolution,[],[f286,f58])).
% 2.48/0.70  fof(f286,plain,(
% 2.48/0.70    l1_pre_topc(k1_tex_2(sK1,sK2(sK1)))),
% 2.48/0.70    inference(subsumption_resolution,[],[f278,f87])).
% 2.48/0.70  fof(f278,plain,(
% 2.48/0.70    l1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | ~l1_pre_topc(sK1)),
% 2.48/0.70    inference(resolution,[],[f171,f62])).
% 2.48/0.70  fof(f171,plain,(
% 2.48/0.70    m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f170,f53])).
% 2.48/0.70  fof(f170,plain,(
% 2.48/0.70    m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1) | v2_struct_0(sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f165,f87])).
% 2.48/0.70  fof(f165,plain,(
% 2.48/0.70    m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.48/0.70    inference(resolution,[],[f116,f77])).
% 2.48/0.70  fof(f682,plain,(
% 2.48/0.70    ~v1_xboole_0(u1_struct_0(sK1)) | ~l1_struct_0(k1_tex_2(sK1,sK2(sK1))) | v2_struct_0(k1_tex_2(sK1,sK2(sK1)))),
% 2.48/0.70    inference(superposition,[],[f66,f201])).
% 2.48/0.70  fof(f201,plain,(
% 2.48/0.70    u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))),
% 2.48/0.70    inference(forward_demodulation,[],[f200,f104])).
% 2.48/0.70  fof(f200,plain,(
% 2.48/0.70    k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1)))),
% 2.48/0.70    inference(subsumption_resolution,[],[f199,f53])).
% 2.48/0.70  fof(f199,plain,(
% 2.48/0.70    k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | v2_struct_0(sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f198,f87])).
% 2.48/0.70  fof(f198,plain,(
% 2.48/0.70    k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f197,f116])).
% 2.48/0.70  fof(f197,plain,(
% 2.48/0.70    k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f196,f175])).
% 2.48/0.70  fof(f196,plain,(
% 2.48/0.70    k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f194,f171])).
% 2.48/0.70  fof(f194,plain,(
% 2.48/0.70    ~m1_pre_topc(k1_tex_2(sK1,sK2(sK1)),sK1) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) = u1_struct_0(k1_tex_2(sK1,sK2(sK1))) | v2_struct_0(k1_tex_2(sK1,sK2(sK1))) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.48/0.70    inference(resolution,[],[f173,f81])).
% 2.48/0.70  fof(f173,plain,(
% 2.48/0.70    v1_pre_topc(k1_tex_2(sK1,sK2(sK1)))),
% 2.48/0.70    inference(subsumption_resolution,[],[f172,f53])).
% 2.48/0.70  fof(f172,plain,(
% 2.48/0.70    v1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | v2_struct_0(sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f166,f87])).
% 2.48/0.70  fof(f166,plain,(
% 2.48/0.70    v1_pre_topc(k1_tex_2(sK1,sK2(sK1))) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.48/0.70    inference(resolution,[],[f116,f76])).
% 2.48/0.70  fof(f624,plain,(
% 2.48/0.70    v1_xboole_0(u1_struct_0(sK1)) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1))),
% 2.48/0.70    inference(forward_demodulation,[],[f623,f301])).
% 2.48/0.70  fof(f623,plain,(
% 2.48/0.70    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1)) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.48/0.70    inference(subsumption_resolution,[],[f622,f144])).
% 2.48/0.70  fof(f144,plain,(
% 2.48/0.70    l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.48/0.70    inference(resolution,[],[f126,f58])).
% 2.48/0.70  fof(f622,plain,(
% 2.48/0.70    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1)) | ~l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.48/0.70    inference(resolution,[],[f332,f73])).
% 2.48/0.70  fof(f73,plain,(
% 2.48/0.70    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 2.48/0.70    inference(cnf_transformation,[],[f35])).
% 2.48/0.70  fof(f35,plain,(
% 2.48/0.70    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 2.48/0.70    inference(flattening,[],[f34])).
% 2.48/0.70  fof(f34,plain,(
% 2.48/0.70    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 2.48/0.70    inference(ennf_transformation,[],[f5])).
% 2.48/0.70  fof(f5,axiom,(
% 2.48/0.70    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 2.48/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).
% 2.48/0.70  fof(f332,plain,(
% 2.48/0.70    v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1))),
% 2.48/0.70    inference(trivial_inequality_removal,[],[f313])).
% 2.48/0.70  fof(f313,plain,(
% 2.48/0.70    u1_struct_0(sK1) != u1_struct_0(sK1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.48/0.70    inference(backward_demodulation,[],[f193,f301])).
% 2.48/0.70  fof(f193,plain,(
% 2.48/0.70    u1_struct_0(sK1) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.48/0.70    inference(forward_demodulation,[],[f192,f104])).
% 2.48/0.70  fof(f192,plain,(
% 2.48/0.70    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.48/0.70    inference(subsumption_resolution,[],[f191,f53])).
% 2.48/0.70  fof(f191,plain,(
% 2.48/0.70    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v2_struct_0(sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f190,f87])).
% 2.48/0.70  fof(f190,plain,(
% 2.48/0.70    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f189,f134])).
% 2.48/0.70  fof(f189,plain,(
% 2.48/0.70    ~m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tex_2(sK1,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.48/0.70    inference(resolution,[],[f115,f116])).
% 2.48/0.70  fof(f1138,plain,(
% 2.48/0.70    k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK1,sK2(sK1))))),
% 2.48/0.70    inference(backward_demodulation,[],[f889,f1105])).
% 2.48/0.70  fof(f889,plain,(
% 2.48/0.70    k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.48/0.70    inference(subsumption_resolution,[],[f888,f695])).
% 2.48/0.70  fof(f888,plain,(
% 2.48/0.70    v1_xboole_0(u1_struct_0(sK1)) | k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.48/0.70    inference(forward_demodulation,[],[f887,f782])).
% 2.48/0.70  fof(f782,plain,(
% 2.48/0.70    u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.70    inference(subsumption_resolution,[],[f781,f463])).
% 2.48/0.70  fof(f463,plain,(
% 2.48/0.70    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_struct_0(sK1))),
% 2.48/0.70    inference(subsumption_resolution,[],[f460,f87])).
% 2.48/0.70  fof(f460,plain,(
% 2.48/0.70    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 2.48/0.70    inference(resolution,[],[f316,f63])).
% 2.48/0.70  fof(f316,plain,(
% 2.48/0.70    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK1)),
% 2.48/0.70    inference(backward_demodulation,[],[f224,f301])).
% 2.48/0.70  fof(f224,plain,(
% 2.48/0.70    m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f220,f87])).
% 2.48/0.70  fof(f220,plain,(
% 2.48/0.70    m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK1) | ~l1_pre_topc(sK1)),
% 2.48/0.70    inference(resolution,[],[f134,f65])).
% 2.48/0.70  fof(f781,plain,(
% 2.48/0.70    u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_struct_0(sK1))),
% 2.48/0.70    inference(resolution,[],[f456,f80])).
% 2.48/0.70  fof(f456,plain,(
% 2.48/0.70    r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.48/0.70    inference(subsumption_resolution,[],[f452,f312])).
% 2.48/0.70  fof(f312,plain,(
% 2.48/0.70    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.70    inference(backward_demodulation,[],[f187,f301])).
% 2.48/0.70  fof(f187,plain,(
% 2.48/0.70    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.70    inference(subsumption_resolution,[],[f182,f52])).
% 2.48/0.70  fof(f182,plain,(
% 2.48/0.70    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(sK0)),
% 2.48/0.70    inference(resolution,[],[f123,f62])).
% 2.48/0.70  fof(f123,plain,(
% 2.48/0.70    m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK0)),
% 2.48/0.70    inference(subsumption_resolution,[],[f118,f52])).
% 2.48/0.70  fof(f118,plain,(
% 2.48/0.70    m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK0) | ~l1_pre_topc(sK0)),
% 2.48/0.70    inference(resolution,[],[f98,f65])).
% 2.48/0.70  fof(f452,plain,(
% 2.48/0.70    r1_tarski(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.70    inference(resolution,[],[f314,f63])).
% 2.48/0.70  fof(f314,plain,(
% 2.48/0.70    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.70    inference(backward_demodulation,[],[f217,f301])).
% 2.48/0.70  fof(f217,plain,(
% 2.48/0.70    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.70    inference(subsumption_resolution,[],[f216,f87])).
% 2.48/0.70  fof(f216,plain,(
% 2.48/0.70    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(sK1)),
% 2.48/0.70    inference(subsumption_resolution,[],[f210,f126])).
% 2.48/0.70  fof(f210,plain,(
% 2.48/0.70    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1)),
% 2.48/0.70    inference(resolution,[],[f133,f60])).
% 2.48/0.70  fof(f887,plain,(
% 2.48/0.70    k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.48/0.70    inference(subsumption_resolution,[],[f886,f323])).
% 2.48/0.70  fof(f323,plain,(
% 2.48/0.70    l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.70    inference(backward_demodulation,[],[f248,f301])).
% 2.48/0.70  fof(f248,plain,(
% 2.48/0.70    l1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.70    inference(resolution,[],[f187,f58])).
% 2.48/0.71  fof(f886,plain,(
% 2.48/0.71    k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.48/0.71    inference(resolution,[],[f823,f73])).
% 2.48/0.71  fof(f823,plain,(
% 2.48/0.71    v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.48/0.71    inference(trivial_inequality_removal,[],[f794])).
% 2.48/0.71  fof(f794,plain,(
% 2.48/0.71    u1_struct_0(sK1) != u1_struct_0(sK1) | k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.71    inference(backward_demodulation,[],[f344,f782])).
% 2.48/0.71  fof(f344,plain,(
% 2.48/0.71    u1_struct_0(sK1) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | k1_tex_2(sK1,sK2(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.71    inference(forward_demodulation,[],[f343,f301])).
% 2.48/0.71  fof(f343,plain,(
% 2.48/0.71    u1_struct_0(sK1) != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1))),
% 2.48/0.71    inference(forward_demodulation,[],[f331,f301])).
% 2.48/0.71  fof(f331,plain,(
% 2.48/0.71    v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | u1_struct_0(sK1) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1))),
% 2.48/0.71    inference(backward_demodulation,[],[f295,f301])).
% 2.48/0.71  fof(f295,plain,(
% 2.48/0.71    u1_struct_0(sK1) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.71    inference(forward_demodulation,[],[f294,f104])).
% 2.48/0.71  fof(f294,plain,(
% 2.48/0.71    g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.71    inference(subsumption_resolution,[],[f293,f53])).
% 2.48/0.71  fof(f293,plain,(
% 2.48/0.71    g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | v2_struct_0(sK1)),
% 2.48/0.71    inference(subsumption_resolution,[],[f292,f87])).
% 2.48/0.71  fof(f292,plain,(
% 2.48/0.71    g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.48/0.71    inference(subsumption_resolution,[],[f291,f224])).
% 2.48/0.71  fof(f291,plain,(
% 2.48/0.71    ~m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK1) | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = k1_tex_2(sK1,sK2(sK1)) | v2_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | k6_domain_1(u1_struct_0(sK1),sK2(sK1)) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.48/0.71    inference(resolution,[],[f177,f116])).
% 2.48/0.71  fof(f177,plain,(
% 2.48/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),X0) | k1_tex_2(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v2_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | k6_domain_1(u1_struct_0(X0),X1) != u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/0.71    inference(resolution,[],[f124,f71])).
% 2.48/0.71  fof(f124,plain,(
% 2.48/0.71    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.48/0.71    inference(subsumption_resolution,[],[f119,f52])).
% 2.48/0.71  fof(f119,plain,(
% 2.48/0.71    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(sK0)),
% 2.48/0.71    inference(resolution,[],[f98,f64])).
% 2.48/0.71  fof(f1515,plain,(
% 2.48/0.71    k1_tex_2(sK0,sK2(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK2(sK1))))),
% 2.48/0.71    inference(backward_demodulation,[],[f1474,f1483])).
% 2.48/0.71  fof(f1474,plain,(
% 2.48/0.71    k1_tex_2(sK1,sK2(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK2(sK1))))),
% 2.48/0.71    inference(backward_demodulation,[],[f1124,f1465])).
% 2.48/0.71  fof(f1124,plain,(
% 2.48/0.71    k1_tex_2(sK1,sK2(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK2(sK1))),u1_pre_topc(k1_tex_2(sK0,sK2(sK1))))),
% 2.48/0.71    inference(backward_demodulation,[],[f508,f1105])).
% 2.48/0.71  fof(f508,plain,(
% 2.48/0.71    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK2(sK1))),u1_pre_topc(k1_tex_2(sK0,sK2(sK1))))),
% 2.48/0.71    inference(resolution,[],[f472,f56])).
% 2.48/0.71  fof(f56,plain,(
% 2.48/0.71    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2))) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )),
% 2.48/0.71    inference(cnf_transformation,[],[f42])).
% 2.48/0.71  % SZS output end Proof for theBenchmark
% 2.48/0.71  % (15412)------------------------------
% 2.48/0.71  % (15412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.48/0.71  % (15412)Termination reason: Refutation
% 2.48/0.71  
% 2.48/0.71  % (15412)Memory used [KB]: 2302
% 2.48/0.71  % (15412)Time elapsed: 0.236 s
% 2.48/0.71  % (15412)------------------------------
% 2.48/0.71  % (15412)------------------------------
% 2.48/0.71  % (15404)Success in time 0.34 s
%------------------------------------------------------------------------------

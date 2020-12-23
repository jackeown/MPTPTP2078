%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 501 expanded)
%              Number of leaves         :   16 ( 163 expanded)
%              Depth                    :   55
%              Number of atoms          :  737 (4752 expanded)
%              Number of equality atoms :   83 ( 519 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f41,f42,f44,f47,f45,f46,f49,f48,f228,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( ( v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v3_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_6)).

fof(f228,plain,(
    ~ v3_yellow_6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f227,f41])).

fof(f227,plain,
    ( ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f226,f42])).

fof(f226,plain,
    ( ~ v3_yellow_6(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f225,f43])).

fof(f43,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & v1_yellow_6(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
            & l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k11_yellow_6(sK0,X1) != k4_yellow_6(sK0,X1)
          & l1_waybel_0(X1,sK0)
          & v1_yellow_6(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( k11_yellow_6(sK0,X1) != k4_yellow_6(sK0,X1)
        & l1_waybel_0(X1,sK0)
        & v1_yellow_6(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1)
      & l1_waybel_0(sK1,sK0)
      & v1_yellow_6(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_6)).

fof(f225,plain,
    ( ~ v3_yellow_6(sK1,sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f224,f44])).

fof(f224,plain,
    ( ~ v3_yellow_6(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f223,f45])).

fof(f223,plain,
    ( ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f222,f46])).

fof(f222,plain,
    ( ~ v3_yellow_6(sK1,sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f221,f47])).

fof(f221,plain,
    ( ~ v3_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f220,f49])).

fof(f220,plain,
    ( ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,
    ( ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f218,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v3_yellow_6(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_yellow_6)).

fof(f218,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_yellow_6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f217,f41])).

fof(f217,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f216,f42])).

fof(f216,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f215,f43])).

fof(f215,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f214,f44])).

fof(f214,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f213,f45])).

fof(f213,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f212,f46])).

fof(f212,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f211,f47])).

fof(f211,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f210,f49])).

fof(f210,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f205,f50])).

fof(f50,plain,(
    k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f205,plain,
    ( k11_yellow_6(sK0,sK1) = k4_yellow_6(sK0,sK1)
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f178,f78])).

% (17649)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(k11_yellow_6(X0,X1),k10_yellow_6(X0,X1))
      | ~ m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | k11_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k11_yellow_6(X0,X1) = X2
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
                & ( r2_hidden(X2,k10_yellow_6(X0,X1))
                  | k11_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

% (17648)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_yellow_6)).

fof(f178,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | k4_yellow_6(sK0,sK1) = X1 ) ),
    inference(superposition,[],[f81,f174])).

fof(f174,plain,(
    k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f173,f41])).

fof(f173,plain,
    ( k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f172,f42])).

fof(f172,plain,
    ( k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f171,f44])).

fof(f171,plain,
    ( k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f170,f45])).

fof(f170,plain,
    ( k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f46])).

fof(f169,plain,
    ( k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f168,f47])).

fof(f168,plain,
    ( k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1))
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f167,f48])).

fof(f167,plain,
    ( k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1))
    | ~ v1_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f156,f49])).

fof(f156,plain,
    ( k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f148,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_6)).

fof(f148,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f147,f41])).

fof(f147,plain,(
    ! [X3] :
      ( k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1)
      | ~ r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f146,f42])).

fof(f146,plain,(
    ! [X3] :
      ( k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1)
      | ~ r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f44])).

fof(f145,plain,(
    ! [X3] :
      ( k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1)
      | ~ r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f144,f45])).

fof(f144,plain,(
    ! [X3] :
      ( k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1)
      | ~ r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f46])).

fof(f143,plain,(
    ! [X3] :
      ( k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1)
      | ~ r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f47])).

fof(f142,plain,(
    ! [X3] :
      ( k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1)
      | ~ r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f141,f48])).

fof(f141,plain,(
    ! [X3] :
      ( k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1)
      | ~ r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ v1_yellow_6(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f130,f49])).

fof(f130,plain,(
    ! [X3] :
      ( k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1)
      | ~ r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v1_yellow_6(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f122,f60])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | k2_tarski(X0,X0) = k10_yellow_6(sK0,sK1)
      | ~ r2_hidden(X0,k10_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f121,f71])).

fof(f71,plain,(
    ! [X0] : ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f121,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = k10_yellow_6(sK0,sK1)
      | v1_xboole_0(k2_tarski(X0,X0))
      | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | ~ r2_hidden(X0,k10_yellow_6(sK0,sK1)) ) ),
    inference(resolution,[],[f120,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK1))
      | k10_yellow_6(sK0,sK1) = X0
      | v1_xboole_0(X0)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f119,f49])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK1))
      | k10_yellow_6(sK0,sK1) = X0
      | ~ l1_waybel_0(sK1,sK0)
      | v1_xboole_0(X0)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f118,f46])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK1)
      | ~ r1_tarski(X0,k10_yellow_6(sK0,sK1))
      | k10_yellow_6(sK0,sK1) = X0
      | ~ l1_waybel_0(sK1,sK0)
      | v1_xboole_0(X0)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f117,f45])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | ~ r1_tarski(X0,k10_yellow_6(sK0,sK1))
      | k10_yellow_6(sK0,sK1) = X0
      | ~ l1_waybel_0(sK1,sK0)
      | v1_xboole_0(X0)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) ) ),
    inference(resolution,[],[f116,f47])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ r1_tarski(X1,k10_yellow_6(sK0,X0))
      | k10_yellow_6(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | v1_xboole_0(X1)
      | ~ r2_hidden(X2,k10_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f115,f41])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v7_waybel_0(X0)
      | v2_struct_0(sK0)
      | ~ r1_tarski(X1,k10_yellow_6(sK0,X0))
      | k10_yellow_6(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | v1_xboole_0(X1)
      | ~ r2_hidden(X2,k10_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f114,f42])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v7_waybel_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r1_tarski(X1,k10_yellow_6(sK0,X0))
      | k10_yellow_6(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | v1_xboole_0(X1)
      | ~ r2_hidden(X2,k10_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f113,f44])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v7_waybel_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r1_tarski(X1,k10_yellow_6(sK0,X0))
      | k10_yellow_6(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | v1_xboole_0(X1)
      | ~ r2_hidden(X2,k10_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f97,f43])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v8_pre_topc(X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v7_waybel_0(X0)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r1_tarski(X2,k10_yellow_6(X1,X0))
      | k10_yellow_6(X1,X0) = X2
      | ~ l1_waybel_0(X0,X1)
      | v1_xboole_0(X2)
      | ~ r2_hidden(X3,k10_yellow_6(X1,X0)) ) ),
    inference(resolution,[],[f89,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k10_yellow_6(X1,X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r1_tarski(X2,k10_yellow_6(X1,X0))
      | k10_yellow_6(X1,X0) = X2
      | ~ l1_waybel_0(X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f64,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => v1_zfmisc_1(k10_yellow_6(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_yellow_6)).

fof(f81,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f65,f52])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f48,plain,(
    v1_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:25:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (17660)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (17652)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (17646)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (17660)Refutation not found, incomplete strategy% (17660)------------------------------
% 0.22/0.52  % (17660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17660)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17660)Memory used [KB]: 1791
% 0.22/0.52  % (17660)Time elapsed: 0.093 s
% 0.22/0.52  % (17660)------------------------------
% 0.22/0.52  % (17660)------------------------------
% 0.22/0.52  % (17651)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (17669)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (17668)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (17667)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (17661)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (17659)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (17668)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f41,f42,f44,f47,f45,f46,f49,f48,f228,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | (~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_waybel_0(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => ((v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_6)).
% 0.22/0.54  fof(f228,plain,(
% 0.22/0.54    ~v3_yellow_6(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f227,f41])).
% 0.22/0.54  fof(f227,plain,(
% 0.22/0.54    ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f226,f42])).
% 0.22/0.54  fof(f226,plain,(
% 0.22/0.54    ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f225,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    v8_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    (k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1) & l1_waybel_0(sK1,sK0) & v1_yellow_6(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f29,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (k11_yellow_6(sK0,X1) != k4_yellow_6(sK0,X1) & l1_waybel_0(X1,sK0) & v1_yellow_6(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ? [X1] : (k11_yellow_6(sK0,X1) != k4_yellow_6(sK0,X1) & l1_waybel_0(X1,sK0) & v1_yellow_6(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1) & l1_waybel_0(sK1,sK0) & v1_yellow_6(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & (l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f12])).
% 0.22/0.54  fof(f12,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_6)).
% 0.22/0.54  fof(f225,plain,(
% 0.22/0.54    ~v3_yellow_6(sK1,sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f224,f44])).
% 0.22/0.54  fof(f224,plain,(
% 0.22/0.54    ~v3_yellow_6(sK1,sK0) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f223,f45])).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f222,f46])).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    ~v3_yellow_6(sK1,sK0) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f221,f47])).
% 0.22/0.54  fof(f221,plain,(
% 0.22/0.54    ~v3_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f220,f49])).
% 0.22/0.54  fof(f220,plain,(
% 0.22/0.54    ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f219])).
% 0.22/0.54  fof(f219,plain,(
% 0.22/0.54    ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v3_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f218,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_yellow_6)).
% 0.22/0.54  fof(f218,plain,(
% 0.22/0.54    ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v3_yellow_6(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f217,f41])).
% 0.22/0.54  fof(f217,plain,(
% 0.22/0.54    ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f216,f42])).
% 0.22/0.54  fof(f216,plain,(
% 0.22/0.54    ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f215,f43])).
% 0.22/0.54  fof(f215,plain,(
% 0.22/0.54    ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v3_yellow_6(sK1,sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f214,f44])).
% 0.22/0.54  fof(f214,plain,(
% 0.22/0.54    ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v3_yellow_6(sK1,sK0) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f213,f45])).
% 0.22/0.54  fof(f213,plain,(
% 0.22/0.54    ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f212,f46])).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v3_yellow_6(sK1,sK0) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f211,f47])).
% 0.22/0.54  fof(f211,plain,(
% 0.22/0.54    ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v3_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f210,f49])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v3_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f205,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    k11_yellow_6(sK0,sK1) = k4_yellow_6(sK0,sK1) | ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v3_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f178,f78])).
% 0.22/0.54  % (17649)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(k11_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | k11_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((k11_yellow_6(X0,X1) = X2 | ~r2_hidden(X2,k10_yellow_6(X0,X1))) & (r2_hidden(X2,k10_yellow_6(X0,X1)) | k11_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  % (17648)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_yellow_6)).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    ( ! [X1] : (~r2_hidden(X1,k10_yellow_6(sK0,sK1)) | k4_yellow_6(sK0,sK1) = X1) )),
% 0.22/0.54    inference(superposition,[],[f81,f174])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1))),
% 0.22/0.54    inference(subsumption_resolution,[],[f173,f41])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f172,f42])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f171,f44])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f170,f45])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f169,f46])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f168,f47])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f167,f48])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1)) | ~v1_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f156,f49])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    k10_yellow_6(sK0,sK1) = k2_tarski(k4_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v1_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f148,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_6)).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    ( ! [X3] : (~r2_hidden(X3,k10_yellow_6(sK0,sK1)) | k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f147,f41])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ( ! [X3] : (k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1) | ~r2_hidden(X3,k10_yellow_6(sK0,sK1)) | v2_struct_0(sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f146,f42])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    ( ! [X3] : (k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1) | ~r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f145,f44])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    ( ! [X3] : (k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1) | ~r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f144,f45])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ( ! [X3] : (k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1) | ~r2_hidden(X3,k10_yellow_6(sK0,sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f143,f46])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X3] : (k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1) | ~r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f142,f47])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    ( ! [X3] : (k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1) | ~r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f141,f48])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    ( ! [X3] : (k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1) | ~r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~v1_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f130,f49])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    ( ! [X3] : (k2_tarski(X3,X3) = k10_yellow_6(sK0,sK1) | ~r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v1_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.54    inference(resolution,[],[f122,f60])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k10_yellow_6(sK0,sK1)) | k2_tarski(X0,X0) = k10_yellow_6(sK0,sK1) | ~r2_hidden(X0,k10_yellow_6(sK0,sK1))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f121,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(k2_tarski(X0,X0))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f51,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X0) = k10_yellow_6(sK0,sK1) | v1_xboole_0(k2_tarski(X0,X0)) | ~r2_hidden(X1,k10_yellow_6(sK0,sK1)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK1))) )),
% 0.22/0.54    inference(resolution,[],[f120,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f70,f52])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k10_yellow_6(sK0,sK1)) | k10_yellow_6(sK0,sK1) = X0 | v1_xboole_0(X0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK1))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f119,f49])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k10_yellow_6(sK0,sK1)) | k10_yellow_6(sK0,sK1) = X0 | ~l1_waybel_0(sK1,sK0) | v1_xboole_0(X0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK1))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f118,f46])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v4_orders_2(sK1) | ~r1_tarski(X0,k10_yellow_6(sK0,sK1)) | k10_yellow_6(sK0,sK1) = X0 | ~l1_waybel_0(sK1,sK0) | v1_xboole_0(X0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK1))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f117,f45])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~r1_tarski(X0,k10_yellow_6(sK0,sK1)) | k10_yellow_6(sK0,sK1) = X0 | ~l1_waybel_0(sK1,sK0) | v1_xboole_0(X0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK1))) )),
% 0.22/0.54    inference(resolution,[],[f116,f47])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v7_waybel_0(X0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~r1_tarski(X1,k10_yellow_6(sK0,X0)) | k10_yellow_6(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | v1_xboole_0(X1) | ~r2_hidden(X2,k10_yellow_6(sK0,X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f115,f41])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v4_orders_2(X0) | v2_struct_0(X0) | ~v7_waybel_0(X0) | v2_struct_0(sK0) | ~r1_tarski(X1,k10_yellow_6(sK0,X0)) | k10_yellow_6(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | v1_xboole_0(X1) | ~r2_hidden(X2,k10_yellow_6(sK0,X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f114,f42])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v4_orders_2(X0) | v2_struct_0(X0) | ~v7_waybel_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(X1,k10_yellow_6(sK0,X0)) | k10_yellow_6(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | v1_xboole_0(X1) | ~r2_hidden(X2,k10_yellow_6(sK0,X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f113,f44])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v7_waybel_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(X1,k10_yellow_6(sK0,X0)) | k10_yellow_6(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | v1_xboole_0(X1) | ~r2_hidden(X2,k10_yellow_6(sK0,X0))) )),
% 0.22/0.54    inference(resolution,[],[f97,f43])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v8_pre_topc(X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v7_waybel_0(X0) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tarski(X2,k10_yellow_6(X1,X0)) | k10_yellow_6(X1,X0) = X2 | ~l1_waybel_0(X0,X1) | v1_xboole_0(X2) | ~r2_hidden(X3,k10_yellow_6(X1,X0))) )),
% 0.22/0.54    inference(resolution,[],[f89,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(rectify,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_xboole_0(k10_yellow_6(X1,X0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tarski(X2,k10_yellow_6(X1,X0)) | k10_yellow_6(X1,X0) = X2 | ~l1_waybel_0(X0,X1) | v1_xboole_0(X2)) )),
% 0.22/0.54    inference(resolution,[],[f64,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_zfmisc_1(k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : (v1_zfmisc_1(k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : (v1_zfmisc_1(k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => v1_zfmisc_1(k10_yellow_6(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_yellow_6)).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 0.22/0.54    inference(equality_resolution,[],[f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f65,f52])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(rectify,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    v1_yellow_6(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    l1_waybel_0(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    v4_orders_2(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ~v2_struct_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    v7_waybel_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ~v2_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (17668)------------------------------
% 0.22/0.54  % (17668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17668)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (17668)Memory used [KB]: 6396
% 0.22/0.54  % (17668)Time elapsed: 0.121 s
% 0.22/0.54  % (17668)------------------------------
% 0.22/0.54  % (17668)------------------------------
% 0.22/0.54  % (17650)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (17645)Success in time 0.175 s
%------------------------------------------------------------------------------

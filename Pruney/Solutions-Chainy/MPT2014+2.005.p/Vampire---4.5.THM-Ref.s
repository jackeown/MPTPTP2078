%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 198 expanded)
%              Number of leaves         :   18 (  60 expanded)
%              Depth                    :   20
%              Number of atoms          :  392 ( 910 expanded)
%              Number of equality atoms :   12 (  40 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f102,f107,f118,f130,f136,f141,f146,f226])).

fof(f226,plain,
    ( spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_7
    | spl7_9
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_7
    | spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f224,f117])).

% (4722)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f117,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl7_7
  <=> r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f224,plain,
    ( r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_11 ),
    inference(resolution,[],[f212,f140])).

fof(f140,plain,
    ( r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl7_11
  <=> r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f212,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(X3,u1_struct_0(sK1)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | r1_tarski(X3,u1_struct_0(sK1)) )
    | spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(resolution,[],[f203,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

% (4720)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f203,plain,
    ( ! [X3] :
        ( r2_hidden(X3,u1_struct_0(sK1))
        | ~ r2_hidden(X3,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) )
    | spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(resolution,[],[f195,f153])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(X0,u1_struct_0(sK1)) )
    | spl7_9 ),
    inference(resolution,[],[f129,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f129,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_9
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f195,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) )
    | spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f193,f175])).

fof(f175,plain,
    ( ! [X3] :
        ( sP4(X3,sK2,sK1)
        | ~ r2_hidden(X3,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) )
    | spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f166,f106])).

fof(f106,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_5
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | sP4(X1,X0,sK1)
        | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(sK0,sK1,X0))) )
    | spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f164,f101])).

fof(f101,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl7_4
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | sP4(X1,X0,sK1)
        | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(sK0,sK1,X0))) )
    | spl7_1
    | spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f93,f56])).

fof(f56,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl7_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f93,plain,
    ( ! [X8,X7,X9] :
        ( v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK0)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | sP4(X9,X8,X7)
        | ~ r2_hidden(X9,u1_struct_0(k4_waybel_9(sK0,X7,X8))) )
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f92,f87])).

fof(f87,plain,
    ( ! [X2,X3] :
        ( l1_waybel_0(k4_waybel_9(sK0,X2,X3),sK0)
        | ~ l1_waybel_0(X2,sK0)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | v2_struct_0(X2) )
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f81,f66])).

fof(f66,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl7_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f81,plain,
    ( ! [X2,X3] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | l1_waybel_0(k4_waybel_9(sK0,X2,X3),sK0) )
    | spl7_2 ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(f61,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f92,plain,
    ( ! [X8,X7,X9] :
        ( v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK0)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ l1_waybel_0(k4_waybel_9(sK0,X7,X8),sK0)
        | sP4(X9,X8,X7)
        | ~ r2_hidden(X9,u1_struct_0(k4_waybel_9(sK0,X7,X8))) )
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f91,f86])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( v6_waybel_0(k4_waybel_9(sK0,X0,X1),sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f80,f66])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v6_waybel_0(k4_waybel_9(sK0,X0,X1),sK0) )
    | spl7_2 ),
    inference(resolution,[],[f61,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,
    ( ! [X8,X7,X9] :
        ( v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK0)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v6_waybel_0(k4_waybel_9(sK0,X7,X8),sK0)
        | ~ l1_waybel_0(k4_waybel_9(sK0,X7,X8),sK0)
        | sP4(X9,X8,X7)
        | ~ r2_hidden(X9,u1_struct_0(k4_waybel_9(sK0,X7,X8))) )
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f83,f66])).

fof(f83,plain,
    ( ! [X8,X7,X9] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK0)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v6_waybel_0(k4_waybel_9(sK0,X7,X8),sK0)
        | ~ l1_waybel_0(k4_waybel_9(sK0,X7,X8),sK0)
        | sP4(X9,X8,X7)
        | ~ r2_hidden(X9,u1_struct_0(k4_waybel_9(sK0,X7,X8))) )
    | spl7_2 ),
    inference(resolution,[],[f61,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | sP4(X4,X2,X1)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | sP4(X4,X2,X1)
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

fof(f193,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK1))
        | ~ sP4(X0,sK2,sK1)
        | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) )
    | spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(superposition,[],[f33,f180])).

fof(f180,plain,
    ( ! [X3] :
        ( sK5(sK1,sK2,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) )
    | spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f175,f34])).

fof(f34,plain,(
    ! [X4,X2,X1] :
      ( ~ sP4(X4,X2,X1)
      | sK5(X1,X2,X4) = X4 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X4,X2,X1] :
      ( m1_subset_1(sK5(X1,X2,X4),u1_struct_0(X1))
      | ~ sP4(X4,X2,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f146,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f144,f66])).

fof(f144,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl7_4
    | spl7_10 ),
    inference(resolution,[],[f142,f101])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK1,X0)
        | ~ l1_struct_0(X0) )
    | spl7_10 ),
    inference(resolution,[],[f135,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f135,plain,
    ( ~ l1_orders_2(sK1)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_10
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f141,plain,
    ( spl7_11
    | spl7_7 ),
    inference(avatar_split_clause,[],[f121,f115,f138])).

fof(f121,plain,
    ( r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | spl7_7 ),
    inference(resolution,[],[f117,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f136,plain,
    ( ~ spl7_10
    | spl7_8 ),
    inference(avatar_split_clause,[],[f131,f123,f133])).

fof(f123,plain,
    ( spl7_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f131,plain,
    ( ~ l1_orders_2(sK1)
    | spl7_8 ),
    inference(resolution,[],[f125,f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f125,plain,
    ( ~ l1_struct_0(sK1)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f130,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | spl7_1 ),
    inference(avatar_split_clause,[],[f73,f54,f127,f123])).

fof(f73,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | spl7_1 ),
    inference(resolution,[],[f56,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_struct_0)).

fof(f118,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f23,f115])).

fof(f23,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

fof(f107,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f22,f104])).

fof(f22,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f102,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f25,f99])).

fof(f25,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:46:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (4729)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (4739)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (4731)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (4739)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 1.21/0.54  % (4735)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.21/0.54  % (4743)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.21/0.55  % (4719)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.55  % (4719)Refutation not found, incomplete strategy% (4719)------------------------------
% 1.21/0.55  % (4719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.55  % (4719)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.55  
% 1.21/0.55  % (4719)Memory used [KB]: 1663
% 1.21/0.55  % (4719)Time elapsed: 0.136 s
% 1.21/0.55  % (4719)------------------------------
% 1.21/0.55  % (4719)------------------------------
% 1.21/0.55  % SZS output start Proof for theBenchmark
% 1.21/0.55  fof(f227,plain,(
% 1.21/0.55    $false),
% 1.21/0.55    inference(avatar_sat_refutation,[],[f57,f62,f67,f102,f107,f118,f130,f136,f141,f146,f226])).
% 1.21/0.55  fof(f226,plain,(
% 1.21/0.55    spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_7 | spl7_9 | ~spl7_11),
% 1.21/0.55    inference(avatar_contradiction_clause,[],[f225])).
% 1.21/0.55  fof(f225,plain,(
% 1.21/0.55    $false | (spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_7 | spl7_9 | ~spl7_11)),
% 1.21/0.55    inference(subsumption_resolution,[],[f224,f117])).
% 1.21/0.55  % (4722)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.55  fof(f117,plain,(
% 1.21/0.55    ~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) | spl7_7),
% 1.21/0.55    inference(avatar_component_clause,[],[f115])).
% 1.21/0.55  fof(f115,plain,(
% 1.21/0.55    spl7_7 <=> r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 1.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.21/0.55  fof(f224,plain,(
% 1.21/0.55    r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) | (spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_9 | ~spl7_11)),
% 1.21/0.55    inference(resolution,[],[f212,f140])).
% 1.21/0.55  fof(f140,plain,(
% 1.21/0.55    r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | ~spl7_11),
% 1.21/0.55    inference(avatar_component_clause,[],[f138])).
% 1.21/0.55  fof(f138,plain,(
% 1.21/0.55    spl7_11 <=> r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))),
% 1.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.21/0.55  fof(f212,plain,(
% 1.21/0.55    ( ! [X3] : (~r2_hidden(sK6(X3,u1_struct_0(sK1)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | r1_tarski(X3,u1_struct_0(sK1))) ) | (spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_9)),
% 1.21/0.55    inference(resolution,[],[f203,f45])).
% 1.21/0.55  fof(f45,plain,(
% 1.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.21/0.55    inference(cnf_transformation,[],[f19])).
% 1.21/0.55  % (4720)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.21/0.55  fof(f19,plain,(
% 1.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.21/0.55    inference(ennf_transformation,[],[f1])).
% 1.21/0.55  fof(f1,axiom,(
% 1.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.21/0.55  fof(f203,plain,(
% 1.21/0.55    ( ! [X3] : (r2_hidden(X3,u1_struct_0(sK1)) | ~r2_hidden(X3,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) ) | (spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_9)),
% 1.21/0.55    inference(resolution,[],[f195,f153])).
% 1.21/0.55  fof(f153,plain,(
% 1.21/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r2_hidden(X0,u1_struct_0(sK1))) ) | spl7_9),
% 1.21/0.55    inference(resolution,[],[f129,f42])).
% 1.21/0.55  fof(f42,plain,(
% 1.21/0.55    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 1.21/0.55    inference(cnf_transformation,[],[f18])).
% 1.21/0.55  fof(f18,plain,(
% 1.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.21/0.55    inference(flattening,[],[f17])).
% 1.21/0.55  fof(f17,plain,(
% 1.21/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.21/0.55    inference(ennf_transformation,[],[f2])).
% 1.21/0.55  fof(f2,axiom,(
% 1.21/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.21/0.55  fof(f129,plain,(
% 1.21/0.55    ~v1_xboole_0(u1_struct_0(sK1)) | spl7_9),
% 1.21/0.55    inference(avatar_component_clause,[],[f127])).
% 1.21/0.55  fof(f127,plain,(
% 1.21/0.55    spl7_9 <=> v1_xboole_0(u1_struct_0(sK1))),
% 1.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.21/0.55  fof(f195,plain,(
% 1.21/0.55    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) ) | (spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 1.21/0.55    inference(subsumption_resolution,[],[f193,f175])).
% 1.21/0.55  fof(f175,plain,(
% 1.21/0.55    ( ! [X3] : (sP4(X3,sK2,sK1) | ~r2_hidden(X3,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) ) | (spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 1.21/0.55    inference(resolution,[],[f166,f106])).
% 1.21/0.55  fof(f106,plain,(
% 1.21/0.55    m1_subset_1(sK2,u1_struct_0(sK1)) | ~spl7_5),
% 1.21/0.55    inference(avatar_component_clause,[],[f104])).
% 1.21/0.55  fof(f104,plain,(
% 1.21/0.55    spl7_5 <=> m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.21/0.55  fof(f166,plain,(
% 1.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | sP4(X1,X0,sK1) | ~r2_hidden(X1,u1_struct_0(k4_waybel_9(sK0,sK1,X0)))) ) | (spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4)),
% 1.21/0.55    inference(subsumption_resolution,[],[f164,f101])).
% 1.21/0.55  fof(f101,plain,(
% 1.21/0.55    l1_waybel_0(sK1,sK0) | ~spl7_4),
% 1.21/0.55    inference(avatar_component_clause,[],[f99])).
% 1.21/0.55  fof(f99,plain,(
% 1.21/0.55    spl7_4 <=> l1_waybel_0(sK1,sK0)),
% 1.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.21/0.55  fof(f164,plain,(
% 1.21/0.55    ( ! [X0,X1] : (~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | sP4(X1,X0,sK1) | ~r2_hidden(X1,u1_struct_0(k4_waybel_9(sK0,sK1,X0)))) ) | (spl7_1 | spl7_2 | ~spl7_3)),
% 1.21/0.55    inference(resolution,[],[f93,f56])).
% 1.21/0.56  fof(f56,plain,(
% 1.21/0.56    ~v2_struct_0(sK1) | spl7_1),
% 1.21/0.56    inference(avatar_component_clause,[],[f54])).
% 1.21/0.56  fof(f54,plain,(
% 1.21/0.56    spl7_1 <=> v2_struct_0(sK1)),
% 1.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.21/0.56  fof(f93,plain,(
% 1.21/0.56    ( ! [X8,X7,X9] : (v2_struct_0(X7) | ~l1_waybel_0(X7,sK0) | ~m1_subset_1(X8,u1_struct_0(X7)) | sP4(X9,X8,X7) | ~r2_hidden(X9,u1_struct_0(k4_waybel_9(sK0,X7,X8)))) ) | (spl7_2 | ~spl7_3)),
% 1.21/0.56    inference(subsumption_resolution,[],[f92,f87])).
% 1.21/0.56  fof(f87,plain,(
% 1.21/0.56    ( ! [X2,X3] : (l1_waybel_0(k4_waybel_9(sK0,X2,X3),sK0) | ~l1_waybel_0(X2,sK0) | ~m1_subset_1(X3,u1_struct_0(X2)) | v2_struct_0(X2)) ) | (spl7_2 | ~spl7_3)),
% 1.21/0.56    inference(subsumption_resolution,[],[f81,f66])).
% 1.21/0.56  fof(f66,plain,(
% 1.21/0.56    l1_struct_0(sK0) | ~spl7_3),
% 1.21/0.56    inference(avatar_component_clause,[],[f64])).
% 1.21/0.56  fof(f64,plain,(
% 1.21/0.56    spl7_3 <=> l1_struct_0(sK0)),
% 1.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.21/0.56  fof(f81,plain,(
% 1.21/0.56    ( ! [X2,X3] : (~l1_struct_0(sK0) | v2_struct_0(X2) | ~l1_waybel_0(X2,sK0) | ~m1_subset_1(X3,u1_struct_0(X2)) | l1_waybel_0(k4_waybel_9(sK0,X2,X3),sK0)) ) | spl7_2),
% 1.21/0.56    inference(resolution,[],[f61,f47])).
% 1.21/0.56  fof(f47,plain,(
% 1.21/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f21])).
% 1.21/0.56  fof(f21,plain,(
% 1.21/0.56    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.21/0.56    inference(flattening,[],[f20])).
% 1.21/0.56  fof(f20,plain,(
% 1.21/0.56    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.21/0.56    inference(ennf_transformation,[],[f7])).
% 1.21/0.56  fof(f7,axiom,(
% 1.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).
% 1.21/0.56  fof(f61,plain,(
% 1.21/0.56    ~v2_struct_0(sK0) | spl7_2),
% 1.21/0.56    inference(avatar_component_clause,[],[f59])).
% 1.21/0.56  fof(f59,plain,(
% 1.21/0.56    spl7_2 <=> v2_struct_0(sK0)),
% 1.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.21/0.56  fof(f92,plain,(
% 1.21/0.56    ( ! [X8,X7,X9] : (v2_struct_0(X7) | ~l1_waybel_0(X7,sK0) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~l1_waybel_0(k4_waybel_9(sK0,X7,X8),sK0) | sP4(X9,X8,X7) | ~r2_hidden(X9,u1_struct_0(k4_waybel_9(sK0,X7,X8)))) ) | (spl7_2 | ~spl7_3)),
% 1.21/0.56    inference(subsumption_resolution,[],[f91,f86])).
% 1.21/0.56  fof(f86,plain,(
% 1.21/0.56    ( ! [X0,X1] : (v6_waybel_0(k4_waybel_9(sK0,X0,X1),sK0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | (spl7_2 | ~spl7_3)),
% 1.21/0.56    inference(subsumption_resolution,[],[f80,f66])).
% 1.21/0.56  fof(f80,plain,(
% 1.21/0.56    ( ! [X0,X1] : (~l1_struct_0(sK0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v6_waybel_0(k4_waybel_9(sK0,X0,X1),sK0)) ) | spl7_2),
% 1.21/0.56    inference(resolution,[],[f61,f46])).
% 1.21/0.56  fof(f46,plain,(
% 1.21/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f21])).
% 1.21/0.56  fof(f91,plain,(
% 1.21/0.56    ( ! [X8,X7,X9] : (v2_struct_0(X7) | ~l1_waybel_0(X7,sK0) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~v6_waybel_0(k4_waybel_9(sK0,X7,X8),sK0) | ~l1_waybel_0(k4_waybel_9(sK0,X7,X8),sK0) | sP4(X9,X8,X7) | ~r2_hidden(X9,u1_struct_0(k4_waybel_9(sK0,X7,X8)))) ) | (spl7_2 | ~spl7_3)),
% 1.21/0.56    inference(subsumption_resolution,[],[f83,f66])).
% 1.21/0.56  fof(f83,plain,(
% 1.21/0.56    ( ! [X8,X7,X9] : (~l1_struct_0(sK0) | v2_struct_0(X7) | ~l1_waybel_0(X7,sK0) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~v6_waybel_0(k4_waybel_9(sK0,X7,X8),sK0) | ~l1_waybel_0(k4_waybel_9(sK0,X7,X8),sK0) | sP4(X9,X8,X7) | ~r2_hidden(X9,u1_struct_0(k4_waybel_9(sK0,X7,X8)))) ) | spl7_2),
% 1.21/0.56    inference(resolution,[],[f61,f50])).
% 1.21/0.56  fof(f50,plain,(
% 1.21/0.56    ( ! [X4,X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | sP4(X4,X2,X1) | ~r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))) )),
% 1.21/0.56    inference(equality_resolution,[],[f39])).
% 1.21/0.56  fof(f39,plain,(
% 1.21/0.56    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(X3,X0) | ~l1_waybel_0(X3,X0) | sP4(X4,X2,X1) | ~r2_hidden(X4,u1_struct_0(X3)) | k4_waybel_9(X0,X1,X2) != X3) )),
% 1.21/0.56    inference(cnf_transformation,[],[f16])).
% 1.21/0.56  fof(f16,plain,(
% 1.21/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.21/0.56    inference(flattening,[],[f15])).
% 1.21/0.56  fof(f15,plain,(
% 1.21/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | (~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0))) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.21/0.56    inference(ennf_transformation,[],[f6])).
% 1.21/0.56  fof(f6,axiom,(
% 1.21/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : ((l1_waybel_0(X3,X0) & v6_waybel_0(X3,X0)) => (k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))))))))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).
% 1.21/0.56  fof(f193,plain,(
% 1.21/0.56    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK1)) | ~sP4(X0,sK2,sK1) | ~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) ) | (spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 1.21/0.56    inference(superposition,[],[f33,f180])).
% 1.21/0.56  fof(f180,plain,(
% 1.21/0.56    ( ! [X3] : (sK5(sK1,sK2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) ) | (spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 1.21/0.56    inference(resolution,[],[f175,f34])).
% 1.21/0.56  fof(f34,plain,(
% 1.21/0.56    ( ! [X4,X2,X1] : (~sP4(X4,X2,X1) | sK5(X1,X2,X4) = X4) )),
% 1.21/0.56    inference(cnf_transformation,[],[f16])).
% 1.21/0.56  fof(f33,plain,(
% 1.21/0.56    ( ! [X4,X2,X1] : (m1_subset_1(sK5(X1,X2,X4),u1_struct_0(X1)) | ~sP4(X4,X2,X1)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f16])).
% 1.21/0.56  fof(f146,plain,(
% 1.21/0.56    ~spl7_3 | ~spl7_4 | spl7_10),
% 1.21/0.56    inference(avatar_contradiction_clause,[],[f145])).
% 1.21/0.56  fof(f145,plain,(
% 1.21/0.56    $false | (~spl7_3 | ~spl7_4 | spl7_10)),
% 1.21/0.56    inference(subsumption_resolution,[],[f144,f66])).
% 1.21/0.56  fof(f144,plain,(
% 1.21/0.56    ~l1_struct_0(sK0) | (~spl7_4 | spl7_10)),
% 1.21/0.56    inference(resolution,[],[f142,f101])).
% 1.21/0.56  fof(f142,plain,(
% 1.21/0.56    ( ! [X0] : (~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0)) ) | spl7_10),
% 1.21/0.56    inference(resolution,[],[f135,f31])).
% 1.21/0.56  fof(f31,plain,(
% 1.21/0.56    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f14])).
% 1.21/0.56  fof(f14,plain,(
% 1.21/0.56    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.21/0.56    inference(ennf_transformation,[],[f4])).
% 1.21/0.56  fof(f4,axiom,(
% 1.21/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 1.21/0.56  fof(f135,plain,(
% 1.21/0.56    ~l1_orders_2(sK1) | spl7_10),
% 1.21/0.56    inference(avatar_component_clause,[],[f133])).
% 1.21/0.56  fof(f133,plain,(
% 1.21/0.56    spl7_10 <=> l1_orders_2(sK1)),
% 1.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.21/0.56  fof(f141,plain,(
% 1.21/0.56    spl7_11 | spl7_7),
% 1.21/0.56    inference(avatar_split_clause,[],[f121,f115,f138])).
% 1.21/0.56  fof(f121,plain,(
% 1.21/0.56    r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | spl7_7),
% 1.21/0.56    inference(resolution,[],[f117,f44])).
% 1.21/0.56  fof(f44,plain,(
% 1.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f19])).
% 1.21/0.56  fof(f136,plain,(
% 1.21/0.56    ~spl7_10 | spl7_8),
% 1.21/0.56    inference(avatar_split_clause,[],[f131,f123,f133])).
% 1.21/0.56  fof(f123,plain,(
% 1.21/0.56    spl7_8 <=> l1_struct_0(sK1)),
% 1.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.21/0.56  fof(f131,plain,(
% 1.21/0.56    ~l1_orders_2(sK1) | spl7_8),
% 1.21/0.56    inference(resolution,[],[f125,f28])).
% 1.21/0.56  fof(f28,plain,(
% 1.21/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f12])).
% 1.21/0.56  fof(f12,plain,(
% 1.21/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.21/0.56    inference(ennf_transformation,[],[f3])).
% 1.21/0.56  fof(f3,axiom,(
% 1.21/0.56    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.21/0.56  fof(f125,plain,(
% 1.21/0.56    ~l1_struct_0(sK1) | spl7_8),
% 1.21/0.56    inference(avatar_component_clause,[],[f123])).
% 1.21/0.56  fof(f130,plain,(
% 1.21/0.56    ~spl7_8 | ~spl7_9 | spl7_1),
% 1.21/0.56    inference(avatar_split_clause,[],[f73,f54,f127,f123])).
% 1.21/0.56  fof(f73,plain,(
% 1.21/0.56    ~v1_xboole_0(u1_struct_0(sK1)) | ~l1_struct_0(sK1) | spl7_1),
% 1.21/0.56    inference(resolution,[],[f56,f29])).
% 1.21/0.56  fof(f29,plain,(
% 1.21/0.56    ( ! [X0] : (v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f13])).
% 1.21/0.56  fof(f13,plain,(
% 1.21/0.56    ! [X0] : ((v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.21/0.56    inference(ennf_transformation,[],[f5])).
% 1.21/0.56  fof(f5,axiom,(
% 1.21/0.56    ! [X0] : (l1_struct_0(X0) => (v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_struct_0)).
% 1.21/0.56  fof(f118,plain,(
% 1.21/0.56    ~spl7_7),
% 1.21/0.56    inference(avatar_split_clause,[],[f23,f115])).
% 1.21/0.56  fof(f23,plain,(
% 1.21/0.56    ~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 1.21/0.56    inference(cnf_transformation,[],[f11])).
% 1.21/0.56  fof(f11,plain,(
% 1.21/0.56    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.21/0.56    inference(flattening,[],[f10])).
% 1.21/0.56  fof(f10,plain,(
% 1.21/0.56    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.21/0.56    inference(ennf_transformation,[],[f9])).
% 1.21/0.56  fof(f9,negated_conjecture,(
% 1.21/0.56    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 1.21/0.56    inference(negated_conjecture,[],[f8])).
% 1.21/0.56  fof(f8,conjecture,(
% 1.21/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).
% 1.21/0.56  fof(f107,plain,(
% 1.21/0.56    spl7_5),
% 1.21/0.56    inference(avatar_split_clause,[],[f22,f104])).
% 1.21/0.56  fof(f22,plain,(
% 1.21/0.56    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.21/0.56    inference(cnf_transformation,[],[f11])).
% 1.21/0.56  fof(f102,plain,(
% 1.21/0.56    spl7_4),
% 1.21/0.56    inference(avatar_split_clause,[],[f25,f99])).
% 1.21/0.56  fof(f25,plain,(
% 1.21/0.56    l1_waybel_0(sK1,sK0)),
% 1.21/0.56    inference(cnf_transformation,[],[f11])).
% 1.21/0.56  fof(f67,plain,(
% 1.21/0.56    spl7_3),
% 1.21/0.56    inference(avatar_split_clause,[],[f27,f64])).
% 1.21/0.56  fof(f27,plain,(
% 1.21/0.56    l1_struct_0(sK0)),
% 1.21/0.56    inference(cnf_transformation,[],[f11])).
% 1.21/0.56  fof(f62,plain,(
% 1.21/0.56    ~spl7_2),
% 1.21/0.56    inference(avatar_split_clause,[],[f26,f59])).
% 1.21/0.56  fof(f26,plain,(
% 1.21/0.56    ~v2_struct_0(sK0)),
% 1.21/0.56    inference(cnf_transformation,[],[f11])).
% 1.21/0.56  fof(f57,plain,(
% 1.21/0.56    ~spl7_1),
% 1.21/0.56    inference(avatar_split_clause,[],[f24,f54])).
% 1.21/0.56  fof(f24,plain,(
% 1.21/0.56    ~v2_struct_0(sK1)),
% 1.21/0.56    inference(cnf_transformation,[],[f11])).
% 1.21/0.56  % SZS output end Proof for theBenchmark
% 1.21/0.56  % (4739)------------------------------
% 1.21/0.56  % (4739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.56  % (4739)Termination reason: Refutation
% 1.21/0.56  
% 1.21/0.56  % (4739)Memory used [KB]: 11001
% 1.21/0.56  % (4739)Time elapsed: 0.110 s
% 1.21/0.56  % (4739)------------------------------
% 1.21/0.56  % (4739)------------------------------
% 1.21/0.56  % (4718)Success in time 0.19 s
%------------------------------------------------------------------------------

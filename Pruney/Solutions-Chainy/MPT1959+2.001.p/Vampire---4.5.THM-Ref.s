%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:50 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 250 expanded)
%              Number of leaves         :   32 (  95 expanded)
%              Depth                    :    9
%              Number of atoms          :  411 (1138 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f605,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f94,f99,f108,f109,f115,f132,f164,f430,f498,f515,f520,f564,f573,f574,f597,f600,f602,f604])).

fof(f604,plain,(
    ~ spl5_30 ),
    inference(avatar_contradiction_clause,[],[f603])).

fof(f603,plain,
    ( $false
    | ~ spl5_30 ),
    inference(resolution,[],[f376,f125])).

fof(f125,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(global_subsumption,[],[f116,f62])).

fof(f62,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f116,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f59,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f376,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl5_30
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f602,plain,
    ( spl5_30
    | ~ spl5_8
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f352,f153,f101,f374])).

fof(f101,plain,
    ( spl5_8
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f153,plain,
    ( spl5_16
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f352,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl5_8
    | ~ spl5_16 ),
    inference(backward_demodulation,[],[f102,f155])).

fof(f155,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f153])).

fof(f102,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f600,plain,
    ( spl5_16
    | ~ spl5_43
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f582,f451,f467,f153])).

fof(f467,plain,
    ( spl5_43
  <=> r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f451,plain,
    ( spl5_39
  <=> r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f582,plain,
    ( ~ r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1)
    | sK1 = u1_struct_0(sK0)
    | ~ spl5_39 ),
    inference(resolution,[],[f453,f55])).

% (17147)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f453,plain,
    ( r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f451])).

fof(f597,plain,
    ( ~ spl5_48
    | ~ spl5_9
    | ~ spl5_10
    | spl5_43
    | ~ spl5_22
    | ~ spl5_53 ),
    inference(avatar_split_clause,[],[f596,f570,f274,f467,f112,f105,f487])).

fof(f487,plain,
    ( spl5_48
  <=> m1_subset_1(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f105,plain,
    ( spl5_9
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f112,plain,
    ( spl5_10
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f274,plain,
    ( spl5_22
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f570,plain,
    ( spl5_53
  <=> r1_orders_2(sK0,k3_yellow_0(sK0),sK4(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f596,plain,
    ( r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ m1_subset_1(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_22
    | ~ spl5_53 ),
    inference(resolution,[],[f572,f275])).

fof(f275,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f274])).

fof(f572,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK4(sK1,u1_struct_0(sK0)))
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f570])).

fof(f574,plain,
    ( spl5_39
    | spl5_12
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f568,f487,f129,f451])).

fof(f129,plain,
    ( spl5_12
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f568,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_48 ),
    inference(resolution,[],[f489,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f489,plain,
    ( m1_subset_1(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f487])).

fof(f573,plain,
    ( spl5_53
    | spl5_4
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f567,f487,f76,f71,f66,f81,f570])).

fof(f81,plain,
    ( spl5_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f66,plain,
    ( spl5_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f71,plain,
    ( spl5_2
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f76,plain,
    ( spl5_3
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f567,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,k3_yellow_0(sK0),sK4(sK1,u1_struct_0(sK0)))
    | ~ spl5_48 ),
    inference(resolution,[],[f489,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_orders_2(X0,k3_yellow_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f564,plain,
    ( spl5_16
    | spl5_48
    | ~ spl5_5
    | spl5_39 ),
    inference(avatar_split_clause,[],[f560,f451,f86,f487,f153])).

fof(f86,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f560,plain,
    ( m1_subset_1(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | ~ spl5_5
    | spl5_39 ),
    inference(resolution,[],[f299,f452])).

fof(f452,plain,
    ( ~ r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl5_39 ),
    inference(avatar_component_clause,[],[f451])).

fof(f299,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0),X0)
        | m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | sK1 = X0 )
    | ~ spl5_5 ),
    inference(resolution,[],[f180,f88])).

fof(f88,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | X0 = X1
      | r2_hidden(sK4(X0,X1),X1)
      | m1_subset_1(sK4(X0,X1),X2) ) ),
    inference(resolution,[],[f54,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f520,plain,
    ( spl5_15
    | spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f519,f112,f129,f146])).

fof(f146,plain,
    ( spl5_15
  <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f519,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(resolution,[],[f114,f51])).

fof(f114,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f515,plain,
    ( sK1 != u1_struct_0(sK0)
    | r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f498,plain,
    ( spl5_48
    | spl5_43
    | spl5_16 ),
    inference(avatar_split_clause,[],[f440,f153,f467,f487])).

fof(f440,plain,
    ( r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1)
    | m1_subset_1(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl5_16 ),
    inference(extensionality_resolution,[],[f179,f154])).

fof(f154,plain,
    ( sK1 != u1_struct_0(sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f153])).

fof(f179,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK4(X3,X4),X3)
      | m1_subset_1(sK4(X3,X4),X4)
      | X3 = X4 ) ),
    inference(resolution,[],[f54,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f430,plain,
    ( ~ spl5_6
    | spl5_22
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f417,f86,f66,f274,f91])).

fof(f91,plain,
    ( spl5_6
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f417,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ v13_waybel_0(sK1,sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f88,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f164,plain,
    ( spl5_8
    | spl5_16
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f162,f86,f153,f101])).

fof(f162,plain,
    ( sK1 = u1_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f52,f88])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f132,plain,
    ( spl5_7
    | ~ spl5_12
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f126,f86,f129,f96])).

fof(f96,plain,
    ( spl5_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f126,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f48,f88])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f115,plain,
    ( spl5_10
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f110,f66,f112])).

fof(f110,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f41,f68])).

fof(f68,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f109,plain,
    ( spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f32,f105,f101])).

fof(f32,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f108,plain,
    ( ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f33,f105,f101])).

fof(f33,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f34,f96])).

fof(f34,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f35,f91])).

fof(f35,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f36,f86])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f37,f81])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f38,f76])).

fof(f38,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f39,f71])).

fof(f39,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f40,f66])).

fof(f40,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:55:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (17148)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (17156)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (17141)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (17144)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.53  % (17148)Refutation not found, incomplete strategy% (17148)------------------------------
% 1.25/0.53  % (17148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (17148)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (17148)Memory used [KB]: 10746
% 1.25/0.53  % (17148)Time elapsed: 0.108 s
% 1.25/0.53  % (17148)------------------------------
% 1.25/0.53  % (17148)------------------------------
% 1.25/0.53  % (17154)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.53  % (17156)Refutation found. Thanks to Tanya!
% 1.25/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f605,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f94,f99,f108,f109,f115,f132,f164,f430,f498,f515,f520,f564,f573,f574,f597,f600,f602,f604])).
% 1.25/0.53  fof(f604,plain,(
% 1.25/0.53    ~spl5_30),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f603])).
% 1.25/0.53  fof(f603,plain,(
% 1.25/0.53    $false | ~spl5_30),
% 1.25/0.53    inference(resolution,[],[f376,f125])).
% 1.25/0.53  fof(f125,plain,(
% 1.25/0.53    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 1.25/0.53    inference(global_subsumption,[],[f116,f62])).
% 1.25/0.53  fof(f62,plain,(
% 1.25/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.25/0.53    inference(equality_resolution,[],[f53])).
% 1.25/0.53  fof(f53,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f28])).
% 1.25/0.53  fof(f28,plain,(
% 1.25/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.25/0.53    inference(ennf_transformation,[],[f11])).
% 1.25/0.53  fof(f11,axiom,(
% 1.25/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.25/0.53  fof(f116,plain,(
% 1.25/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.25/0.53    inference(resolution,[],[f59,f63])).
% 1.25/0.53  fof(f63,plain,(
% 1.25/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.25/0.53    inference(equality_resolution,[],[f57])).
% 1.25/0.53  fof(f57,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f2,axiom,(
% 1.25/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.25/0.53  fof(f59,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f6])).
% 1.25/0.53  fof(f6,axiom,(
% 1.25/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.25/0.53  fof(f376,plain,(
% 1.25/0.53    v1_subset_1(sK1,sK1) | ~spl5_30),
% 1.25/0.53    inference(avatar_component_clause,[],[f374])).
% 1.25/0.53  fof(f374,plain,(
% 1.25/0.53    spl5_30 <=> v1_subset_1(sK1,sK1)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.25/0.53  fof(f602,plain,(
% 1.25/0.53    spl5_30 | ~spl5_8 | ~spl5_16),
% 1.25/0.53    inference(avatar_split_clause,[],[f352,f153,f101,f374])).
% 1.25/0.53  fof(f101,plain,(
% 1.25/0.53    spl5_8 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.25/0.53  fof(f153,plain,(
% 1.25/0.53    spl5_16 <=> sK1 = u1_struct_0(sK0)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.25/0.53  fof(f352,plain,(
% 1.25/0.53    v1_subset_1(sK1,sK1) | (~spl5_8 | ~spl5_16)),
% 1.25/0.53    inference(backward_demodulation,[],[f102,f155])).
% 1.25/0.53  fof(f155,plain,(
% 1.25/0.53    sK1 = u1_struct_0(sK0) | ~spl5_16),
% 1.25/0.53    inference(avatar_component_clause,[],[f153])).
% 1.25/0.53  fof(f102,plain,(
% 1.25/0.53    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_8),
% 1.25/0.53    inference(avatar_component_clause,[],[f101])).
% 1.25/0.53  fof(f600,plain,(
% 1.25/0.53    spl5_16 | ~spl5_43 | ~spl5_39),
% 1.25/0.53    inference(avatar_split_clause,[],[f582,f451,f467,f153])).
% 1.25/0.53  fof(f467,plain,(
% 1.25/0.53    spl5_43 <=> r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 1.25/0.53  fof(f451,plain,(
% 1.25/0.53    spl5_39 <=> r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.25/0.53  fof(f582,plain,(
% 1.25/0.53    ~r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1) | sK1 = u1_struct_0(sK0) | ~spl5_39),
% 1.25/0.53    inference(resolution,[],[f453,f55])).
% 1.25/0.53  % (17147)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.53  fof(f55,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 1.25/0.53    inference(cnf_transformation,[],[f29])).
% 1.25/0.53  fof(f29,plain,(
% 1.25/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.25/0.53    inference(ennf_transformation,[],[f1])).
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.25/0.53  fof(f453,plain,(
% 1.25/0.53    r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl5_39),
% 1.25/0.53    inference(avatar_component_clause,[],[f451])).
% 1.25/0.53  fof(f597,plain,(
% 1.25/0.53    ~spl5_48 | ~spl5_9 | ~spl5_10 | spl5_43 | ~spl5_22 | ~spl5_53),
% 1.25/0.53    inference(avatar_split_clause,[],[f596,f570,f274,f467,f112,f105,f487])).
% 1.25/0.53  fof(f487,plain,(
% 1.25/0.53    spl5_48 <=> m1_subset_1(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 1.25/0.53  fof(f105,plain,(
% 1.25/0.53    spl5_9 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.25/0.53  fof(f112,plain,(
% 1.25/0.53    spl5_10 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.25/0.53  fof(f274,plain,(
% 1.25/0.53    spl5_22 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X1,sK1) | ~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.25/0.53  fof(f570,plain,(
% 1.25/0.53    spl5_53 <=> r1_orders_2(sK0,k3_yellow_0(sK0),sK4(sK1,u1_struct_0(sK0)))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 1.25/0.53  fof(f596,plain,(
% 1.25/0.53    r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | (~spl5_22 | ~spl5_53)),
% 1.25/0.53    inference(resolution,[],[f572,f275])).
% 1.25/0.53  fof(f275,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_22),
% 1.25/0.53    inference(avatar_component_clause,[],[f274])).
% 1.25/0.53  fof(f572,plain,(
% 1.25/0.53    r1_orders_2(sK0,k3_yellow_0(sK0),sK4(sK1,u1_struct_0(sK0))) | ~spl5_53),
% 1.25/0.53    inference(avatar_component_clause,[],[f570])).
% 1.25/0.53  fof(f574,plain,(
% 1.25/0.53    spl5_39 | spl5_12 | ~spl5_48),
% 1.25/0.53    inference(avatar_split_clause,[],[f568,f487,f129,f451])).
% 1.25/0.53  fof(f129,plain,(
% 1.25/0.53    spl5_12 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.25/0.53  fof(f568,plain,(
% 1.25/0.53    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl5_48),
% 1.25/0.53    inference(resolution,[],[f489,f51])).
% 1.25/0.53  fof(f51,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f27])).
% 1.25/0.53  fof(f27,plain,(
% 1.25/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.25/0.53    inference(flattening,[],[f26])).
% 1.25/0.53  fof(f26,plain,(
% 1.25/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f5])).
% 1.25/0.53  fof(f5,axiom,(
% 1.25/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.25/0.53  fof(f489,plain,(
% 1.25/0.53    m1_subset_1(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl5_48),
% 1.25/0.53    inference(avatar_component_clause,[],[f487])).
% 1.25/0.53  fof(f573,plain,(
% 1.25/0.53    spl5_53 | spl5_4 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_48),
% 1.25/0.53    inference(avatar_split_clause,[],[f567,f487,f76,f71,f66,f81,f570])).
% 1.25/0.53  fof(f81,plain,(
% 1.25/0.53    spl5_4 <=> v2_struct_0(sK0)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.25/0.53  fof(f66,plain,(
% 1.25/0.53    spl5_1 <=> l1_orders_2(sK0)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.25/0.53  fof(f71,plain,(
% 1.25/0.53    spl5_2 <=> v1_yellow_0(sK0)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.25/0.53  fof(f76,plain,(
% 1.25/0.53    spl5_3 <=> v5_orders_2(sK0)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.25/0.53  fof(f567,plain,(
% 1.25/0.53    ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_orders_2(sK0,k3_yellow_0(sK0),sK4(sK1,u1_struct_0(sK0))) | ~spl5_48),
% 1.25/0.53    inference(resolution,[],[f489,f49])).
% 1.25/0.53  fof(f49,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,k3_yellow_0(X0),X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f24])).
% 1.25/0.53  fof(f24,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.25/0.53    inference(flattening,[],[f23])).
% 1.25/0.53  fof(f23,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.25/0.53    inference(ennf_transformation,[],[f9])).
% 1.25/0.53  fof(f9,axiom,(
% 1.25/0.53    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 1.25/0.53  fof(f564,plain,(
% 1.25/0.53    spl5_16 | spl5_48 | ~spl5_5 | spl5_39),
% 1.25/0.53    inference(avatar_split_clause,[],[f560,f451,f86,f487,f153])).
% 1.25/0.53  fof(f86,plain,(
% 1.25/0.53    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.25/0.53  fof(f560,plain,(
% 1.25/0.53    m1_subset_1(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | (~spl5_5 | spl5_39)),
% 1.25/0.53    inference(resolution,[],[f299,f452])).
% 1.25/0.53  fof(f452,plain,(
% 1.25/0.53    ~r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | spl5_39),
% 1.25/0.53    inference(avatar_component_clause,[],[f451])).
% 1.25/0.53  fof(f299,plain,(
% 1.25/0.53    ( ! [X0] : (r2_hidden(sK4(sK1,X0),X0) | m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) | sK1 = X0) ) | ~spl5_5),
% 1.25/0.53    inference(resolution,[],[f180,f88])).
% 1.25/0.53  fof(f88,plain,(
% 1.25/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 1.25/0.53    inference(avatar_component_clause,[],[f86])).
% 1.25/0.53  fof(f180,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X2)) | X0 = X1 | r2_hidden(sK4(X0,X1),X1) | m1_subset_1(sK4(X0,X1),X2)) )),
% 1.25/0.53    inference(resolution,[],[f54,f61])).
% 1.25/0.53  fof(f61,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f31])).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.25/0.53    inference(flattening,[],[f30])).
% 1.25/0.53  fof(f30,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.25/0.53    inference(ennf_transformation,[],[f7])).
% 1.25/0.53  fof(f7,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.25/0.53  fof(f54,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 1.25/0.53    inference(cnf_transformation,[],[f29])).
% 1.25/0.53  fof(f520,plain,(
% 1.25/0.53    spl5_15 | spl5_12 | ~spl5_10),
% 1.25/0.53    inference(avatar_split_clause,[],[f519,f112,f129,f146])).
% 1.25/0.53  fof(f146,plain,(
% 1.25/0.53    spl5_15 <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.25/0.53  fof(f519,plain,(
% 1.25/0.53    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl5_10),
% 1.25/0.53    inference(resolution,[],[f114,f51])).
% 1.25/0.53  fof(f114,plain,(
% 1.25/0.53    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl5_10),
% 1.25/0.53    inference(avatar_component_clause,[],[f112])).
% 1.25/0.53  fof(f515,plain,(
% 1.25/0.53    sK1 != u1_struct_0(sK0) | r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.25/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.25/0.53  fof(f498,plain,(
% 1.25/0.53    spl5_48 | spl5_43 | spl5_16),
% 1.25/0.53    inference(avatar_split_clause,[],[f440,f153,f467,f487])).
% 1.25/0.53  fof(f440,plain,(
% 1.25/0.53    r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1) | m1_subset_1(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | spl5_16),
% 1.25/0.53    inference(extensionality_resolution,[],[f179,f154])).
% 1.25/0.53  fof(f154,plain,(
% 1.25/0.53    sK1 != u1_struct_0(sK0) | spl5_16),
% 1.25/0.53    inference(avatar_component_clause,[],[f153])).
% 1.25/0.53  fof(f179,plain,(
% 1.25/0.53    ( ! [X4,X3] : (r2_hidden(sK4(X3,X4),X3) | m1_subset_1(sK4(X3,X4),X4) | X3 = X4) )),
% 1.25/0.53    inference(resolution,[],[f54,f50])).
% 1.25/0.53  fof(f50,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f25])).
% 1.25/0.53  fof(f25,plain,(
% 1.25/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.25/0.53  fof(f430,plain,(
% 1.25/0.53    ~spl5_6 | spl5_22 | ~spl5_1 | ~spl5_5),
% 1.25/0.53    inference(avatar_split_clause,[],[f417,f86,f66,f274,f91])).
% 1.25/0.53  fof(f91,plain,(
% 1.25/0.53    spl5_6 <=> v13_waybel_0(sK1,sK0)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.25/0.53  fof(f417,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~v13_waybel_0(sK1,sK0)) ) | ~spl5_5),
% 1.25/0.53    inference(resolution,[],[f88,f46])).
% 1.25/0.53  fof(f46,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f21])).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.25/0.53    inference(flattening,[],[f20])).
% 1.25/0.53  fof(f20,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f10])).
% 1.25/0.53  fof(f10,axiom,(
% 1.25/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.25/0.53  fof(f164,plain,(
% 1.25/0.53    spl5_8 | spl5_16 | ~spl5_5),
% 1.25/0.53    inference(avatar_split_clause,[],[f162,f86,f153,f101])).
% 1.25/0.53  fof(f162,plain,(
% 1.25/0.53    sK1 = u1_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_5),
% 1.25/0.53    inference(resolution,[],[f52,f88])).
% 1.25/0.53  fof(f52,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f28])).
% 1.25/0.53  fof(f132,plain,(
% 1.25/0.53    spl5_7 | ~spl5_12 | ~spl5_5),
% 1.25/0.53    inference(avatar_split_clause,[],[f126,f86,f129,f96])).
% 1.25/0.53  fof(f96,plain,(
% 1.25/0.53    spl5_7 <=> v1_xboole_0(sK1)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.25/0.53  fof(f126,plain,(
% 1.25/0.53    ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK1) | ~spl5_5),
% 1.25/0.53    inference(resolution,[],[f48,f88])).
% 1.25/0.53  fof(f48,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f22])).
% 1.25/0.53  fof(f22,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f3])).
% 1.25/0.53  fof(f3,axiom,(
% 1.25/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.25/0.53  fof(f115,plain,(
% 1.25/0.53    spl5_10 | ~spl5_1),
% 1.25/0.53    inference(avatar_split_clause,[],[f110,f66,f112])).
% 1.25/0.53  fof(f110,plain,(
% 1.25/0.53    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl5_1),
% 1.25/0.53    inference(resolution,[],[f41,f68])).
% 1.25/0.53  fof(f68,plain,(
% 1.25/0.53    l1_orders_2(sK0) | ~spl5_1),
% 1.25/0.53    inference(avatar_component_clause,[],[f66])).
% 1.25/0.53  fof(f41,plain,(
% 1.25/0.53    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f19])).
% 1.25/0.53  fof(f19,plain,(
% 1.25/0.53    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f8])).
% 1.25/0.53  fof(f8,axiom,(
% 1.25/0.53    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 1.25/0.53  fof(f109,plain,(
% 1.25/0.53    spl5_8 | ~spl5_9),
% 1.25/0.53    inference(avatar_split_clause,[],[f32,f105,f101])).
% 1.25/0.53  fof(f32,plain,(
% 1.25/0.53    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f18,plain,(
% 1.25/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.25/0.53    inference(flattening,[],[f17])).
% 1.25/0.53  fof(f17,plain,(
% 1.25/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.25/0.53    inference(ennf_transformation,[],[f16])).
% 1.25/0.53  fof(f16,plain,(
% 1.25/0.53    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.25/0.53    inference(pure_predicate_removal,[],[f15])).
% 1.25/0.53  fof(f15,plain,(
% 1.25/0.53    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.25/0.53    inference(pure_predicate_removal,[],[f14])).
% 1.25/0.53  fof(f14,plain,(
% 1.25/0.53    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.25/0.53    inference(pure_predicate_removal,[],[f13])).
% 1.25/0.53  fof(f13,negated_conjecture,(
% 1.25/0.53    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.25/0.53    inference(negated_conjecture,[],[f12])).
% 1.25/0.53  fof(f12,conjecture,(
% 1.25/0.53    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.25/0.53  fof(f108,plain,(
% 1.25/0.53    ~spl5_8 | spl5_9),
% 1.25/0.53    inference(avatar_split_clause,[],[f33,f105,f101])).
% 1.25/0.53  fof(f33,plain,(
% 1.25/0.53    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f99,plain,(
% 1.25/0.53    ~spl5_7),
% 1.25/0.53    inference(avatar_split_clause,[],[f34,f96])).
% 1.25/0.53  fof(f34,plain,(
% 1.25/0.53    ~v1_xboole_0(sK1)),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f94,plain,(
% 1.25/0.53    spl5_6),
% 1.25/0.53    inference(avatar_split_clause,[],[f35,f91])).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    v13_waybel_0(sK1,sK0)),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f89,plain,(
% 1.25/0.53    spl5_5),
% 1.25/0.53    inference(avatar_split_clause,[],[f36,f86])).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f84,plain,(
% 1.25/0.53    ~spl5_4),
% 1.25/0.53    inference(avatar_split_clause,[],[f37,f81])).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    ~v2_struct_0(sK0)),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f79,plain,(
% 1.25/0.53    spl5_3),
% 1.25/0.53    inference(avatar_split_clause,[],[f38,f76])).
% 1.25/0.53  fof(f38,plain,(
% 1.25/0.53    v5_orders_2(sK0)),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f74,plain,(
% 1.25/0.53    spl5_2),
% 1.25/0.53    inference(avatar_split_clause,[],[f39,f71])).
% 1.25/0.53  fof(f39,plain,(
% 1.25/0.53    v1_yellow_0(sK0)),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f69,plain,(
% 1.25/0.53    spl5_1),
% 1.25/0.53    inference(avatar_split_clause,[],[f40,f66])).
% 1.25/0.53  fof(f40,plain,(
% 1.25/0.53    l1_orders_2(sK0)),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  % SZS output end Proof for theBenchmark
% 1.25/0.53  % (17156)------------------------------
% 1.25/0.53  % (17156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (17156)Termination reason: Refutation
% 1.25/0.53  
% 1.25/0.53  % (17156)Memory used [KB]: 11129
% 1.25/0.53  % (17156)Time elapsed: 0.097 s
% 1.25/0.53  % (17156)------------------------------
% 1.25/0.53  % (17156)------------------------------
% 1.25/0.53  % (17139)Success in time 0.17 s
%------------------------------------------------------------------------------

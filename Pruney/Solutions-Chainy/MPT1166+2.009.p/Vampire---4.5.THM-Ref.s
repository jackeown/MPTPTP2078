%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 210 expanded)
%              Number of leaves         :   26 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  469 (1010 expanded)
%              Number of equality atoms :   35 (  81 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8301)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f171,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f40,f44,f48,f52,f56,f60,f64,f68,f72,f84,f88,f97,f101,f110,f115,f121,f133,f143,f154,f159,f167])).

fof(f167,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_17
    | spl3_25 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_17
    | spl3_25 ),
    inference(unit_resulting_resolution,[],[f51,f43,f39,f35,f47,f63,f71,f158,f100])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_orders_2(X2,X0,X1)
        | r1_tarski(X2,X1) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_orders_2(X2,X0,X1)
        | r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f158,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl3_25 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl3_25
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f63,plain,
    ( m1_orders_2(sK2,sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_8
  <=> m1_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

% (8293)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f47,plain,
    ( v5_orders_2(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f35,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,
    ( v3_orders_2(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f43,plain,
    ( v4_orders_2(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f51,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f159,plain,
    ( ~ spl3_25
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f155,f128,f82,f157])).

fof(f82,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ r2_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f128,plain,
    ( spl3_22
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f155,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(resolution,[],[f129,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ r2_xboole_0(X1,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f82])).

fof(f129,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f128])).

fof(f154,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_6
    | ~ spl3_10
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_6
    | ~ spl3_10
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f152,f35])).

fof(f152,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_6
    | ~ spl3_10
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f151,f55])).

fof(f55,plain,
    ( k1_xboole_0 != sK1
    | spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f151,plain,
    ( k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f150,f71])).

fof(f150,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f149,f51])).

fof(f149,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f148,f47])).

fof(f148,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f147,f43])).

fof(f147,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f145,f39])).

fof(f145,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(resolution,[],[f142,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X1,X0,X1)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | v2_struct_0(X0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_xboole_0 = X1
        | ~ m1_orders_2(X1,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f142,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_24
  <=> m1_orders_2(sK1,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f143,plain,
    ( spl3_24
    | ~ spl3_7
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f134,f131,f58,f141])).

fof(f58,plain,
    ( spl3_7
  <=> m1_orders_2(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f131,plain,
    ( spl3_23
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f134,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_7
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f59,f132])).

fof(f132,plain,
    ( sK1 = sK2
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f131])).

fof(f59,plain,
    ( m1_orders_2(sK1,sK0,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f133,plain,
    ( spl3_22
    | spl3_23
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f122,f119,f58,f131,f128])).

fof(f119,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK2)
        | sK2 = X0
        | r2_xboole_0(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f122,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK1,sK2)
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(resolution,[],[f120,f59])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK2)
        | sK2 = X0
        | r2_xboole_0(X0,sK2) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl3_20
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f116,f113,f66,f119])).

fof(f66,plain,
    ( spl3_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f113,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK2)
        | sK2 = X0
        | r2_xboole_0(X0,sK2) )
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(resolution,[],[f114,f67])).

fof(f67,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl3_19
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f111,f108,f86,f113])).

fof(f86,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f108,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(resolution,[],[f109,f87])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f86])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,X0)
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,
    ( spl3_18
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f106,f99,f50,f46,f42,f38,f34,f108])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | r1_tarski(X1,X0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f105,f35])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | r1_tarski(X1,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f104,f47])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | r1_tarski(X1,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f103,f43])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | r1_tarski(X1,X0) )
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f102,f39])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | r1_tarski(X1,X0) )
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(resolution,[],[f100,f51])).

fof(f101,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f26,f99])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(f97,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f25,f95])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).

fof(f88,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f29,f86])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f84,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f30,f82])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f72,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f18,f70])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( m1_orders_2(X2,X0,X1)
                    & m1_orders_2(X1,X0,X2)
                    & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

fof(f68,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f14,f66])).

fof(f14,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f17,f62])).

fof(f17,plain,(
    m1_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f16,f58])).

fof(f16,plain,(
    m1_orders_2(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f15,f54])).

fof(f15,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f46])).

fof(f22,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f38])).

fof(f20,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:52:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (8288)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (8296)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (8296)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  % (8301)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f36,f40,f44,f48,f52,f56,f60,f64,f68,f72,f84,f88,f97,f101,f110,f115,f121,f133,f143,f154,f159,f167])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_17 | spl3_25),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f163])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_17 | spl3_25)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f51,f43,f39,f35,f47,f63,f71,f158,f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1)) ) | ~spl3_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl3_17 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ~r1_tarski(sK2,sK1) | spl3_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f157])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl3_25 <=> r1_tarski(sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl3_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    m1_orders_2(sK2,sK0,sK1) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl3_8 <=> m1_orders_2(sK2,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  % (8293)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    v5_orders_2(sK0) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl3_4 <=> v5_orders_2(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl3_1 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v3_orders_2(sK0) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl3_2 <=> v3_orders_2(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    v4_orders_2(sK0) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl3_3 <=> v4_orders_2(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    l1_orders_2(sK0) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl3_5 <=> l1_orders_2(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    ~spl3_25 | ~spl3_13 | ~spl3_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f155,f128,f82,f157])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl3_13 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl3_22 <=> r2_xboole_0(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ~r1_tarski(sK2,sK1) | (~spl3_13 | ~spl3_22)),
% 0.21/0.48    inference(resolution,[],[f129,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) ) | ~spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f82])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    r2_xboole_0(sK1,sK2) | ~spl3_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f128])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_6 | ~spl3_10 | ~spl3_16 | ~spl3_24),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_6 | ~spl3_10 | ~spl3_16 | ~spl3_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f152,f35])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    v2_struct_0(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_6 | ~spl3_10 | ~spl3_16 | ~spl3_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f151,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl3_6 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | v2_struct_0(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_10 | ~spl3_16 | ~spl3_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f150,f71])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_16 | ~spl3_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f149,f51])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_16 | ~spl3_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f47])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_16 | ~spl3_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f147,f43])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | (~spl3_2 | ~spl3_16 | ~spl3_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f145,f39])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | (~spl3_16 | ~spl3_24)),
% 0.21/0.48    inference(resolution,[],[f142,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_orders_2(X1,X0,X1) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | v2_struct_0(X0)) ) | ~spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl3_16 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    m1_orders_2(sK1,sK0,sK1) | ~spl3_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl3_24 <=> m1_orders_2(sK1,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl3_24 | ~spl3_7 | ~spl3_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f134,f131,f58,f141])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl3_7 <=> m1_orders_2(sK1,sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl3_23 <=> sK1 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    m1_orders_2(sK1,sK0,sK1) | (~spl3_7 | ~spl3_23)),
% 0.21/0.48    inference(backward_demodulation,[],[f59,f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    sK1 = sK2 | ~spl3_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f131])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    m1_orders_2(sK1,sK0,sK2) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f58])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    spl3_22 | spl3_23 | ~spl3_7 | ~spl3_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f122,f119,f58,f131,f128])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl3_20 <=> ! [X0] : (~m1_orders_2(X0,sK0,sK2) | sK2 = X0 | r2_xboole_0(X0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    sK1 = sK2 | r2_xboole_0(sK1,sK2) | (~spl3_7 | ~spl3_20)),
% 0.21/0.48    inference(resolution,[],[f120,f59])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | sK2 = X0 | r2_xboole_0(X0,sK2)) ) | ~spl3_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f119])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl3_20 | ~spl3_9 | ~spl3_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f116,f113,f66,f119])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl3_9 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl3_19 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | X0 = X1 | r2_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | sK2 = X0 | r2_xboole_0(X0,sK2)) ) | (~spl3_9 | ~spl3_19)),
% 0.21/0.48    inference(resolution,[],[f114,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f66])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) ) | ~spl3_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f113])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl3_19 | ~spl3_14 | ~spl3_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f111,f108,f86,f113])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl3_14 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl3_18 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | X0 = X1 | r2_xboole_0(X0,X1)) ) | (~spl3_14 | ~spl3_18)),
% 0.21/0.48    inference(resolution,[],[f109,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) ) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~m1_orders_2(X1,sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f108])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl3_18 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f106,f99,f50,f46,f42,f38,f34,f108])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f35])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f104,f47])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f103,f43])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0)) ) | (~spl3_2 | ~spl3_5 | ~spl3_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f102,f39])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0)) ) | (~spl3_5 | ~spl3_17)),
% 0.21/0.48    inference(resolution,[],[f100,f51])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl3_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f99])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl3_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f95])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl3_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f86])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f82])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f70])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f66])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f62])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    m1_orders_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f58])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    m1_orders_2(sK1,sK0,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f54])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f50])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    l1_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f46])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    v5_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f42])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v4_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f38])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    v3_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f34])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (8296)------------------------------
% 0.21/0.48  % (8296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8296)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (8296)Memory used [KB]: 10618
% 0.21/0.48  % (8296)Time elapsed: 0.056 s
% 0.21/0.48  % (8296)------------------------------
% 0.21/0.48  % (8296)------------------------------
% 0.21/0.49  % (8286)Success in time 0.123 s
%------------------------------------------------------------------------------

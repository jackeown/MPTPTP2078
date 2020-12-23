%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1305+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:41 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 224 expanded)
%              Number of leaves         :   20 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  343 ( 717 expanded)
%              Number of equality atoms :   15 (  28 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f49,f53,f57,f77,f102,f156,f172,f176,f180,f193,f216,f243,f252])).

fof(f252,plain,
    ( spl6_18
    | spl6_24
    | ~ spl6_27 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl6_18
    | spl6_24
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f250,f192])).

fof(f192,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_18
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f250,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | spl6_24
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f248,f215])).

fof(f215,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl6_24
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f248,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl6_27 ),
    inference(resolution,[],[f242,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f242,plain,
    ( sP5(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl6_27
  <=> sP5(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f243,plain,
    ( spl6_27
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f181,f174,f241])).

fof(f174,plain,
    ( spl6_16
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f181,plain,
    ( sP5(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl6_16 ),
    inference(resolution,[],[f175,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f175,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f216,plain,
    ( ~ spl6_24
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | spl6_15
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f189,f178,f170,f51,f47,f39,f214])).

fof(f39,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f47,plain,
    ( spl6_3
  <=> v2_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f51,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f170,plain,
    ( spl6_15
  <=> v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f178,plain,
    ( spl6_17
  <=> m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f189,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | spl6_15
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f185,f171])).

fof(f171,plain,
    ( ~ v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f185,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(resolution,[],[f179,f65])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK2)
        | v4_pre_topc(X0,sK0) )
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f64,f48])).

fof(f48,plain,
    ( v2_tops_2(sK2,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK2)
        | v4_pre_topc(X0,sK0)
        | ~ v2_tops_2(sK2,sK0) )
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f58,f40])).

fof(f40,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK2)
        | v4_pre_topc(X0,sK0)
        | ~ v2_tops_2(sK2,sK0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f52,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v4_pre_topc(X2,X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(f52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f179,plain,
    ( m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f178])).

fof(f193,plain,
    ( ~ spl6_18
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | spl6_15
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f188,f178,f170,f55,f43,f39,f191])).

fof(f43,plain,
    ( spl6_2
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f55,plain,
    ( spl6_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f188,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | spl6_15
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f184,f171])).

fof(f184,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_17 ),
    inference(resolution,[],[f179,f73])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f72,f44])).

fof(f44,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0)
        | ~ v2_tops_2(sK1,sK0) )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f66,f40])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0)
        | ~ v2_tops_2(sK1,sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f56,f24])).

fof(f56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f55])).

% (20149)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (20158)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (20153)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f180,plain,
    ( spl6_17
    | ~ spl6_1
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f164,f154,f100,f75,f39,f178])).

fof(f75,plain,
    ( spl6_6
  <=> v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f100,plain,
    ( spl6_9
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f154,plain,
    ( spl6_12
  <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f164,plain,
    ( m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_1
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f132,f161])).

fof(f161,plain,
    ( ~ v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | spl6_6
    | ~ spl6_12 ),
    inference(superposition,[],[f76,f155])).

fof(f155,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f76,plain,
    ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f132,plain,
    ( m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f126,f40])).

fof(f126,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f101,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f101,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f176,plain,
    ( spl6_16
    | ~ spl6_1
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f163,f154,f100,f75,f39,f174])).

fof(f163,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl6_1
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f133,f161])).

fof(f133,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f127,f40])).

fof(f127,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f101,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f172,plain,
    ( ~ spl6_15
    | ~ spl6_1
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f162,f154,f100,f75,f39,f170])).

fof(f162,plain,
    ( ~ v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl6_1
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f134,f161])).

fof(f134,plain,
    ( ~ v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f128,f40])).

fof(f128,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f101,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(sK3(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f156,plain,
    ( spl6_12
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f81,f55,f51,f154])).

fof(f81,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f71,f52])).

fof(f71,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2) = k2_xboole_0(sK1,X2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f56,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f102,plain,
    ( spl6_9
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f90,f55,f51,f100])).

fof(f90,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f88,f80])).

fof(f80,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f79,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f79,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK2,sK1)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f63,f56])).

fof(f63,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,X2) = k2_xboole_0(sK2,X2) )
    | ~ spl6_4 ),
    inference(resolution,[],[f52,f22])).

fof(f88,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f62,f56])).

fof(f62,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl6_4 ),
    inference(resolution,[],[f52,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f77,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f19,f75])).

fof(f19,plain,(
    ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X2,X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X2,X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v2_tops_2(X2,X0)
                    & v2_tops_2(X1,X0) )
                 => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & v2_tops_2(X1,X0) )
               => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tops_2)).

fof(f57,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f20,f55])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f16,f51])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f18,f47])).

fof(f18,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f17,f43])).

fof(f17,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------

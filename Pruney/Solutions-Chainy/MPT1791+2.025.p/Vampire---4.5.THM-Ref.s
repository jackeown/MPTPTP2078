%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 275 expanded)
%              Number of leaves         :   32 ( 122 expanded)
%              Depth                    :   10
%              Number of atoms          :  568 (1159 expanded)
%              Number of equality atoms :   47 ( 158 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f72,f76,f80,f84,f88,f95,f103,f109,f116,f121,f135,f146,f150,f162,f178,f203,f214,f219,f222,f238])).

fof(f238,plain,
    ( spl2_6
    | ~ spl2_5
    | ~ spl2_4
    | ~ spl2_3
    | spl2_2
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f231,f201,f67,f74,f78,f82,f86])).

fof(f86,plain,
    ( spl2_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f82,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f78,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f74,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f67,plain,
    ( spl2_2
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f201,plain,
    ( spl2_26
  <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f231,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_26 ),
    inference(superposition,[],[f54,f202])).

fof(f202,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f201])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f222,plain,
    ( ~ spl2_16
    | ~ spl2_4
    | ~ spl2_7
    | spl2_17 ),
    inference(avatar_split_clause,[],[f220,f153,f93,f78,f144])).

fof(f144,plain,
    ( spl2_16
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f93,plain,
    ( spl2_7
  <=> ! [X0] :
        ( m1_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f153,plain,
    ( spl2_17
  <=> m1_pre_topc(sK0,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f220,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl2_7
    | spl2_17 ),
    inference(resolution,[],[f154,f94])).

fof(f94,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f154,plain,
    ( ~ m1_pre_topc(sK0,k6_tmap_1(sK0,sK1))
    | spl2_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f219,plain,
    ( ~ spl2_17
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f217,f133,f74,f153])).

fof(f133,plain,
    ( spl2_14
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,k6_tmap_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f217,plain,
    ( ~ m1_pre_topc(sK0,k6_tmap_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(resolution,[],[f134,f75])).

fof(f75,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,k6_tmap_1(sK0,sK1)) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f214,plain,
    ( ~ spl2_16
    | ~ spl2_2
    | ~ spl2_4
    | spl2_20 ),
    inference(avatar_split_clause,[],[f212,f167,f78,f67,f144])).

fof(f167,plain,
    ( spl2_20
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f212,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ spl2_2
    | ~ spl2_4
    | spl2_20 ),
    inference(resolution,[],[f180,f79])).

fof(f79,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0) )
    | ~ spl2_2
    | spl2_20 ),
    inference(subsumption_resolution,[],[f89,f179])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k6_tmap_1(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl2_20 ),
    inference(resolution,[],[f168,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

% (31431)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f168,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl2_20 ),
    inference(avatar_component_clause,[],[f167])).

fof(f89,plain,
    ( ! [X0] :
        ( m1_pre_topc(k6_tmap_1(sK0,sK1),X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_2 ),
    inference(superposition,[],[f50,f71])).

fof(f71,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f203,plain,
    ( ~ spl2_3
    | spl2_26
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f196,f107,f64,f201,f74])).

fof(f64,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f107,plain,
    ( spl2_9
  <=> ! [X0] :
        ( u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f196,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(resolution,[],[f70,f108])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f70,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f178,plain,
    ( ~ spl2_20
    | spl2_14
    | spl2_18 ),
    inference(avatar_split_clause,[],[f177,f160,f133,f167])).

fof(f160,plain,
    ( spl2_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) )
    | spl2_18 ),
    inference(resolution,[],[f161,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f161,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    | spl2_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( ~ spl2_18
    | spl2_1
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f156,f130,f114,f64,f160])).

fof(f114,plain,
    ( spl2_10
  <=> ! [X0] :
        ( ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f130,plain,
    ( spl2_13
  <=> v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f156,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(resolution,[],[f131,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f131,plain,
    ( v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f150,plain,
    ( ~ spl2_4
    | spl2_16 ),
    inference(avatar_split_clause,[],[f147,f144,f78])).

fof(f147,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_16 ),
    inference(resolution,[],[f145,f46])).

% (31430)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (31441)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f46,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f145,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | spl2_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,
    ( ~ spl2_16
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f141,f127,f78,f67,f144])).

fof(f127,plain,
    ( spl2_12
  <=> ! [X1] :
        ( ~ m1_pre_topc(k6_tmap_1(sK0,sK1),X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f141,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(resolution,[],[f140,f79])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0) )
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f89,f128])).

fof(f128,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k6_tmap_1(sK0,sK1),X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f135,plain,
    ( spl2_12
    | spl2_13
    | spl2_14
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f124,f119,f74,f133,f130,f127])).

fof(f119,plain,
    ( spl2_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))
        | v3_pre_topc(X0,k6_tmap_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
        | ~ m1_pre_topc(k6_tmap_1(sK0,sK1),X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(resolution,[],[f123,f75])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,k6_tmap_1(sK0,X0))
        | v3_pre_topc(X0,k6_tmap_1(sK0,X0))
        | ~ m1_pre_topc(k6_tmap_1(sK0,X0),X2)
        | ~ l1_pre_topc(X2) )
    | ~ spl2_11 ),
    inference(resolution,[],[f122,f49])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(k6_tmap_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,k6_tmap_1(sK0,X0))
        | v3_pre_topc(X0,k6_tmap_1(sK0,X0)) )
    | ~ spl2_11 ),
    inference(resolution,[],[f120,f51])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))
        | v3_pre_topc(X0,k6_tmap_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_11
    | spl2_6 ),
    inference(avatar_split_clause,[],[f117,f86,f119,f78,f82])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v3_pre_topc(X0,k6_tmap_1(sK0,X0)) )
    | spl2_6 ),
    inference(resolution,[],[f62,f87])).

fof(f87,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f62,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(X2,k6_tmap_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f116,plain,
    ( ~ spl2_4
    | spl2_10
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f112,f82,f67,f114,f78])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(X0,sK0) )
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f111,f71])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(X0,sK0) )
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f110,f71])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(X0,sK0) )
    | ~ spl2_5 ),
    inference(resolution,[],[f60,f83])).

fof(f83,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f109,plain,
    ( ~ spl2_4
    | spl2_9
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f105,f101,f107,f78])).

fof(f101,plain,
    ( spl2_8
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK0))
        | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f105,plain,
    ( ! [X0] :
        ( u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_8 ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( ! [X0] :
        ( u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_8 ),
    inference(resolution,[],[f102,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK0))
        | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_8
    | spl2_6 ),
    inference(avatar_split_clause,[],[f98,f86,f101,f78,f82])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) )
    | spl2_6 ),
    inference(resolution,[],[f55,f87])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f95,plain,
    ( ~ spl2_4
    | spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f90,f67,f93,f78])).

fof(f90,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_2 ),
    inference(superposition,[],[f47,f71])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f88,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f40,f86])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f84,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f42,f78])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f43,f74])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f44,f67,f64])).

fof(f44,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f45,f67,f64])).

fof(f45,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (31433)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (31446)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (31433)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (31432)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f239,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f69,f72,f76,f80,f84,f88,f95,f103,f109,f116,f121,f135,f146,f150,f162,f178,f203,f214,f219,f222,f238])).
% 0.20/0.47  fof(f238,plain,(
% 0.20/0.47    spl2_6 | ~spl2_5 | ~spl2_4 | ~spl2_3 | spl2_2 | ~spl2_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f231,f201,f67,f74,f78,f82,f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl2_6 <=> v2_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl2_5 <=> v2_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl2_4 <=> l1_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl2_2 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.47  fof(f201,plain,(
% 0.20/0.47    spl2_26 <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.20/0.47  fof(f231,plain,(
% 0.20/0.47    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl2_26),
% 0.20/0.47    inference(superposition,[],[f54,f202])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~spl2_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f201])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).
% 0.20/0.47  fof(f222,plain,(
% 0.20/0.47    ~spl2_16 | ~spl2_4 | ~spl2_7 | spl2_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f220,f153,f93,f78,f144])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    spl2_16 <=> m1_pre_topc(sK0,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl2_7 <=> ! [X0] : (m1_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    spl2_17 <=> m1_pre_topc(sK0,k6_tmap_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.47  fof(f220,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK0,sK0) | (~spl2_7 | spl2_17)),
% 0.20/0.47    inference(resolution,[],[f154,f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    ( ! [X0] : (m1_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl2_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f93])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    ~m1_pre_topc(sK0,k6_tmap_1(sK0,sK1)) | spl2_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f153])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    ~spl2_17 | ~spl2_3 | ~spl2_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f217,f133,f74,f153])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    spl2_14 <=> ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,k6_tmap_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    ~m1_pre_topc(sK0,k6_tmap_1(sK0,sK1)) | (~spl2_3 | ~spl2_14)),
% 0.20/0.47    inference(resolution,[],[f134,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f74])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,k6_tmap_1(sK0,sK1))) ) | ~spl2_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f133])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    ~spl2_16 | ~spl2_2 | ~spl2_4 | spl2_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f212,f167,f78,f67,f144])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    spl2_20 <=> l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.47  fof(f212,plain,(
% 0.20/0.47    ~m1_pre_topc(sK0,sK0) | (~spl2_2 | ~spl2_4 | spl2_20)),
% 0.20/0.47    inference(resolution,[],[f180,f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    l1_pre_topc(sK0) | ~spl2_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f78])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0)) ) | (~spl2_2 | spl2_20)),
% 0.20/0.47    inference(subsumption_resolution,[],[f89,f179])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_pre_topc(k6_tmap_1(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | spl2_20),
% 0.20/0.47    inference(resolution,[],[f168,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  % (31431)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | spl2_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f167])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ( ! [X0] : (m1_pre_topc(k6_tmap_1(sK0,sK1),X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0)) ) | ~spl2_2),
% 0.20/0.47    inference(superposition,[],[f50,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~spl2_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f67])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.20/0.48  fof(f203,plain,(
% 0.20/0.48    ~spl2_3 | spl2_26 | ~spl2_1 | ~spl2_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f196,f107,f64,f201,f74])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    spl2_9 <=> ! [X0] : (u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.48  fof(f196,plain,(
% 0.20/0.48    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_9)),
% 0.20/0.48    inference(resolution,[],[f70,f108])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    ( ! [X0] : (~v3_pre_topc(X0,sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f107])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    v3_pre_topc(sK1,sK0) | ~spl2_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f64])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    ~spl2_20 | spl2_14 | spl2_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f177,f160,f133,f167])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    spl2_18 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1))) ) | spl2_18),
% 0.20/0.48    inference(resolution,[],[f161,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | spl2_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f160])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    ~spl2_18 | spl2_1 | ~spl2_10 | ~spl2_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f156,f130,f114,f64,f160])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    spl2_10 <=> ! [X0] : (~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    spl2_13 <=> v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | (~spl2_10 | ~spl2_13)),
% 0.20/0.48    inference(resolution,[],[f131,f115])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ( ! [X0] : (~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) ) | ~spl2_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f114])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | ~spl2_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f130])).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    ~spl2_4 | spl2_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f147,f144,f78])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | spl2_16),
% 0.20/0.48    inference(resolution,[],[f145,f46])).
% 0.20/0.48  % (31430)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (31441)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ~m1_pre_topc(sK0,sK0) | spl2_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f144])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    ~spl2_16 | ~spl2_2 | ~spl2_4 | ~spl2_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f141,f127,f78,f67,f144])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    spl2_12 <=> ! [X1] : (~m1_pre_topc(k6_tmap_1(sK0,sK1),X1) | ~l1_pre_topc(X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ~m1_pre_topc(sK0,sK0) | (~spl2_2 | ~spl2_4 | ~spl2_12)),
% 0.20/0.48    inference(resolution,[],[f140,f79])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0)) ) | (~spl2_2 | ~spl2_12)),
% 0.20/0.48    inference(subsumption_resolution,[],[f89,f128])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ( ! [X1] : (~m1_pre_topc(k6_tmap_1(sK0,sK1),X1) | ~l1_pre_topc(X1)) ) | ~spl2_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f127])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    spl2_12 | spl2_13 | spl2_14 | ~spl2_3 | ~spl2_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f124,f119,f74,f133,f130,f127])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    spl2_11 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0)))) | v3_pre_topc(X0,k6_tmap_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | ~m1_pre_topc(k6_tmap_1(sK0,sK1),X1) | ~l1_pre_topc(X1)) ) | (~spl2_3 | ~spl2_11)),
% 0.20/0.48    inference(resolution,[],[f123,f75])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,k6_tmap_1(sK0,X0)) | v3_pre_topc(X0,k6_tmap_1(sK0,X0)) | ~m1_pre_topc(k6_tmap_1(sK0,X0),X2) | ~l1_pre_topc(X2)) ) | ~spl2_11),
% 0.20/0.48    inference(resolution,[],[f122,f49])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_pre_topc(k6_tmap_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,k6_tmap_1(sK0,X0)) | v3_pre_topc(X0,k6_tmap_1(sK0,X0))) ) | ~spl2_11),
% 0.20/0.48    inference(resolution,[],[f120,f51])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0)))) | v3_pre_topc(X0,k6_tmap_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f119])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ~spl2_5 | ~spl2_4 | spl2_11 | spl2_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f117,f86,f119,f78,f82])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(X0,k6_tmap_1(sK0,X0))) ) | spl2_6),
% 0.20/0.48    inference(resolution,[],[f62,f87])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ~v2_struct_0(sK0) | spl2_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f86])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X2,X0] : (v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(X2,k6_tmap_1(X0,X2))) )),
% 0.20/0.48    inference(equality_resolution,[],[f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ~spl2_4 | spl2_10 | ~spl2_2 | ~spl2_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f112,f82,f67,f114,f78])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ( ! [X0] : (~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~l1_pre_topc(sK0) | v3_pre_topc(X0,sK0)) ) | (~spl2_2 | ~spl2_5)),
% 0.20/0.48    inference(forward_demodulation,[],[f111,f71])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(X0,sK0)) ) | (~spl2_2 | ~spl2_5)),
% 0.20/0.48    inference(forward_demodulation,[],[f110,f71])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(X0,sK0)) ) | ~spl2_5),
% 0.20/0.48    inference(resolution,[],[f60,f83])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    v2_pre_topc(sK0) | ~spl2_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f82])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    ~spl2_4 | spl2_9 | ~spl2_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f105,f101,f107,f78])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    spl2_8 <=> ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ( ! [X0] : (u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl2_8),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f104])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ( ! [X0] : (u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_8),
% 0.20/0.48    inference(resolution,[],[f102,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f101])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ~spl2_5 | ~spl2_4 | spl2_8 | spl2_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f98,f86,f101,f78,f82])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)) ) | spl2_6),
% 0.20/0.48    inference(resolution,[],[f55,f87])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | u1_pre_topc(X0) = k5_tmap_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ~spl2_4 | spl2_7 | ~spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f90,f67,f93,f78])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ( ! [X0] : (m1_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X0)) ) | ~spl2_2),
% 0.20/0.48    inference(superposition,[],[f47,f71])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ~spl2_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f86])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f11])).
% 0.20/0.48  fof(f11,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    spl2_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f82])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl2_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f42,f78])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl2_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f43,f74])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl2_1 | spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f44,f67,f64])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ~spl2_1 | ~spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f45,f67,f64])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (31433)------------------------------
% 0.20/0.48  % (31433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31433)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (31433)Memory used [KB]: 10746
% 0.20/0.48  % (31433)Time elapsed: 0.059 s
% 0.20/0.48  % (31433)------------------------------
% 0.20/0.48  % (31433)------------------------------
% 0.20/0.48  % (31440)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (31423)Success in time 0.125 s
%------------------------------------------------------------------------------

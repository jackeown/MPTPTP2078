%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 465 expanded)
%              Number of leaves         :   43 ( 224 expanded)
%              Depth                    :   10
%              Number of atoms          :  640 (1653 expanded)
%              Number of equality atoms :  102 ( 263 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f76,f81,f86,f91,f96,f102,f108,f117,f127,f135,f150,f164,f183,f190,f194,f200,f207,f211,f217,f230,f275,f310,f338,f343,f360,f387,f393,f426,f434,f436,f442])).

fof(f442,plain,
    ( spl2_6
    | ~ spl2_5
    | ~ spl2_4
    | ~ spl2_3
    | ~ spl2_11
    | spl2_2
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f413,f213,f72,f132,f78,f83,f88,f93])).

fof(f93,plain,
    ( spl2_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f88,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f83,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f78,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f132,plain,
    ( spl2_11
  <=> r2_hidden(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f72,plain,
    ( spl2_2
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f213,plain,
    ( spl2_24
  <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f413,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_24 ),
    inference(superposition,[],[f215,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f20])).

% (17810)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f215,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f436,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | spl2_11 ),
    inference(avatar_split_clause,[],[f142,f132,f83,f78,f68])).

fof(f68,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f142,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | spl2_11 ),
    inference(unit_resulting_resolution,[],[f85,f80,f134,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f134,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f80,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f85,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f434,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK0))
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK0))
    | u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK1)
    | k5_tmap_1(sK0,u1_struct_0(sK0)) != u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f426,plain,
    ( spl2_50
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_9
    | ~ spl2_36
    | ~ spl2_39
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f421,f389,f340,f307,f114,f93,f88,f83,f72,f423])).

fof(f423,plain,
    ( spl2_50
  <=> k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f114,plain,
    ( spl2_9
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f307,plain,
    ( spl2_36
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f340,plain,
    ( spl2_39
  <=> l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f389,plain,
    ( spl2_46
  <=> u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f421,plain,
    ( k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_9
    | ~ spl2_36
    | ~ spl2_39
    | ~ spl2_46 ),
    inference(forward_demodulation,[],[f420,f73])).

fof(f73,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f420,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_9
    | ~ spl2_36
    | ~ spl2_39
    | ~ spl2_46 ),
    inference(forward_demodulation,[],[f419,f309])).

fof(f309,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f307])).

fof(f419,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(sK0))
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_9
    | ~ spl2_39
    | ~ spl2_46 ),
    inference(forward_demodulation,[],[f415,f391])).

fof(f391,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f389])).

fof(f415,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))))
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_9
    | ~ spl2_39 ),
    inference(unit_resulting_resolution,[],[f95,f85,f90,f116,f342,f145])).

% (17816)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f145,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k6_tmap_1(X1,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(X1,X0)),u1_pre_topc(k6_tmap_1(X1,X0)))
      | ~ l1_pre_topc(k6_tmap_1(X1,X0)) ) ),
    inference(resolution,[],[f57,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f342,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f340])).

fof(f116,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f90,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f95,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f393,plain,
    ( spl2_46
    | ~ spl2_42
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f392,f384,f355,f389])).

fof(f355,plain,
    ( spl2_42
  <=> k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f384,plain,
    ( spl2_45
  <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f392,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ spl2_42
    | ~ spl2_45 ),
    inference(backward_demodulation,[],[f357,f386])).

fof(f386,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f384])).

fof(f357,plain,
    ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f355])).

fof(f387,plain,
    ( spl2_45
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_9
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f380,f335,f114,f93,f88,f83,f384])).

fof(f335,plain,
    ( spl2_38
  <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f380,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_9
    | ~ spl2_38 ),
    inference(unit_resulting_resolution,[],[f95,f90,f85,f116,f337,f51])).

fof(f337,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f335])).

fof(f360,plain,
    ( spl2_42
    | ~ spl2_9
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f315,f209,f114,f355])).

fof(f209,plain,
    ( spl2_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f315,plain,
    ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ spl2_9
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f116,f210])).

fof(f210,plain,
    ( ! [X0] :
        ( k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f209])).

fof(f343,plain,
    ( spl2_39
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f322,f114,f93,f88,f83,f340])).

fof(f322,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f95,f90,f85,f116,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f338,plain,
    ( spl2_38
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f323,f272,f114,f83,f335])).

fof(f272,plain,
    ( spl2_32
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f323,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_32 ),
    inference(unit_resulting_resolution,[],[f85,f274,f116,f60])).

fof(f274,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f272])).

fof(f310,plain,
    ( ~ spl2_7
    | spl2_36
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f299,f192,f307,f99])).

fof(f99,plain,
    ( spl2_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f192,plain,
    ( spl2_20
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

% (17817)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
fof(f299,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl2_20 ),
    inference(resolution,[],[f193,f111])).

fof(f111,plain,(
    ! [X0] :
      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f65,f56])).

fof(f56,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f193,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f192])).

fof(f275,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | ~ spl2_9
    | spl2_32
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f270,f122,f272,f114,f83,f88])).

fof(f122,plain,
    ( spl2_10
  <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f270,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_10 ),
    inference(superposition,[],[f62,f124])).

fof(f124,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f230,plain,
    ( ~ spl2_26
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | spl2_11 ),
    inference(avatar_split_clause,[],[f224,f132,f93,f88,f83,f78,f227])).

fof(f227,plain,
    ( spl2_26
  <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f224,plain,
    ( u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6
    | spl2_11 ),
    inference(unit_resulting_resolution,[],[f95,f90,f85,f134,f80,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f217,plain,
    ( spl2_24
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f216,f204,f196,f213])).

fof(f196,plain,
    ( spl2_21
  <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f204,plain,
    ( spl2_22
  <=> u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

% (17811)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f216,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(backward_demodulation,[],[f198,f206])).

fof(f206,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f204])).

fof(f198,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f196])).

fof(f211,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_23
    | spl2_6 ),
    inference(avatar_split_clause,[],[f202,f93,f209,f83,f88])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)) )
    | spl2_6 ),
    inference(resolution,[],[f54,f95])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f207,plain,
    ( spl2_22
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f201,f93,f88,f83,f78,f204])).

fof(f201,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f95,f90,f85,f80,f54])).

fof(f200,plain,
    ( spl2_21
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f199,f187,f180,f196])).

fof(f180,plain,
    ( spl2_18
  <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f187,plain,
    ( spl2_19
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f199,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(backward_demodulation,[],[f182,f189])).

fof(f189,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f187])).

fof(f182,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f180])).

fof(f194,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_20
    | spl2_6 ),
    inference(avatar_split_clause,[],[f185,f93,f192,f83,f88])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) )
    | spl2_6 ),
    inference(resolution,[],[f53,f95])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f190,plain,
    ( spl2_19
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f184,f93,f88,f83,f78,f187])).

fof(f184,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f95,f90,f85,f80,f53])).

fof(f183,plain,
    ( ~ spl2_15
    | spl2_18
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f178,f147,f180,f161])).

fof(f161,plain,
    ( spl2_15
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f147,plain,
    ( spl2_13
  <=> v1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f178,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl2_13 ),
    inference(resolution,[],[f149,f55])).

fof(f149,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f164,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f158,f93,f88,f83,f78,f161])).

fof(f158,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f95,f90,f85,f80,f59])).

fof(f150,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f144,f93,f88,f83,f78,f147])).

fof(f144,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f95,f90,f85,f80,f57])).

fof(f135,plain,
    ( ~ spl2_11
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f129,f83,f78,f68,f132])).

fof(f129,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f85,f70,f80,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f127,plain,
    ( ~ spl2_4
    | spl2_10
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f126,f105,f88,f122,f83])).

fof(f105,plain,
    ( spl2_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f126,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f119,f107])).

fof(f107,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl2_5 ),
    inference(resolution,[],[f50,f90])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f117,plain,
    ( spl2_9
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f112,f105,f99,f114])).

fof(f112,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f109,f107])).

fof(f109,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f101,f65])).

fof(f101,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f108,plain,
    ( spl2_8
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f103,f99,f105])).

fof(f103,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f101,f56])).

fof(f102,plain,
    ( spl2_7
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f97,f83,f99])).

fof(f97,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f85,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f96,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f44,f93])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f91,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f46,f83])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f47,f78])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f48,f72,f68])).

fof(f48,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f49,f72,f68])).

fof(f49,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (17814)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.48  % (17814)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (17830)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.49  % (17812)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f445,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f75,f76,f81,f86,f91,f96,f102,f108,f117,f127,f135,f150,f164,f183,f190,f194,f200,f207,f211,f217,f230,f275,f310,f338,f343,f360,f387,f393,f426,f434,f436,f442])).
% 0.21/0.49  fof(f442,plain,(
% 0.21/0.49    spl2_6 | ~spl2_5 | ~spl2_4 | ~spl2_3 | ~spl2_11 | spl2_2 | ~spl2_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f413,f213,f72,f132,f78,f83,f88,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl2_6 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl2_5 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl2_4 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl2_11 <=> r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl2_2 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    spl2_24 <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.49  fof(f413,plain,(
% 0.21/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~r2_hidden(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl2_24),
% 0.21/0.49    inference(superposition,[],[f215,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f20])).
% 0.21/0.49  % (17810)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | ~spl2_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f213])).
% 0.21/0.49  fof(f436,plain,(
% 0.21/0.49    ~spl2_1 | ~spl2_3 | ~spl2_4 | spl2_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f142,f132,f83,f78,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ~v3_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | spl2_11)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f85,f80,f134,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ~r2_hidden(sK1,u1_pre_topc(sK0)) | spl2_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f132])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f434,plain,(
% 0.21/0.49    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK0)) | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK0)) | u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK1) | k5_tmap_1(sK0,u1_struct_0(sK0)) != u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f426,plain,(
% 0.21/0.49    spl2_50 | ~spl2_2 | ~spl2_4 | ~spl2_5 | spl2_6 | ~spl2_9 | ~spl2_36 | ~spl2_39 | ~spl2_46),
% 0.21/0.49    inference(avatar_split_clause,[],[f421,f389,f340,f307,f114,f93,f88,f83,f72,f423])).
% 0.21/0.49  fof(f423,plain,(
% 0.21/0.49    spl2_50 <=> k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl2_9 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    spl2_36 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.21/0.49  fof(f340,plain,(
% 0.21/0.49    spl2_39 <=> l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.21/0.49  fof(f389,plain,(
% 0.21/0.49    spl2_46 <=> u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.21/0.49  fof(f421,plain,(
% 0.21/0.49    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0)) | (~spl2_2 | ~spl2_4 | ~spl2_5 | spl2_6 | ~spl2_9 | ~spl2_36 | ~spl2_39 | ~spl2_46)),
% 0.21/0.49    inference(forward_demodulation,[],[f420,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f420,plain,(
% 0.21/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK0)) | (~spl2_4 | ~spl2_5 | spl2_6 | ~spl2_9 | ~spl2_36 | ~spl2_39 | ~spl2_46)),
% 0.21/0.49    inference(forward_demodulation,[],[f419,f309])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~spl2_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f307])).
% 0.21/0.49  fof(f419,plain,(
% 0.21/0.49    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(sK0)) | (~spl2_4 | ~spl2_5 | spl2_6 | ~spl2_9 | ~spl2_39 | ~spl2_46)),
% 0.21/0.49    inference(forward_demodulation,[],[f415,f391])).
% 0.21/0.49  fof(f391,plain,(
% 0.21/0.49    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~spl2_46),
% 0.21/0.49    inference(avatar_component_clause,[],[f389])).
% 0.21/0.49  fof(f415,plain,(
% 0.21/0.49    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) | (~spl2_4 | ~spl2_5 | spl2_6 | ~spl2_9 | ~spl2_39)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f95,f85,f90,f116,f342,f145])).
% 0.21/0.49  % (17816)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k6_tmap_1(X1,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(X1,X0)),u1_pre_topc(k6_tmap_1(X1,X0))) | ~l1_pre_topc(k6_tmap_1(X1,X0))) )),
% 0.21/0.49    inference(resolution,[],[f57,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.21/0.49  fof(f342,plain,(
% 0.21/0.49    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~spl2_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f340])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f88])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~v2_struct_0(sK0) | spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f393,plain,(
% 0.21/0.49    spl2_46 | ~spl2_42 | ~spl2_45),
% 0.21/0.49    inference(avatar_split_clause,[],[f392,f384,f355,f389])).
% 0.21/0.49  fof(f355,plain,(
% 0.21/0.49    spl2_42 <=> k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.21/0.49  fof(f384,plain,(
% 0.21/0.49    spl2_45 <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.21/0.49  fof(f392,plain,(
% 0.21/0.49    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | (~spl2_42 | ~spl2_45)),
% 0.21/0.49    inference(backward_demodulation,[],[f357,f386])).
% 0.21/0.49  fof(f386,plain,(
% 0.21/0.49    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | ~spl2_45),
% 0.21/0.49    inference(avatar_component_clause,[],[f384])).
% 0.21/0.49  fof(f357,plain,(
% 0.21/0.49    k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~spl2_42),
% 0.21/0.49    inference(avatar_component_clause,[],[f355])).
% 0.21/0.49  fof(f387,plain,(
% 0.21/0.49    spl2_45 | ~spl2_4 | ~spl2_5 | spl2_6 | ~spl2_9 | ~spl2_38),
% 0.21/0.49    inference(avatar_split_clause,[],[f380,f335,f114,f93,f88,f83,f384])).
% 0.21/0.49  fof(f335,plain,(
% 0.21/0.49    spl2_38 <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.21/0.49  fof(f380,plain,(
% 0.21/0.49    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | (~spl2_4 | ~spl2_5 | spl2_6 | ~spl2_9 | ~spl2_38)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f95,f90,f85,f116,f337,f51])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~spl2_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f335])).
% 0.21/0.49  fof(f360,plain,(
% 0.21/0.49    spl2_42 | ~spl2_9 | ~spl2_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f315,f209,f114,f355])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    spl2_23 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | (~spl2_9 | ~spl2_23)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f116,f210])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ( ! [X0] : (k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f209])).
% 0.21/0.49  fof(f343,plain,(
% 0.21/0.49    spl2_39 | ~spl2_4 | ~spl2_5 | spl2_6 | ~spl2_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f322,f114,f93,f88,f83,f340])).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | (~spl2_4 | ~spl2_5 | spl2_6 | ~spl2_9)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f95,f90,f85,f116,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f338,plain,(
% 0.21/0.49    spl2_38 | ~spl2_4 | ~spl2_9 | ~spl2_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f323,f272,f114,f83,f335])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    spl2_32 <=> v3_pre_topc(u1_struct_0(sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | (~spl2_4 | ~spl2_9 | ~spl2_32)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f85,f274,f116,f60])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    v3_pre_topc(u1_struct_0(sK0),sK0) | ~spl2_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f272])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    ~spl2_7 | spl2_36 | ~spl2_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f299,f192,f307,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl2_7 <=> l1_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    spl2_20 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.49  % (17817)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~l1_struct_0(sK0) | ~spl2_20),
% 0.21/0.49    inference(resolution,[],[f193,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(superposition,[],[f65,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))) ) | ~spl2_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f192])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    ~spl2_5 | ~spl2_4 | ~spl2_9 | spl2_32 | ~spl2_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f270,f122,f272,f114,f83,f88])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl2_10 <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    v3_pre_topc(u1_struct_0(sK0),sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_10),
% 0.21/0.49    inference(superposition,[],[f62,f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) | ~spl2_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ~spl2_26 | ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_6 | spl2_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f224,f132,f93,f88,f83,f78,f227])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    spl2_26 <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_6 | spl2_11)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f95,f90,f85,f134,f80,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    spl2_24 | ~spl2_21 | ~spl2_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f216,f204,f196,f213])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    spl2_21 <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    spl2_22 <=> u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.50  % (17811)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | (~spl2_21 | ~spl2_22)),
% 0.21/0.50    inference(backward_demodulation,[],[f198,f206])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) | ~spl2_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f204])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,sK1))) | ~spl2_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f196])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    ~spl2_5 | ~spl2_4 | spl2_23 | spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f202,f93,f209,f83,f88])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0))) ) | spl2_6),
% 0.21/0.50    inference(resolution,[],[f54,f95])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    spl2_22 | ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f201,f93,f88,f83,f78,f204])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_6)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f95,f90,f85,f80,f54])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    spl2_21 | ~spl2_18 | ~spl2_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f199,f187,f180,f196])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    spl2_18 <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    spl2_19 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,sK1))) | (~spl2_18 | ~spl2_19)),
% 0.21/0.50    inference(backward_demodulation,[],[f182,f189])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | ~spl2_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f187])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) | ~spl2_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f180])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ~spl2_5 | ~spl2_4 | spl2_20 | spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f185,f93,f192,f83,f88])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))) ) | spl2_6),
% 0.21/0.50    inference(resolution,[],[f53,f95])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    spl2_19 | ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f184,f93,f88,f83,f78,f187])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_6)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f95,f90,f85,f80,f53])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ~spl2_15 | spl2_18 | ~spl2_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f178,f147,f180,f161])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    spl2_15 <=> l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    spl2_13 <=> v1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~spl2_13),
% 0.21/0.50    inference(resolution,[],[f149,f55])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    v1_pre_topc(k6_tmap_1(sK0,sK1)) | ~spl2_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f147])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    spl2_15 | ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f158,f93,f88,f83,f78,f161])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    l1_pre_topc(k6_tmap_1(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_6)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f95,f90,f85,f80,f59])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl2_13 | ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f144,f93,f88,f83,f78,f147])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    v1_pre_topc(k6_tmap_1(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_6)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f95,f90,f85,f80,f57])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ~spl2_11 | spl2_1 | ~spl2_3 | ~spl2_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f129,f83,f78,f68,f132])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ~r2_hidden(sK1,u1_pre_topc(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f85,f70,f80,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~v3_pre_topc(sK1,sK0) | spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f68])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ~spl2_4 | spl2_10 | ~spl2_5 | ~spl2_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f126,f105,f88,f122,f83])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl2_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | (~spl2_5 | ~spl2_8)),
% 0.21/0.50    inference(forward_demodulation,[],[f119,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f105])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | ~spl2_5),
% 0.21/0.50    inference(resolution,[],[f50,f90])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl2_9 | ~spl2_7 | ~spl2_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f112,f105,f99,f114])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_7 | ~spl2_8)),
% 0.21/0.50    inference(forward_demodulation,[],[f109,f107])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_7),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f101,f65])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    l1_struct_0(sK0) | ~spl2_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f99])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl2_8 | ~spl2_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f103,f99,f105])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_7),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f101,f56])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl2_7 | ~spl2_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f97,f83,f99])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    l1_struct_0(sK0) | ~spl2_4),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f85,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ~spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f93])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl2_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f88])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl2_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f83])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl2_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f78])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl2_1 | spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f72,f68])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f72,f68])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (17814)------------------------------
% 0.21/0.50  % (17814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17814)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (17814)Memory used [KB]: 10874
% 0.21/0.50  % (17814)Time elapsed: 0.065 s
% 0.21/0.50  % (17814)------------------------------
% 0.21/0.50  % (17814)------------------------------
% 0.21/0.50  % (17807)Success in time 0.142 s
%------------------------------------------------------------------------------

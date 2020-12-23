%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 359 expanded)
%              Number of leaves         :   45 ( 171 expanded)
%              Depth                    :    9
%              Number of atoms          :  564 (1317 expanded)
%              Number of equality atoms :   46 ( 146 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (11108)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f442,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f114,f119,f124,f130,f142,f163,f164,f173,f180,f218,f219,f268,f299,f304,f321,f335,f360,f367,f405,f419,f432,f441])).

% (11107)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f441,plain,
    ( ~ spl5_23
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_22
    | spl5_47 ),
    inference(avatar_split_clause,[],[f440,f429,f223,f116,f106,f235])).

fof(f235,plain,
    ( spl5_23
  <=> k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f106,plain,
    ( spl5_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f116,plain,
    ( spl5_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f223,plain,
    ( spl5_22
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f429,plain,
    ( spl5_47
  <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f440,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_22
    | spl5_47 ),
    inference(unit_resulting_resolution,[],[f108,f118,f225,f431,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f431,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | spl5_47 ),
    inference(avatar_component_clause,[],[f429])).

fof(f225,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f223])).

fof(f118,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f108,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f432,plain,
    ( ~ spl5_47
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_22
    | spl5_46 ),
    inference(avatar_split_clause,[],[f427,f402,f223,f116,f111,f106,f429])).

fof(f111,plain,
    ( spl5_6
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f402,plain,
    ( spl5_46
  <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f427,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_22
    | spl5_46 ),
    inference(unit_resulting_resolution,[],[f118,f108,f113,f225,f404,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ v3_tdlat_3(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & v4_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f404,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | spl5_46 ),
    inference(avatar_component_clause,[],[f402])).

fof(f113,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f419,plain,
    ( spl5_23
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f410,f170,f106,f235])).

fof(f170,plain,
    ( spl5_15
  <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f410,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(resolution,[],[f233,f172])).

fof(f172,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f81,f108])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f405,plain,
    ( ~ spl5_46
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_16
    | ~ spl5_22
    | spl5_38
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f385,f356,f332,f223,f177,f116,f106,f402])).

fof(f177,plain,
    ( spl5_16
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f332,plain,
    ( spl5_38
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f356,plain,
    ( spl5_42
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f385,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_16
    | ~ spl5_22
    | spl5_38
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f118,f108,f179,f358,f334,f225,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X1,X0)
                  & r1_xboole_0(X1,X2) )
               => r1_xboole_0(X1,k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

fof(f334,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl5_38 ),
    inference(avatar_component_clause,[],[f332])).

fof(f358,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f356])).

fof(f179,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f367,plain,
    ( spl5_22
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f362,f170,f106,f223])).

fof(f362,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f172,f221])).

fof(f221,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_5 ),
    inference(resolution,[],[f80,f108])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f360,plain,
    ( spl5_42
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f354,f318,f356])).

fof(f318,plain,
    ( spl5_36
  <=> r1_xboole_0(k2_tarski(sK2,sK2),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

% (11113)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f354,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ spl5_36 ),
    inference(resolution,[],[f320,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f320,plain,
    ( r1_xboole_0(k2_tarski(sK2,sK2),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f318])).

% (11117)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f335,plain,
    ( ~ spl5_38
    | ~ spl5_21
    | spl5_33 ),
    inference(avatar_split_clause,[],[f324,f301,f214,f332])).

fof(f214,plain,
    ( spl5_21
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f301,plain,
    ( spl5_33
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f324,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_21
    | spl5_33 ),
    inference(backward_demodulation,[],[f303,f216])).

fof(f216,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f214])).

fof(f303,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_33 ),
    inference(avatar_component_clause,[],[f301])).

fof(f321,plain,
    ( spl5_36
    | spl5_32 ),
    inference(avatar_split_clause,[],[f316,f296,f318])).

fof(f296,plain,
    ( spl5_32
  <=> r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f316,plain,
    ( r1_xboole_0(k2_tarski(sK2,sK2),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | spl5_32 ),
    inference(unit_resulting_resolution,[],[f298,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f62])).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f298,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | spl5_32 ),
    inference(avatar_component_clause,[],[f296])).

fof(f304,plain,
    ( ~ spl5_33
    | spl5_2
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f293,f209,f91,f301])).

fof(f91,plain,
    ( spl5_2
  <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f209,plain,
    ( spl5_20
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f293,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_2
    | ~ spl5_20 ),
    inference(backward_demodulation,[],[f93,f211])).

fof(f211,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f209])).

fof(f93,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f299,plain,
    ( ~ spl5_32
    | ~ spl5_20
    | spl5_27 ),
    inference(avatar_split_clause,[],[f292,f265,f209,f296])).

fof(f265,plain,
    ( spl5_27
  <=> r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f292,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl5_20
    | spl5_27 ),
    inference(backward_demodulation,[],[f267,f211])).

fof(f267,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | spl5_27 ),
    inference(avatar_component_clause,[],[f265])).

fof(f268,plain,
    ( ~ spl5_27
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f262,f121,f116,f111,f106,f101,f96,f86,f265])).

fof(f86,plain,
    ( spl5_1
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f96,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f101,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f121,plain,
    ( spl5_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f262,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f123,f118,f113,f108,f98,f103,f88,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

fof(f88,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f103,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f98,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f123,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f219,plain,
    ( spl5_11
    | spl5_20
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f204,f101,f209,f139])).

fof(f139,plain,
    ( spl5_11
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f204,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f84,f103])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f79,f62])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f218,plain,
    ( spl5_11
    | spl5_21
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f203,f96,f214,f139])).

fof(f203,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f84,f98])).

fof(f180,plain,
    ( spl5_16
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f174,f159,f177])).

fof(f159,plain,
    ( spl5_14
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f174,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f161,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f62])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f161,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f173,plain,
    ( spl5_15
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f167,f154,f170])).

fof(f154,plain,
    ( spl5_13
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f167,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f156,f83])).

fof(f156,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f164,plain,
    ( spl5_13
    | spl5_11
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f152,f101,f139,f154])).

fof(f152,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f78,f103])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f163,plain,
    ( spl5_14
    | spl5_11
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f151,f96,f139,f159])).

fof(f151,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f78,f98])).

fof(f142,plain,
    ( ~ spl5_11
    | spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f137,f127,f121,f139])).

fof(f127,plain,
    ( spl5_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f137,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_8
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f123,f129,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f129,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f130,plain,
    ( spl5_9
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f125,f106,f127])).

fof(f125,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f108,f63])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f124,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f54,f121])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
              & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
            & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
          & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
      & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

fof(f119,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f55,f116])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f114,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f56,f111])).

fof(f56,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f109,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f57,f106])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f58,f101])).

fof(f58,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f99,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f59,f96])).

fof(f59,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f60,f91])).

fof(f60,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f61,f86])).

fof(f61,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:15:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (11106)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (11119)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (11104)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (11110)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (11105)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (11116)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (11109)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (11114)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (11120)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (11111)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (11110)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  % (11108)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  fof(f442,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f114,f119,f124,f130,f142,f163,f164,f173,f180,f218,f219,f268,f299,f304,f321,f335,f360,f367,f405,f419,f432,f441])).
% 0.21/0.49  % (11107)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  fof(f441,plain,(
% 0.21/0.49    ~spl5_23 | ~spl5_5 | ~spl5_7 | ~spl5_22 | spl5_47),
% 0.21/0.49    inference(avatar_split_clause,[],[f440,f429,f223,f116,f106,f235])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    spl5_23 <=> k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl5_5 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl5_7 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    spl5_22 <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.49  fof(f429,plain,(
% 0.21/0.49    spl5_47 <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 0.21/0.49  fof(f440,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | (~spl5_5 | ~spl5_7 | ~spl5_22 | spl5_47)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f108,f118,f225,f431,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.49  fof(f431,plain,(
% 0.21/0.49    ~v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | spl5_47),
% 0.21/0.49    inference(avatar_component_clause,[],[f429])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f223])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl5_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f116])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f106])).
% 0.21/0.49  fof(f432,plain,(
% 0.21/0.49    ~spl5_47 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_22 | spl5_46),
% 0.21/0.49    inference(avatar_split_clause,[],[f427,f402,f223,f116,f111,f106,f429])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    spl5_6 <=> v3_tdlat_3(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.49  fof(f402,plain,(
% 0.21/0.49    spl5_46 <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 0.21/0.49  fof(f427,plain,(
% 0.21/0.49    ~v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | (~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_22 | spl5_46)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f118,f108,f113,f225,f404,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v3_tdlat_3(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(rectify,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.21/0.49  fof(f404,plain,(
% 0.21/0.49    ~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | spl5_46),
% 0.21/0.49    inference(avatar_component_clause,[],[f402])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    v3_tdlat_3(sK0) | ~spl5_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f111])).
% 0.21/0.49  fof(f419,plain,(
% 0.21/0.49    spl5_23 | ~spl5_5 | ~spl5_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f410,f170,f106,f235])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl5_15 <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.49  fof(f410,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | (~spl5_5 | ~spl5_15)),
% 0.21/0.49    inference(resolution,[],[f233,f172])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f170])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))) ) | ~spl5_5),
% 0.21/0.49    inference(resolution,[],[f81,f108])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 0.21/0.49  fof(f405,plain,(
% 0.21/0.49    ~spl5_46 | ~spl5_5 | ~spl5_7 | ~spl5_16 | ~spl5_22 | spl5_38 | ~spl5_42),
% 0.21/0.49    inference(avatar_split_clause,[],[f385,f356,f332,f223,f177,f116,f106,f402])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    spl5_16 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.49  fof(f332,plain,(
% 0.21/0.49    spl5_38 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.21/0.49  fof(f356,plain,(
% 0.21/0.49    spl5_42 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.21/0.49  fof(f385,plain,(
% 0.21/0.49    ~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | (~spl5_5 | ~spl5_7 | ~spl5_16 | ~spl5_22 | spl5_38 | ~spl5_42)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f118,f108,f179,f358,f334,f225,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).
% 0.21/0.49  fof(f334,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | spl5_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f332])).
% 0.21/0.49  fof(f358,plain,(
% 0.21/0.49    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | ~spl5_42),
% 0.21/0.49    inference(avatar_component_clause,[],[f356])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f177])).
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    spl5_22 | ~spl5_5 | ~spl5_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f362,f170,f106,f223])).
% 0.21/0.49  fof(f362,plain,(
% 0.21/0.49    m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_5 | ~spl5_15)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f172,f221])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_5),
% 0.21/0.49    inference(resolution,[],[f80,f108])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.49  fof(f360,plain,(
% 0.21/0.49    spl5_42 | ~spl5_36),
% 0.21/0.49    inference(avatar_split_clause,[],[f354,f318,f356])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    spl5_36 <=> r1_xboole_0(k2_tarski(sK2,sK2),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.49  % (11113)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  fof(f354,plain,(
% 0.21/0.49    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | ~spl5_36),
% 0.21/0.49    inference(resolution,[],[f320,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.49  fof(f320,plain,(
% 0.21/0.49    r1_xboole_0(k2_tarski(sK2,sK2),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | ~spl5_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f318])).
% 0.21/0.49  % (11117)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  fof(f335,plain,(
% 0.21/0.49    ~spl5_38 | ~spl5_21 | spl5_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f324,f301,f214,f332])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    spl5_21 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    spl5_33 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl5_21 | spl5_33)),
% 0.21/0.49    inference(backward_demodulation,[],[f303,f216])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | ~spl5_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f214])).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl5_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f301])).
% 0.21/0.49  fof(f321,plain,(
% 0.21/0.49    spl5_36 | spl5_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f316,f296,f318])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    spl5_32 <=> r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    r1_xboole_0(k2_tarski(sK2,sK2),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | spl5_32),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f298,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f75,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    ~r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | spl5_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f296])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    ~spl5_33 | spl5_2 | ~spl5_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f293,f209,f91,f301])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl5_2 <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    spl5_20 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | (spl5_2 | ~spl5_20)),
% 0.21/0.49    inference(backward_demodulation,[],[f93,f211])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~spl5_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f209])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f91])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    ~spl5_32 | ~spl5_20 | spl5_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f292,f265,f209,f296])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    spl5_27 <=> r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    ~r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | (~spl5_20 | spl5_27)),
% 0.21/0.49    inference(backward_demodulation,[],[f267,f211])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | spl5_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f265])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ~spl5_27 | spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f262,f121,f116,f111,f106,f101,f96,f86,f265])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl5_1 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl5_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl5_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl5_8 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | (spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f123,f118,f113,f108,f98,f103,f88,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v3_tdlat_3(X0) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ~v2_struct_0(sK0) | spl5_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f121])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    spl5_11 | spl5_20 | ~spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f204,f101,f209,f139])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    spl5_11 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_4),
% 0.21/0.49    inference(resolution,[],[f84,f103])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f79,f62])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl5_11 | spl5_21 | ~spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f203,f96,f214,f139])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_3),
% 0.21/0.49    inference(resolution,[],[f84,f98])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    spl5_16 | ~spl5_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f174,f159,f177])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    spl5_14 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_14),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f161,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f76,f62])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl5_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f159])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    spl5_15 | ~spl5_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f167,f154,f170])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl5_13 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_13),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f156,f83])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl5_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f154])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl5_13 | spl5_11 | ~spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f152,f101,f139,f154])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0)) | ~spl5_4),
% 0.21/0.49    inference(resolution,[],[f78,f103])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl5_14 | spl5_11 | ~spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f151,f96,f139,f159])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK2,u1_struct_0(sK0)) | ~spl5_3),
% 0.21/0.49    inference(resolution,[],[f78,f98])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ~spl5_11 | spl5_8 | ~spl5_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f137,f127,f121,f139])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl5_9 <=> l1_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~v1_xboole_0(u1_struct_0(sK0)) | (spl5_8 | ~spl5_9)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f123,f129,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    l1_struct_0(sK0) | ~spl5_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f127])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl5_9 | ~spl5_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f125,f106,f127])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    l1_struct_0(sK0) | ~spl5_5),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f108,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~spl5_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f121])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ((k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f44,f43,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) => (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f16])).
% 0.21/0.49  fof(f16,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl5_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f116])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl5_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f111])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    v3_tdlat_3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl5_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f57,f106])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f101])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f59,f96])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f91])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ~spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f61,f86])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11110)------------------------------
% 0.21/0.49  % (11110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11110)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11110)Memory used [KB]: 6396
% 0.21/0.49  % (11110)Time elapsed: 0.017 s
% 0.21/0.49  % (11110)------------------------------
% 0.21/0.49  % (11110)------------------------------
% 0.21/0.50  % (11102)Success in time 0.134 s
%------------------------------------------------------------------------------

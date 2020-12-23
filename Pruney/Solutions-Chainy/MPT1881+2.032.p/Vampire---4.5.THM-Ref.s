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
% DateTime   : Thu Dec  3 13:21:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 317 expanded)
%              Number of leaves         :   32 ( 120 expanded)
%              Depth                    :   16
%              Number of atoms          :  677 (1120 expanded)
%              Number of equality atoms :   51 (  91 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f102,f107,f116,f124,f145,f151,f163,f181,f196,f212,f213,f223,f229,f233,f242,f247,f248])).

fof(f248,plain,
    ( sK1 != u1_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | sK1 = k2_struct_0(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f247,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_16
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_16
    | spl3_17 ),
    inference(subsumption_resolution,[],[f245,f241])).

fof(f241,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl3_17
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f245,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f215,f161])).

fof(f161,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl3_13
  <=> sK1 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f215,plain,
    ( sK1 != k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f214,f83])).

fof(f83,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f214,plain,
    ( sK1 != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f201,f101])).

fof(f101,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f201,plain,
    ( sK1 != k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ spl3_16 ),
    inference(superposition,[],[f51,f195])).

fof(f195,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl3_16
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f242,plain,
    ( ~ spl3_17
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f232,f178,f148,f109,f81,f76,f71,f66,f239])).

fof(f66,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f71,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f76,plain,
    ( spl3_3
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f109,plain,
    ( spl3_7
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f148,plain,
    ( spl3_12
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f178,plain,
    ( spl3_15
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f232,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f231,f180])).

fof(f180,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f178])).

fof(f231,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7
    | ~ spl3_12 ),
    inference(resolution,[],[f110,f191])).

fof(f191,plain,
    ( ! [X0] :
        ( v3_tex_2(X0,sK0)
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f190,f150])).

fof(f150,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0)
        | v3_tex_2(X0,sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f189,f138])).

fof(f138,plain,
    ( ! [X2] :
        ( v2_tex_2(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f137,f83])).

fof(f137,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X2,sK0) )
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f88,f78])).

fof(f78,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f88,plain,
    ( ! [X2] :
        ( ~ v1_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X2,sK0) )
    | spl3_1 ),
    inference(subsumption_resolution,[],[f87,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f87,plain,
    ( ! [X2] :
        ( ~ v2_pre_topc(sK0)
        | ~ v1_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X2,sK0) )
    | spl3_1 ),
    inference(resolution,[],[f68,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f68,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | v3_tex_2(X0,sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f188,f83])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | v3_tex_2(X0,sK0) )
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f85,f73])).

fof(f73,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | v3_tex_2(X0,sK0) )
    | spl3_1 ),
    inference(resolution,[],[f68,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(f110,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f233,plain,
    ( ~ spl3_14
    | spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f227,f148,f113,f168])).

fof(f168,plain,
    ( spl3_14
  <=> v1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f113,plain,
    ( spl3_8
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f227,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_8
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f115,f150])).

fof(f115,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f229,plain,
    ( spl3_14
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f226,f148,f109,f168])).

fof(f226,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f225,f150])).

fof(f225,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f38,f111])).

fof(f111,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f38,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(f223,plain,
    ( ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f221,f132])).

fof(f132,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_10
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f221,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl3_11 ),
    inference(resolution,[],[f144,f64])).

fof(f64,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f144,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f213,plain,
    ( sK1 != u1_struct_0(sK0)
    | v1_subset_1(sK1,sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f212,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_12
    | spl3_13
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_12
    | spl3_13
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f210,f162])).

fof(f162,plain,
    ( sK1 != k2_struct_0(sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f210,plain,
    ( sK1 = k2_struct_0(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f209,f195])).

fof(f209,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f206,f180])).

fof(f206,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(resolution,[],[f203,f111])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(resolution,[],[f200,f166])).

fof(f166,plain,
    ( ! [X2] :
        ( ~ v1_tops_1(X2,sK0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f95,f150])).

fof(f95,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X2)
        | ~ v1_tops_1(X2,sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f83,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f200,plain,
    ( ! [X1] :
        ( v1_tops_1(X1,sK0)
        | ~ v3_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f199,f150])).

fof(f199,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X1,sK0)
        | v1_tops_1(X1,sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f198,f128])).

fof(f128,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f92,f83])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f90,f73])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f78,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f198,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0)
        | ~ v3_tex_2(X1,sK0)
        | v1_tops_1(X1,sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f197,f83])).

fof(f197,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0)
        | ~ v3_tex_2(X1,sK0)
        | v1_tops_1(X1,sK0) )
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f86,f73])).

fof(f86,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0)
        | ~ v3_tex_2(X1,sK0)
        | v1_tops_1(X1,sK0) )
    | spl3_1 ),
    inference(resolution,[],[f68,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(f196,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f187,f178,f148,f81,f76,f71,f193])).

fof(f187,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(resolution,[],[f184,f180])).

fof(f184,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X1) = X1 )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X1) = X1 )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(resolution,[],[f176,f156])).

fof(f156,plain,
    ( ! [X3] :
        ( ~ v4_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X3) = X3 )
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f96,f150])).

fof(f96,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X3,sK0)
        | k2_pre_topc(sK0,X3) = X3 )
    | ~ spl3_4 ),
    inference(resolution,[],[f83,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f176,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f175,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f174,f150])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(resolution,[],[f158,f128])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f157,f150])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f93,f150])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f83,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f181,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f154,f148,f99,f178])).

fof(f154,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(superposition,[],[f101,f150])).

fof(f163,plain,
    ( ~ spl3_13
    | spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f152,f148,f121,f160])).

fof(f121,plain,
    ( spl3_9
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f152,plain,
    ( sK1 != k2_struct_0(sK0)
    | spl3_9
    | ~ spl3_12 ),
    inference(superposition,[],[f122,f150])).

fof(f122,plain,
    ( sK1 != u1_struct_0(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f151,plain,
    ( spl3_12
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f117,f104,f148])).

fof(f104,plain,
    ( spl3_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f117,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f106,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f106,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f145,plain,
    ( spl3_11
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f126,f121,f99,f142])).

fof(f126,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f101,f123])).

fof(f123,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f124,plain,
    ( spl3_9
    | ~ spl3_5
    | spl3_8 ),
    inference(avatar_split_clause,[],[f119,f113,f99,f121])).

fof(f119,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl3_5
    | spl3_8 ),
    inference(subsumption_resolution,[],[f118,f101])).

fof(f118,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8 ),
    inference(resolution,[],[f115,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f116,plain,
    ( spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f37,f113,f109])).

fof(f37,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f107,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f97,f81,f104])).

fof(f97,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f83,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f102,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f39,f99])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f43,f81])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f42,f76])).

fof(f42,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f41,f71])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f40,f66])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (7129)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (7121)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (7121)Refutation not found, incomplete strategy% (7121)------------------------------
% 0.21/0.46  % (7121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (7121)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (7121)Memory used [KB]: 6012
% 0.21/0.46  % (7121)Time elapsed: 0.004 s
% 0.21/0.46  % (7121)------------------------------
% 0.21/0.46  % (7121)------------------------------
% 0.21/0.47  % (7129)Refutation not found, incomplete strategy% (7129)------------------------------
% 0.21/0.47  % (7129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (7129)Memory used [KB]: 10618
% 0.21/0.47  % (7129)Time elapsed: 0.056 s
% 0.21/0.47  % (7129)------------------------------
% 0.21/0.47  % (7129)------------------------------
% 0.21/0.48  % (7112)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (7126)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (7112)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f102,f107,f116,f124,f145,f151,f163,f181,f196,f212,f213,f223,f229,f233,f242,f247,f248])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    sK1 != u1_struct_0(sK0) | u1_struct_0(sK0) != k2_struct_0(sK0) | sK1 = k2_struct_0(sK0)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    ~spl3_4 | ~spl3_5 | ~spl3_13 | ~spl3_16 | spl3_17),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f246])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    $false | (~spl3_4 | ~spl3_5 | ~spl3_13 | ~spl3_16 | spl3_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f245,f241])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    ~v1_tops_1(sK1,sK0) | spl3_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f239])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    spl3_17 <=> v1_tops_1(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    v1_tops_1(sK1,sK0) | (~spl3_4 | ~spl3_5 | ~spl3_13 | ~spl3_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f215,f161])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    sK1 = k2_struct_0(sK0) | ~spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f160])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    spl3_13 <=> sK1 = k2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    sK1 != k2_struct_0(sK0) | v1_tops_1(sK1,sK0) | (~spl3_4 | ~spl3_5 | ~spl3_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f214,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    sK1 != k2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0) | (~spl3_5 | ~spl3_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f201,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    sK1 != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0) | ~spl3_16),
% 0.21/0.48    inference(superposition,[],[f51,f195])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f193])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    spl3_16 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    ~spl3_17 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_7 | ~spl3_12 | ~spl3_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f232,f178,f148,f109,f81,f76,f71,f66,f239])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl3_1 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl3_2 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl3_3 <=> v1_tdlat_3(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl3_7 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    spl3_12 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    spl3_15 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~v1_tops_1(sK1,sK0) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_7 | ~spl3_12 | ~spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f231,f180])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f178])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    ~v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_7 | ~spl3_12)),
% 0.21/0.48    inference(resolution,[],[f110,f191])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ( ! [X0] : (v3_tex_2(X0,sK0) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f190,f150])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f148])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | v3_tex_2(X0,sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f189,f138])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ( ! [X2] : (v2_tex_2(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl3_1 | ~spl3_3 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f137,f83])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X2] : (~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X2,sK0)) ) | (spl3_1 | ~spl3_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f88,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    v1_tdlat_3(sK0) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X2] : (~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X2,sK0)) ) | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X2] : (~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X2,sK0)) ) | spl3_1),
% 0.21/0.48    inference(resolution,[],[f68,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f66])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f188,f83])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) ) | (spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    v2_pre_topc(sK0) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) ) | spl3_1),
% 0.21/0.48    inference(resolution,[],[f68,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ~v3_tex_2(sK1,sK0) | spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f109])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ~spl3_14 | spl3_8 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f227,f148,f113,f168])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    spl3_14 <=> v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl3_8 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ~v1_subset_1(sK1,k2_struct_0(sK0)) | (spl3_8 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f115,f150])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f113])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    spl3_14 | ~spl3_7 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f226,f148,f109,f168])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    v1_subset_1(sK1,k2_struct_0(sK0)) | (~spl3_7 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f225,f150])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_7),
% 0.21/0.48    inference(subsumption_resolution,[],[f38,f111])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    v3_tex_2(sK1,sK0) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f109])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f15])).
% 0.21/0.48  fof(f15,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    ~spl3_10 | ~spl3_11),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f222])).
% 0.21/0.48  fof(f222,plain,(
% 0.21/0.48    $false | (~spl3_10 | ~spl3_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f221,f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    v1_subset_1(sK1,sK1) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl3_10 <=> v1_subset_1(sK1,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    ~v1_subset_1(sK1,sK1) | ~spl3_11),
% 0.21/0.48    inference(resolution,[],[f144,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f142])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    spl3_11 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    sK1 != u1_struct_0(sK0) | v1_subset_1(sK1,sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_12 | spl3_13 | ~spl3_15 | ~spl3_16),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_12 | spl3_13 | ~spl3_15 | ~spl3_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f210,f162])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    sK1 != k2_struct_0(sK0) | spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f160])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    sK1 = k2_struct_0(sK0) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_12 | ~spl3_15 | ~spl3_16)),
% 0.21/0.48    inference(forward_demodulation,[],[f209,f195])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_12 | ~spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f206,f180])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_12)),
% 0.21/0.48    inference(resolution,[],[f203,f111])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f202])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(resolution,[],[f200,f166])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    ( ! [X2] : (~v1_tops_1(X2,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f95,f150])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X2) | ~v1_tops_1(X2,sK0)) ) | ~spl3_4),
% 0.21/0.48    inference(resolution,[],[f83,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    ( ! [X1] : (v1_tops_1(X1,sK0) | ~v3_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f199,f150])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X1,sK0) | v1_tops_1(X1,sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f198,f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f92,f83])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) ) | (~spl3_2 | ~spl3_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f90,f73])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) ) | ~spl3_3),
% 0.21/0.48    inference(resolution,[],[f78,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v3_tex_2(X1,sK0) | v1_tops_1(X1,sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f197,f83])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v3_tex_2(X1,sK0) | v1_tops_1(X1,sK0)) ) | (spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f86,f73])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v3_tex_2(X1,sK0) | v1_tops_1(X1,sK0)) ) | spl3_1),
% 0.21/0.48    inference(resolution,[],[f68,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    spl3_16 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12 | ~spl3_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f187,f178,f148,f81,f76,f71,f193])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    sK1 = k2_pre_topc(sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12 | ~spl3_15)),
% 0.21/0.48    inference(resolution,[],[f184,f180])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X1) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f183])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X1) = X1) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(resolution,[],[f176,f156])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ( ! [X3] : (~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X3) = X3) ) | (~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f96,f150])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X3,sK0) | k2_pre_topc(sK0,X3) = X3) ) | ~spl3_4),
% 0.21/0.48    inference(resolution,[],[f83,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ( ! [X0] : (v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f175,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f174,f150])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(resolution,[],[f158,f128])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f157,f150])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0)) ) | (~spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f93,f150])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0)) ) | ~spl3_4),
% 0.21/0.48    inference(resolution,[],[f83,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    spl3_15 | ~spl3_5 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f154,f148,f99,f178])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_5 | ~spl3_12)),
% 0.21/0.48    inference(superposition,[],[f101,f150])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ~spl3_13 | spl3_9 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f152,f148,f121,f160])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl3_9 <=> sK1 = u1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    sK1 != k2_struct_0(sK0) | (spl3_9 | ~spl3_12)),
% 0.21/0.48    inference(superposition,[],[f122,f150])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    sK1 != u1_struct_0(sK0) | spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f121])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    spl3_12 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f117,f104,f148])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl3_6 <=> l1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_6),
% 0.21/0.48    inference(resolution,[],[f106,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    l1_struct_0(sK0) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    spl3_11 | ~spl3_5 | ~spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f126,f121,f99,f142])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl3_5 | ~spl3_9)),
% 0.21/0.48    inference(superposition,[],[f101,f123])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK0) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f121])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl3_9 | ~spl3_5 | spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f119,f113,f99,f121])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK0) | (~spl3_5 | spl3_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f101])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_8),
% 0.21/0.48    inference(resolution,[],[f115,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl3_7 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f113,f109])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl3_6 | ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f97,f81,f104])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    l1_struct_0(sK0) | ~spl3_4),
% 0.21/0.48    inference(resolution,[],[f83,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f99])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f81])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f76])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    v1_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f71])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f66])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (7112)------------------------------
% 0.21/0.48  % (7112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7112)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (7112)Memory used [KB]: 10746
% 0.21/0.48  % (7112)Time elapsed: 0.074 s
% 0.21/0.48  % (7112)------------------------------
% 0.21/0.48  % (7112)------------------------------
% 0.21/0.48  % (7108)Success in time 0.126 s
%------------------------------------------------------------------------------

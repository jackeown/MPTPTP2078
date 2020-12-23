%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 382 expanded)
%              Number of leaves         :   35 ( 167 expanded)
%              Depth                    :   12
%              Number of atoms          :  792 (2092 expanded)
%              Number of equality atoms :   18 (  94 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f77,f81,f85,f89,f93,f97,f101,f111,f133,f142,f143,f153,f161,f171,f176,f183,f186,f189,f190,f195,f197,f205,f208,f210])).

% (865)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f210,plain,
    ( spl3_8
    | ~ spl3_5
    | spl3_4
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f209,f115,f79,f83,f87,f99])).

fof(f99,plain,
    ( spl3_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f87,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f83,plain,
    ( spl3_4
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f79,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f115,plain,
    ( spl3_10
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f209,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f116,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f116,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f208,plain,
    ( spl3_4
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | spl3_8
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f207,f203,f99,f95,f91,f87,f79,f83])).

fof(f91,plain,
    ( spl3_6
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f95,plain,
    ( spl3_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f203,plain,
    ( spl3_23
  <=> ! [X1] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v2_tdlat_3(X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f207,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ spl3_23 ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_23 ),
    inference(resolution,[],[f204,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f204,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v2_tdlat_3(X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f203])).

fof(f205,plain,
    ( spl3_23
    | spl3_10
    | spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f199,f148,f128,f115,f203])).

fof(f128,plain,
    ( spl3_14
  <=> v7_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f148,plain,
    ( spl3_16
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f199,plain,
    ( ! [X1] :
        ( v7_struct_0(sK2(sK0,sK1))
        | v2_struct_0(sK2(sK0,sK1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_tdlat_3(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl3_16 ),
    inference(resolution,[],[f149,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => ( v7_struct_0(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc31_tex_2)).

fof(f149,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f197,plain,
    ( spl3_8
    | ~ spl3_5
    | spl3_4
    | ~ spl3_3
    | spl3_22 ),
    inference(avatar_split_clause,[],[f196,f193,f79,f83,f87,f99])).

fof(f193,plain,
    ( spl3_22
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f196,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_22 ),
    inference(resolution,[],[f194,f61])).

fof(f194,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f193])).

fof(f195,plain,
    ( ~ spl3_3
    | ~ spl3_22
    | ~ spl3_5
    | spl3_8
    | ~ spl3_1
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f191,f151,f69,f99,f87,f193,f79])).

fof(f69,plain,
    ( spl3_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f151,plain,
    ( spl3_17
  <=> ! [X0] :
        ( ~ v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f191,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_17 ),
    inference(resolution,[],[f75,f152])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f75,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f190,plain,
    ( ~ spl3_15
    | spl3_2
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f145,f128,f109,f72,f131])).

fof(f131,plain,
    ( spl3_15
  <=> l1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f72,plain,
    ( spl3_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f109,plain,
    ( spl3_9
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f145,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f144,f110])).

fof(f110,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f144,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl3_14 ),
    inference(resolution,[],[f129,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f129,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f128])).

fof(f189,plain,
    ( spl3_4
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_8
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f188,f159,f99,f87,f79,f69,f83])).

fof(f159,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_tex_2(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f188,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ spl3_18 ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_18 ),
    inference(resolution,[],[f160,f61])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_tex_2(sK1,X0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f159])).

fof(f186,plain,
    ( spl3_4
    | ~ spl3_3
    | ~ spl3_5
    | spl3_8
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f185,f166,f99,f87,f79,f83])).

fof(f166,plain,
    ( spl3_19
  <=> ! [X1] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f185,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ spl3_19 ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_19 ),
    inference(resolution,[],[f167,f61])).

fof(f167,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f166])).

fof(f183,plain,
    ( spl3_4
    | ~ spl3_3
    | spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_21 ),
    inference(avatar_split_clause,[],[f180,f174,f87,f91,f95,f99,f79,f83])).

fof(f174,plain,
    ( spl3_21
  <=> v2_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f180,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | spl3_21 ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_21 ),
    inference(resolution,[],[f178,f61])).

fof(f178,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_tdlat_3(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl3_21 ),
    inference(resolution,[],[f175,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f175,plain,
    ( ~ v2_tdlat_3(sK2(sK0,sK1))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f174])).

fof(f176,plain,
    ( spl3_19
    | ~ spl3_21
    | spl3_20 ),
    inference(avatar_split_clause,[],[f172,f169,f174,f166])).

fof(f169,plain,
    ( spl3_20
  <=> v2_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ v2_tdlat_3(sK2(sK0,sK1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl3_20 ),
    inference(resolution,[],[f170,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v2_tdlat_3(X1)
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc15_tex_2)).

fof(f170,plain,
    ( ~ v2_pre_topc(sK2(sK0,sK1))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f169])).

fof(f171,plain,
    ( spl3_19
    | ~ spl3_20
    | spl3_10
    | spl3_18
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f164,f128,f109,f159,f115,f169,f166])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK2(sK0,sK1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f163,f110])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK2(sK0,sK1))
        | v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f162,f110])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK2(sK0,sK1))
        | v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl3_14 ),
    inference(resolution,[],[f136,f129])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X0)
      | v2_tex_2(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(X0,X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(u1_struct_0(X0),X1)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f66,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v2_tdlat_3(X1)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f161,plain,
    ( spl3_10
    | spl3_18
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f157,f148,f109,f159,f115])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_tex_2(sK1,X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f156,f110])).

fof(f156,plain,
    ( ! [X0] :
        ( v2_tex_2(sK1,X0)
        | ~ m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f154,f110])).

fof(f154,plain,
    ( ! [X0] :
        ( v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0)
        | ~ m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_16 ),
    inference(resolution,[],[f149,f66])).

fof(f153,plain,
    ( spl3_10
    | spl3_16
    | spl3_17
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f146,f109,f151,f148,f115])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(sK1,X0)
        | v1_tdlat_3(sK2(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_9 ),
    inference(superposition,[],[f67,f110])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(u1_struct_0(X1),X0)
      | v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f143,plain,
    ( ~ spl3_11
    | spl3_15 ),
    inference(avatar_split_clause,[],[f137,f131,f118])).

fof(f118,plain,
    ( spl3_11
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f137,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_15 ),
    inference(resolution,[],[f132,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f132,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f142,plain,
    ( spl3_8
    | spl3_4
    | ~ spl3_3
    | ~ spl3_5
    | spl3_11 ),
    inference(avatar_split_clause,[],[f139,f118,f87,f79,f83,f99])).

fof(f139,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | spl3_11 ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_11 ),
    inference(resolution,[],[f134,f61])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl3_11 ),
    inference(resolution,[],[f119,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f119,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f133,plain,
    ( spl3_14
    | ~ spl3_15
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f113,f109,f72,f131,f128])).

fof(f113,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ spl3_9 ),
    inference(superposition,[],[f52,f110])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f111,plain,
    ( spl3_8
    | ~ spl3_5
    | spl3_9
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f105,f83,f79,f109,f87,f99])).

fof(f105,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3
    | spl3_4 ),
    inference(resolution,[],[f104,f80])).

fof(f80,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | sK1 = u1_struct_0(sK2(X0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl3_4 ),
    inference(resolution,[],[f62,f84])).

fof(f84,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK2(X0,X1)) = X1
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f42,f99])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f97,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f43,f95])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f45,f87])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f46,f83])).

fof(f46,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f47,f79])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f48,f72,f69])).

fof(f48,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f49,f72,f69])).

fof(f49,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (868)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (860)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (859)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (858)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (857)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (867)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (858)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (866)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f74,f77,f81,f85,f89,f93,f97,f101,f111,f133,f142,f143,f153,f161,f171,f176,f183,f186,f189,f190,f195,f197,f205,f208,f210])).
% 0.22/0.52  % (865)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    spl3_8 | ~spl3_5 | spl3_4 | ~spl3_3 | ~spl3_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f209,f115,f79,f83,f87,f99])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    spl3_8 <=> v2_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl3_5 <=> l1_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    spl3_4 <=> v1_xboole_0(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    spl3_10 <=> v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.52  fof(f209,plain,(
% 0.22/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_10),
% 0.22/0.52    inference(resolution,[],[f116,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    v2_struct_0(sK2(sK0,sK1)) | ~spl3_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f115])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    spl3_4 | ~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | spl3_8 | ~spl3_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f207,f203,f99,f95,f91,f87,f79,f83])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    spl3_6 <=> v2_tdlat_3(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl3_7 <=> v2_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    spl3_23 <=> ! [X1] : (~m1_pre_topc(sK2(sK0,sK1),X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~v2_tdlat_3(X1) | ~l1_pre_topc(X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.52  fof(f207,plain,(
% 0.22/0.52    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~spl3_23),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f206])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_23),
% 0.22/0.52    inference(resolution,[],[f204,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f40])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    ( ! [X1] : (~m1_pre_topc(sK2(sK0,sK1),X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~v2_tdlat_3(X1) | ~l1_pre_topc(X1)) ) | ~spl3_23),
% 0.22/0.52    inference(avatar_component_clause,[],[f203])).
% 0.22/0.52  fof(f205,plain,(
% 0.22/0.52    spl3_23 | spl3_10 | spl3_14 | ~spl3_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f199,f148,f128,f115,f203])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    spl3_14 <=> v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    spl3_16 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    ( ! [X1] : (v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X1) | ~l1_pre_topc(X1) | ~v2_tdlat_3(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl3_16),
% 0.22/0.52    inference(resolution,[],[f149,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v7_struct_0(X1) & ~v2_struct_0(X1)) | ~v1_tdlat_3(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v7_struct_0(X1) & ~v2_struct_0(X1)) | (~v1_tdlat_3(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v1_tdlat_3(X1) & ~v2_struct_0(X1)) => (v7_struct_0(X1) & ~v2_struct_0(X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc31_tex_2)).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    v1_tdlat_3(sK2(sK0,sK1)) | ~spl3_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f148])).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    spl3_8 | ~spl3_5 | spl3_4 | ~spl3_3 | spl3_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f196,f193,f79,f83,f87,f99])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    spl3_22 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_22),
% 0.22/0.52    inference(resolution,[],[f194,f61])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ~m1_pre_topc(sK2(sK0,sK1),sK0) | spl3_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f193])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    ~spl3_3 | ~spl3_22 | ~spl3_5 | spl3_8 | ~spl3_1 | ~spl3_17),
% 0.22/0.52    inference(avatar_split_clause,[],[f191,f151,f69,f99,f87,f193,f79])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl3_1 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    spl3_17 <=> ! [X0] : (~v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_17)),
% 0.22/0.52    inference(resolution,[],[f75,f152])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f151])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    v2_tex_2(sK1,sK0) | ~spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f69])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    ~spl3_15 | spl3_2 | ~spl3_9 | ~spl3_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f145,f128,f109,f72,f131])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    spl3_15 <=> l1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    spl3_2 <=> v1_zfmisc_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    spl3_9 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | (~spl3_9 | ~spl3_14)),
% 0.22/0.52    inference(forward_demodulation,[],[f144,f110])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl3_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f109])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | ~spl3_14),
% 0.22/0.52    inference(resolution,[],[f129,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    v7_struct_0(sK2(sK0,sK1)) | ~spl3_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f128])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    spl3_4 | spl3_1 | ~spl3_3 | ~spl3_5 | spl3_8 | ~spl3_18),
% 0.22/0.52    inference(avatar_split_clause,[],[f188,f159,f99,f87,f79,f69,f83])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    spl3_18 <=> ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_tex_2(sK1,X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | ~spl3_18),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f187])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_18),
% 0.22/0.52    inference(resolution,[],[f160,f61])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(sK1,X0)) ) | ~spl3_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f159])).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    spl3_4 | ~spl3_3 | ~spl3_5 | spl3_8 | ~spl3_19),
% 0.22/0.52    inference(avatar_split_clause,[],[f185,f166,f99,f87,f79,f83])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    spl3_19 <=> ! [X1] : (~m1_pre_topc(sK2(sK0,sK1),X1) | v2_struct_0(X1) | ~l1_pre_topc(X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~spl3_19),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f184])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_19),
% 0.22/0.52    inference(resolution,[],[f167,f61])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    ( ! [X1] : (~m1_pre_topc(sK2(sK0,sK1),X1) | v2_struct_0(X1) | ~l1_pre_topc(X1)) ) | ~spl3_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f166])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    spl3_4 | ~spl3_3 | spl3_8 | ~spl3_7 | ~spl3_6 | ~spl3_5 | spl3_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f180,f174,f87,f91,f95,f99,f79,f83])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    spl3_21 <=> v2_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | spl3_21),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f179])).
% 0.22/0.52  fof(f179,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_21),
% 0.22/0.52    inference(resolution,[],[f178,f61])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    ( ! [X1] : (~m1_pre_topc(sK2(sK0,sK1),X1) | ~l1_pre_topc(X1) | ~v2_tdlat_3(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | spl3_21),
% 0.22/0.52    inference(resolution,[],[f175,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    ~v2_tdlat_3(sK2(sK0,sK1)) | spl3_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f174])).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    spl3_19 | ~spl3_21 | spl3_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f172,f169,f174,f166])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    spl3_20 <=> v2_pre_topc(sK2(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_tdlat_3(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | spl3_20),
% 0.22/0.52    inference(resolution,[],[f170,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_pre_topc(X1) | ~v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v2_pre_topc(X1) | ~v2_tdlat_3(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v2_tdlat_3(X1) => v2_pre_topc(X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc15_tex_2)).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    ~v2_pre_topc(sK2(sK0,sK1)) | spl3_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f169])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    spl3_19 | ~spl3_20 | spl3_10 | spl3_18 | ~spl3_9 | ~spl3_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f164,f128,f109,f159,f115,f169,f166])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_tex_2(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X1) | ~l1_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl3_9 | ~spl3_14)),
% 0.22/0.52    inference(forward_demodulation,[],[f163,f110])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK2(sK0,sK1)) | v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0) | ~m1_pre_topc(sK2(sK0,sK1),X1) | ~l1_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl3_9 | ~spl3_14)),
% 0.22/0.52    inference(forward_demodulation,[],[f162,f110])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK2(sK0,sK1)) | v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0) | ~m1_pre_topc(sK2(sK0,sK1),X1) | ~l1_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl3_14),
% 0.22/0.52    inference(resolution,[],[f136,f129])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v7_struct_0(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(X0) | v2_tex_2(u1_struct_0(X0),X1) | ~m1_pre_topc(X0,X2) | ~l1_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f135])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v2_tex_2(u1_struct_0(X0),X1) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | ~m1_pre_topc(X0,X2) | ~l1_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.22/0.52    inference(resolution,[],[f66,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    spl3_10 | spl3_18 | ~spl3_9 | ~spl3_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f157,f148,f109,f159,f115])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(sK1,X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl3_9 | ~spl3_16)),
% 0.22/0.52    inference(forward_demodulation,[],[f156,f110])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ( ! [X0] : (v2_tex_2(sK1,X0) | ~m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl3_9 | ~spl3_16)),
% 0.22/0.52    inference(forward_demodulation,[],[f154,f110])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    ( ! [X0] : (v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0) | ~m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_16),
% 0.22/0.52    inference(resolution,[],[f149,f66])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    spl3_10 | spl3_16 | spl3_17 | ~spl3_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f146,f109,f151,f148,f115])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_tex_2(sK1,X0) | v1_tdlat_3(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_9),
% 0.22/0.52    inference(superposition,[],[f67,f110])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_tex_2(u1_struct_0(X1),X0) | v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ~spl3_11 | spl3_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f137,f131,f118])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    spl3_11 <=> l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ~l1_pre_topc(sK2(sK0,sK1)) | spl3_15),
% 0.22/0.52    inference(resolution,[],[f132,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    ~l1_struct_0(sK2(sK0,sK1)) | spl3_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f131])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    spl3_8 | spl3_4 | ~spl3_3 | ~spl3_5 | spl3_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f139,f118,f87,f79,f83,f99])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | v2_struct_0(sK0) | spl3_11),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_11),
% 0.22/0.52    inference(resolution,[],[f134,f61])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | spl3_11),
% 0.22/0.52    inference(resolution,[],[f119,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ~l1_pre_topc(sK2(sK0,sK1)) | spl3_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f118])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    spl3_14 | ~spl3_15 | ~spl3_2 | ~spl3_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f113,f109,f72,f131,f128])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ~v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~spl3_9),
% 0.22/0.52    inference(superposition,[],[f52,f110])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    spl3_8 | ~spl3_5 | spl3_9 | ~spl3_3 | spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f105,f83,f79,f109,f87,f99])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_3 | spl3_4)),
% 0.22/0.52    inference(resolution,[],[f104,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f79])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | sK1 = u1_struct_0(sK2(X0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | spl3_4),
% 0.22/0.52    inference(resolution,[],[f62,f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ~v1_xboole_0(sK1) | spl3_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f83])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1 | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f40])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ~spl3_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f42,f99])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl3_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f43,f95])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    spl3_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f44,f91])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    v2_tdlat_3(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f45,f87])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f46,f83])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ~v1_xboole_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f47,f79])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl3_1 | spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f48,f72,f69])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ~spl3_1 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f49,f72,f69])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (858)------------------------------
% 0.22/0.53  % (858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (858)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (858)Memory used [KB]: 10746
% 0.22/0.53  % (858)Time elapsed: 0.062 s
% 0.22/0.53  % (858)------------------------------
% 0.22/0.53  % (858)------------------------------
% 0.22/0.53  % (851)Success in time 0.158 s
%------------------------------------------------------------------------------

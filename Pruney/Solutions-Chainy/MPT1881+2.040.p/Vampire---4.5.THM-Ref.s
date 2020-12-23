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
% DateTime   : Thu Dec  3 13:21:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 398 expanded)
%              Number of leaves         :   41 ( 181 expanded)
%              Depth                    :   11
%              Number of atoms          :  772 (1644 expanded)
%              Number of equality atoms :   53 ( 131 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f326,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f83,f87,f91,f95,f99,f103,f109,f116,f120,f137,f149,f158,f172,f178,f187,f190,f218,f269,f279,f284,f290,f298,f300,f305,f307,f325])).

fof(f325,plain,
    ( spl3_27
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f323,f170,f114,f251])).

fof(f251,plain,
    ( spl3_27
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f114,plain,
    ( spl3_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f170,plain,
    ( spl3_17
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0
        | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f323,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(resolution,[],[f322,f115])).

fof(f115,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl3_17 ),
    inference(duplicate_literal_removal,[],[f319])).

fof(f319,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_17 ),
    inference(resolution,[],[f171,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f307,plain,
    ( ~ spl3_4
    | spl3_11 ),
    inference(avatar_split_clause,[],[f306,f122,f89])).

fof(f89,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f122,plain,
    ( spl3_11
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f306,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_11 ),
    inference(resolution,[],[f123,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f123,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f305,plain,
    ( ~ spl3_4
    | spl3_21
    | ~ spl3_9
    | ~ spl3_8
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f304,f185,f107,f114,f195,f89])).

fof(f195,plain,
    ( spl3_21
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f107,plain,
    ( spl3_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f185,plain,
    ( spl3_20
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f304,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f303,f108])).

fof(f108,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f303,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f272,f108])).

fof(f272,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_20 ),
    inference(resolution,[],[f186,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f186,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f185])).

fof(f300,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | sK1 = k2_struct_0(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f298,plain,
    ( spl3_23
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f297,f134,f107,f78,f203])).

fof(f203,plain,
    ( spl3_23
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f78,plain,
    ( spl3_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f134,plain,
    ( spl3_13
  <=> sK1 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f297,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f296,f135])).

fof(f135,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f296,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f79,f108])).

fof(f79,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f290,plain,
    ( ~ spl3_11
    | ~ spl3_23
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f220,f134,f107,f203,f122])).

fof(f220,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f219,f135])).

fof(f219,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f214,f108])).

fof(f214,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl3_13 ),
    inference(superposition,[],[f55,f135])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f284,plain,
    ( spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_8
    | ~ spl3_13
    | spl3_29 ),
    inference(avatar_split_clause,[],[f283,f277,f134,f107,f216,f89,f93,f97,f101])).

fof(f101,plain,
    ( spl3_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f97,plain,
    ( spl3_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f93,plain,
    ( spl3_5
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f216,plain,
    ( spl3_24
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f277,plain,
    ( spl3_29
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f283,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_8
    | ~ spl3_13
    | spl3_29 ),
    inference(forward_demodulation,[],[f282,f135])).

fof(f282,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_8
    | spl3_29 ),
    inference(forward_demodulation,[],[f281,f108])).

fof(f281,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_29 ),
    inference(resolution,[],[f278,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f278,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f277])).

fof(f279,plain,
    ( spl3_7
    | ~ spl3_6
    | ~ spl3_4
    | spl3_1
    | ~ spl3_29
    | ~ spl3_24
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f274,f185,f134,f107,f216,f277,f75,f89,f97,f101])).

fof(f75,plain,
    ( spl3_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f274,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f273,f135])).

fof(f273,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_8
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f271,f108])).

fof(f271,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_20 ),
    inference(resolution,[],[f186,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
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
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(f269,plain,
    ( ~ spl3_4
    | spl3_20
    | ~ spl3_24
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f268,f251,f134,f107,f216,f185,f89])).

fof(f268,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f267,f135])).

fof(f267,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f266,f108])).

fof(f266,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(trivial_inequality_removal,[],[f265])).

fof(f265,plain,
    ( sK1 != sK1
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f264,f135])).

fof(f264,plain,
    ( sK1 != k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_8
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f255,f108])).

fof(f255,plain,
    ( u1_struct_0(sK0) != sK1
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_27 ),
    inference(superposition,[],[f61,f252])).

fof(f252,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f251])).

fof(f61,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f218,plain,
    ( spl3_24
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f213,f134,f114,f216])).

fof(f213,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(superposition,[],[f115,f135])).

fof(f190,plain,
    ( ~ spl3_6
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_8
    | spl3_19 ),
    inference(avatar_split_clause,[],[f189,f182,f107,f114,f93,f89,f97])).

fof(f182,plain,
    ( spl3_19
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f189,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_8
    | spl3_19 ),
    inference(forward_demodulation,[],[f188,f108])).

fof(f188,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_19 ),
    inference(resolution,[],[f183,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f183,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f187,plain,
    ( ~ spl3_9
    | ~ spl3_19
    | spl3_20
    | ~ spl3_1
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f179,f176,f75,f185,f182,f114])).

fof(f176,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v1_tops_1(X0,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f179,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_18 ),
    inference(resolution,[],[f177,f81])).

fof(f81,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK0)
        | v1_tops_1(X0,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( ~ spl3_6
    | ~ spl3_4
    | spl3_18
    | spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f174,f107,f101,f176,f89,f97])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v1_tops_1(X0,sK0) )
    | spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f173,f108])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v1_tops_1(X0,sK0) )
    | spl3_7 ),
    inference(resolution,[],[f63,f102])).

fof(f102,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
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
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(f172,plain,
    ( ~ spl3_4
    | spl3_17
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f168,f156,f107,f170,f89])).

fof(f156,plain,
    ( spl3_15
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f166,f108])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_15 ),
    inference(resolution,[],[f160,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
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

fof(f160,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_15 ),
    inference(superposition,[],[f157,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f157,plain,
    ( ! [X0] :
        ( v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( ~ spl3_6
    | ~ spl3_4
    | ~ spl3_5
    | spl3_15
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f152,f147,f107,f156,f93,f89,f97])).

fof(f147,plain,
    ( spl3_14
  <=> ! [X0] :
        ( v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ v1_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f150,f108])).

fof(f150,plain,
    ( ! [X0] :
        ( v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_14 ),
    inference(resolution,[],[f148,f65])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( ~ spl3_4
    | spl3_14
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f144,f107,f97,f147,f89])).

fof(f144,plain,
    ( ! [X0] :
        ( v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f143,f108])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f142,f108])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) )
    | ~ spl3_6 ),
    inference(resolution,[],[f72,f98])).

fof(f98,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_tops_1)).

fof(f137,plain,
    ( spl3_13
    | spl3_10
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f132,f107,f85,f118,f134])).

fof(f118,plain,
    ( spl3_10
  <=> v1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f85,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f132,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | sK1 = k2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f131,f108])).

fof(f131,plain,
    ( sK1 = k2_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f128,f108])).

fof(f128,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f71,f86])).

fof(f86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f120,plain,
    ( ~ spl3_10
    | spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f111,f107,f78,f118])).

fof(f111,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_2
    | ~ spl3_8 ),
    inference(superposition,[],[f82,f108])).

fof(f82,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f116,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f110,f107,f85,f114])).

fof(f110,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f86,f108])).

fof(f109,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f105,f89,f107])).

fof(f105,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f104,f90])).

fof(f90,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f104,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f56,f57])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f103,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f99,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f49,f97])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f50,f93])).

fof(f50,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f51,f89])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f52,f85])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f53,f78,f75])).

fof(f53,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f54,f78,f75])).

fof(f54,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n012.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 13:35:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.44  % (19589)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (19589)Refutation not found, incomplete strategy% (19589)------------------------------
% 0.21/0.44  % (19589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (19589)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (19589)Memory used [KB]: 10618
% 0.21/0.44  % (19589)Time elapsed: 0.004 s
% 0.21/0.44  % (19589)------------------------------
% 0.21/0.44  % (19589)------------------------------
% 0.21/0.47  % (19570)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (19583)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (19570)Refutation not found, incomplete strategy% (19570)------------------------------
% 0.21/0.48  % (19570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (19570)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (19570)Memory used [KB]: 10618
% 0.21/0.48  % (19570)Time elapsed: 0.053 s
% 0.21/0.48  % (19570)------------------------------
% 0.21/0.48  % (19570)------------------------------
% 0.21/0.49  % (19575)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (19581)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (19581)Refutation not found, incomplete strategy% (19581)------------------------------
% 0.21/0.49  % (19581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19581)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19581)Memory used [KB]: 6012
% 0.21/0.49  % (19581)Time elapsed: 0.003 s
% 0.21/0.49  % (19581)------------------------------
% 0.21/0.49  % (19581)------------------------------
% 0.21/0.49  % (19575)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f326,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f80,f83,f87,f91,f95,f99,f103,f109,f116,f120,f137,f149,f158,f172,f178,f187,f190,f218,f269,f279,f284,f290,f298,f300,f305,f307,f325])).
% 0.21/0.49  fof(f325,plain,(
% 0.21/0.49    spl3_27 | ~spl3_9 | ~spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f323,f170,f114,f251])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    spl3_27 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl3_9 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl3_17 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0 | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    sK1 = k2_pre_topc(sK0,sK1) | (~spl3_9 | ~spl3_17)),
% 0.21/0.49    inference(resolution,[],[f322,f115])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl3_17),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f319])).
% 0.21/0.49  fof(f319,plain,(
% 0.21/0.49    ( ! [X0] : (k2_pre_topc(sK0,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_17),
% 0.21/0.49    inference(resolution,[],[f171,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f170])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ~spl3_4 | spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f306,f122,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl3_11 <=> l1_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | spl3_11),
% 0.21/0.49    inference(resolution,[],[f123,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    ~spl3_4 | spl3_21 | ~spl3_9 | ~spl3_8 | ~spl3_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f304,f185,f107,f114,f195,f89])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    spl3_21 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl3_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl3_20 <=> v1_tops_1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_20)),
% 0.21/0.49    inference(forward_demodulation,[],[f303,f108])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_20)),
% 0.21/0.49    inference(forward_demodulation,[],[f272,f108])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_20),
% 0.21/0.49    inference(resolution,[],[f186,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    v1_tops_1(sK1,sK0) | ~spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f185])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    sK1 != k2_pre_topc(sK0,sK1) | k2_struct_0(sK0) != k2_pre_topc(sK0,sK1) | sK1 = k2_struct_0(sK0)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    spl3_23 | ~spl3_2 | ~spl3_8 | ~spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f297,f134,f107,f78,f203])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    spl3_23 <=> v1_subset_1(sK1,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl3_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl3_13 <=> sK1 = k2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    v1_subset_1(sK1,sK1) | (~spl3_2 | ~spl3_8 | ~spl3_13)),
% 0.21/0.49    inference(forward_demodulation,[],[f296,f135])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    sK1 = k2_struct_0(sK0) | ~spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f134])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    v1_subset_1(sK1,k2_struct_0(sK0)) | (~spl3_2 | ~spl3_8)),
% 0.21/0.49    inference(forward_demodulation,[],[f79,f108])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    ~spl3_11 | ~spl3_23 | ~spl3_8 | ~spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f220,f134,f107,f203,f122])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ~v1_subset_1(sK1,sK1) | ~l1_struct_0(sK0) | (~spl3_8 | ~spl3_13)),
% 0.21/0.49    inference(forward_demodulation,[],[f219,f135])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    ~v1_subset_1(sK1,k2_struct_0(sK0)) | ~l1_struct_0(sK0) | (~spl3_8 | ~spl3_13)),
% 0.21/0.49    inference(forward_demodulation,[],[f214,f108])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    ~v1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_struct_0(sK0) | ~spl3_13),
% 0.21/0.49    inference(superposition,[],[f55,f135])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    spl3_7 | ~spl3_6 | ~spl3_5 | ~spl3_4 | ~spl3_24 | ~spl3_8 | ~spl3_13 | spl3_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f283,f277,f134,f107,f216,f89,f93,f97,f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl3_7 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl3_6 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl3_5 <=> v1_tdlat_3(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    spl3_24 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    spl3_29 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_8 | ~spl3_13 | spl3_29)),
% 0.21/0.49    inference(forward_demodulation,[],[f282,f135])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_8 | spl3_29)),
% 0.21/0.49    inference(forward_demodulation,[],[f281,f108])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl3_29),
% 0.21/0.49    inference(resolution,[],[f278,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    ~v2_tex_2(sK1,sK0) | spl3_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f277])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    spl3_7 | ~spl3_6 | ~spl3_4 | spl3_1 | ~spl3_29 | ~spl3_24 | ~spl3_8 | ~spl3_13 | ~spl3_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f274,f185,f134,f107,f216,f277,f75,f89,f97,f101])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl3_1 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_8 | ~spl3_13 | ~spl3_20)),
% 0.21/0.49    inference(forward_demodulation,[],[f273,f135])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_8 | ~spl3_20)),
% 0.21/0.49    inference(forward_demodulation,[],[f271,f108])).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_20),
% 0.21/0.49    inference(resolution,[],[f186,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ~spl3_4 | spl3_20 | ~spl3_24 | ~spl3_8 | ~spl3_13 | ~spl3_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f268,f251,f134,f107,f216,f185,f89])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_13 | ~spl3_27)),
% 0.21/0.49    inference(forward_demodulation,[],[f267,f135])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_13 | ~spl3_27)),
% 0.21/0.49    inference(forward_demodulation,[],[f266,f108])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_13 | ~spl3_27)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f265])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    sK1 != sK1 | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_13 | ~spl3_27)),
% 0.21/0.49    inference(forward_demodulation,[],[f264,f135])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    sK1 != k2_struct_0(sK0) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_8 | ~spl3_27)),
% 0.21/0.49    inference(forward_demodulation,[],[f255,f108])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    u1_struct_0(sK0) != sK1 | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_27),
% 0.21/0.49    inference(superposition,[],[f61,f252])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f251])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (u1_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl3_24 | ~spl3_9 | ~spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f213,f134,f114,f216])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl3_9 | ~spl3_13)),
% 0.21/0.49    inference(superposition,[],[f115,f135])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ~spl3_6 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_8 | spl3_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f189,f182,f107,f114,f93,f89,f97])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    spl3_19 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_8 | spl3_19)),
% 0.21/0.49    inference(forward_demodulation,[],[f188,f108])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl3_19),
% 0.21/0.49    inference(resolution,[],[f183,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(rectify,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ~v3_pre_topc(sK1,sK0) | spl3_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f182])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ~spl3_9 | ~spl3_19 | spl3_20 | ~spl3_1 | ~spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f179,f176,f75,f185,f182,f114])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    spl3_18 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(X0,sK0) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    v1_tops_1(sK1,sK0) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_1 | ~spl3_18)),
% 0.21/0.49    inference(resolution,[],[f177,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f176])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ~spl3_6 | ~spl3_4 | spl3_18 | spl3_7 | ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f174,f107,f101,f176,f89,f97])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_tex_2(X0,sK0) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v1_tops_1(X0,sK0)) ) | (spl3_7 | ~spl3_8)),
% 0.21/0.49    inference(forward_demodulation,[],[f173,f108])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_tex_2(X0,sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v1_tops_1(X0,sK0)) ) | spl3_7),
% 0.21/0.49    inference(resolution,[],[f63,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ~v2_struct_0(sK0) | spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v1_tops_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ~spl3_4 | spl3_17 | ~spl3_8 | ~spl3_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f168,f156,f107,f170,f89])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    spl3_15 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0 | ~l1_pre_topc(sK0)) ) | (~spl3_8 | ~spl3_15)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f167])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0 | ~l1_pre_topc(sK0)) ) | (~spl3_8 | ~spl3_15)),
% 0.21/0.49    inference(forward_demodulation,[],[f166,f108])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_15),
% 0.21/0.49    inference(resolution,[],[f160,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ( ! [X0] : (v4_pre_topc(X0,sK0) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_15),
% 0.21/0.49    inference(superposition,[],[f157,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ( ! [X0] : (v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f156])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ~spl3_6 | ~spl3_4 | ~spl3_5 | spl3_15 | ~spl3_8 | ~spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f152,f147,f107,f156,f93,f89,f97])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    spl3_14 <=> ! [X0] : (v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl3_8 | ~spl3_14)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f151])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl3_8 | ~spl3_14)),
% 0.21/0.49    inference(forward_demodulation,[],[f150,f108])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ( ! [X0] : (v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl3_14),
% 0.21/0.49    inference(resolution,[],[f148,f65])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_pre_topc(X0,sK0) | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f147])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ~spl3_4 | spl3_14 | ~spl3_6 | ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f144,f107,f97,f147,f89])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ( ! [X0] : (v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (~spl3_6 | ~spl3_8)),
% 0.21/0.49    inference(forward_demodulation,[],[f143,f108])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) ) | (~spl3_6 | ~spl3_8)),
% 0.21/0.49    inference(forward_demodulation,[],[f142,f108])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) ) | ~spl3_6),
% 0.21/0.49    inference(resolution,[],[f72,f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_tops_1)).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl3_13 | spl3_10 | ~spl3_3 | ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f132,f107,f85,f118,f134])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl3_10 <=> v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    v1_subset_1(sK1,k2_struct_0(sK0)) | sK1 = k2_struct_0(sK0) | (~spl3_3 | ~spl3_8)),
% 0.21/0.49    inference(forward_demodulation,[],[f131,f108])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    sK1 = k2_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | (~spl3_3 | ~spl3_8)),
% 0.21/0.49    inference(forward_demodulation,[],[f128,f108])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 0.21/0.49    inference(resolution,[],[f71,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ~spl3_10 | spl3_2 | ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f111,f107,f78,f118])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~v1_subset_1(sK1,k2_struct_0(sK0)) | (spl3_2 | ~spl3_8)),
% 0.21/0.49    inference(superposition,[],[f82,f108])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl3_9 | ~spl3_3 | ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f110,f107,f85,f114])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_3 | ~spl3_8)),
% 0.21/0.49    inference(superposition,[],[f86,f108])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl3_8 | ~spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f105,f89,f107])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_4),
% 0.21/0.49    inference(resolution,[],[f104,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.49    inference(resolution,[],[f56,f57])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ~spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f101])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f14])).
% 0.21/0.49  fof(f14,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f97])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f50,f93])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    v1_tdlat_3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f89])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f85])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl3_1 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f53,f78,f75])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~spl3_1 | spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f78,f75])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (19575)------------------------------
% 0.21/0.49  % (19575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19575)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (19575)Memory used [KB]: 10746
% 0.21/0.49  % (19575)Time elapsed: 0.040 s
% 0.21/0.49  % (19575)------------------------------
% 0.21/0.49  % (19575)------------------------------
% 0.21/0.50  % (19567)Success in time 0.135 s
%------------------------------------------------------------------------------

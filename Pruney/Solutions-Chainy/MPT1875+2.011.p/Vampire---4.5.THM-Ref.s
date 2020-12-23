%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 187 expanded)
%              Number of leaves         :   25 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  381 ( 735 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f77,f83,f102,f108,f109,f119,f137,f139,f144,f146])).

fof(f146,plain,
    ( ~ spl2_3
    | ~ spl2_2
    | spl2_16 ),
    inference(avatar_split_clause,[],[f145,f142,f59,f63])).

fof(f63,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f59,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f142,plain,
    ( spl2_16
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_16 ),
    inference(resolution,[],[f143,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f143,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl2_16 ),
    inference(avatar_component_clause,[],[f142])).

fof(f144,plain,
    ( ~ spl2_2
    | ~ spl2_16
    | ~ spl2_3
    | spl2_6
    | spl2_1
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f140,f117,f55,f75,f63,f142,f59])).

fof(f75,plain,
    ( spl2_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f55,plain,
    ( spl2_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f117,plain,
    ( spl2_14
  <=> ! [X0] :
        ( v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f140,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_1
    | ~ spl2_14 ),
    inference(resolution,[],[f118,f56])).

fof(f56,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f118,plain,
    ( ! [X0] :
        ( v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f139,plain,
    ( spl2_6
    | ~ spl2_5
    | ~ spl2_3
    | ~ spl2_2
    | spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f138,f100,f55,f59,f63,f71,f75])).

fof(f71,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f100,plain,
    ( spl2_12
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f138,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f128,f56])).

fof(f128,plain,
    ( ! [X0] :
        ( v2_tex_2(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl2_12 ),
    inference(resolution,[],[f101,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f101,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f137,plain,
    ( ~ spl2_2
    | spl2_6
    | ~ spl2_5
    | ~ spl2_4
    | ~ spl2_3
    | spl2_13 ),
    inference(avatar_split_clause,[],[f133,f114,f63,f67,f71,f75,f59])).

fof(f67,plain,
    ( spl2_4
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f114,plain,
    ( spl2_13
  <=> v1_tdlat_3(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_13 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_13 ),
    inference(resolution,[],[f120,f51])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tdlat_3(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl2_13 ),
    inference(resolution,[],[f115,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v1_tdlat_3(X1) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f115,plain,
    ( ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f119,plain,
    ( spl2_10
    | ~ spl2_13
    | spl2_14
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f111,f81,f117,f114,f94])).

fof(f94,plain,
    ( spl2_10
  <=> v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f81,plain,
    ( spl2_7
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f111,plain,
    ( ! [X0] :
        ( v2_tex_2(sK1,X0)
        | ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | v2_struct_0(k1_pre_topc(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl2_7 ),
    inference(superposition,[],[f52,f82])).

fof(f82,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

% (8772)Refutation not found, incomplete strategy% (8772)------------------------------
% (8772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

% (8772)Termination reason: Refutation not found, incomplete strategy
fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

% (8772)Memory used [KB]: 1663
% (8772)Time elapsed: 0.088 s
% (8772)------------------------------
% (8772)------------------------------
fof(f109,plain,
    ( ~ spl2_8
    | spl2_11 ),
    inference(avatar_split_clause,[],[f104,f97,f87])).

fof(f87,plain,
    ( spl2_8
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f97,plain,
    ( spl2_11
  <=> l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f104,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl2_11 ),
    inference(resolution,[],[f98,f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f98,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f108,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_8 ),
    inference(avatar_split_clause,[],[f106,f87,f63,f59])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_8 ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_8 ),
    inference(resolution,[],[f103,f51])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl2_8 ),
    inference(resolution,[],[f88,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f88,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f102,plain,
    ( ~ spl2_10
    | ~ spl2_11
    | spl2_12
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f85,f81,f100,f97,f94])).

fof(f85,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_7 ),
    inference(superposition,[],[f50,f82])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f83,plain,
    ( ~ spl2_3
    | spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f78,f59,f81,f63])).

fof(f78,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f45,f60])).

fof(f60,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f77,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f36,f75])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f73,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f37,f71])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f39,f63])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f40,f59])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f41,f55])).

fof(f41,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:33:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (8766)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (8773)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (8765)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (8774)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (8772)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (8765)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (8764)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f77,f83,f102,f108,f109,f119,f137,f139,f144,f146])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ~spl2_3 | ~spl2_2 | spl2_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f145,f142,f59,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl2_3 <=> l1_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    spl2_16 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_16),
% 0.21/0.53    inference(resolution,[],[f143,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | spl2_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f142])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ~spl2_2 | ~spl2_16 | ~spl2_3 | spl2_6 | spl2_1 | ~spl2_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f140,f117,f55,f75,f63,f142,f59])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl2_6 <=> v2_struct_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    spl2_1 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    spl2_14 <=> ! [X0] : (v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_1 | ~spl2_14)),
% 0.21/0.54    inference(resolution,[],[f118,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ~v2_tex_2(sK1,sK0) | spl2_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f55])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ( ! [X0] : (v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl2_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f117])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    spl2_6 | ~spl2_5 | ~spl2_3 | ~spl2_2 | spl2_1 | ~spl2_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f138,f100,f55,f59,f63,f71,f75])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    spl2_5 <=> v2_pre_topc(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    spl2_12 <=> v1_xboole_0(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl2_1 | ~spl2_12)),
% 0.21/0.54    inference(resolution,[],[f128,f56])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ( ! [X0] : (v2_tex_2(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl2_12),
% 0.21/0.54    inference(resolution,[],[f101,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    v1_xboole_0(sK1) | ~spl2_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f100])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ~spl2_2 | spl2_6 | ~spl2_5 | ~spl2_4 | ~spl2_3 | spl2_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f133,f114,f63,f67,f71,f75,f59])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl2_4 <=> v1_tdlat_3(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    spl2_13 <=> v1_tdlat_3(k1_pre_topc(sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_13),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f132])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_13),
% 0.21/0.54    inference(resolution,[],[f120,f51])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | spl2_13),
% 0.21/0.54    inference(resolution,[],[f115,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v1_tdlat_3(X1)))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | spl2_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f114])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    spl2_10 | ~spl2_13 | spl2_14 | ~spl2_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f111,f81,f117,f114,f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl2_10 <=> v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    spl2_7 <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X0] : (v2_tex_2(sK1,X0) | ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl2_7),
% 0.21/0.54    inference(superposition,[],[f52,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f81])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  % (8772)Refutation not found, incomplete strategy% (8772)------------------------------
% 0.21/0.54  % (8772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f27])).
% 0.21/0.54  % (8772)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.21/0.54  
% 0.21/0.54  % (8772)Memory used [KB]: 1663
% 0.21/0.54  % (8772)Time elapsed: 0.088 s
% 0.21/0.54  % (8772)------------------------------
% 0.21/0.54  % (8772)------------------------------
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ~spl2_8 | spl2_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f104,f97,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    spl2_8 <=> l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    spl2_11 <=> l1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl2_11),
% 0.21/0.54    inference(resolution,[],[f98,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | spl2_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f97])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ~spl2_2 | ~spl2_3 | spl2_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f106,f87,f63,f59])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_8),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_8),
% 0.21/0.54    inference(resolution,[],[f103,f51])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | spl2_8),
% 0.21/0.54    inference(resolution,[],[f88,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl2_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f87])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ~spl2_10 | ~spl2_11 | spl2_12 | ~spl2_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f85,f81,f100,f97,f94])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    v1_xboole_0(sK1) | ~l1_struct_0(k1_pre_topc(sK0,sK1)) | ~v2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_7),
% 0.21/0.54    inference(superposition,[],[f50,f82])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ~spl2_3 | spl2_7 | ~spl2_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f78,f59,f81,f63])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.54    inference(resolution,[],[f45,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f59])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ~spl2_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f36,f75])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f33,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    spl2_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f37,f71])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl2_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f67])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    v1_tdlat_3(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    spl2_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f63])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    spl2_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f59])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ~spl2_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f55])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ~v2_tex_2(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (8765)------------------------------
% 0.21/0.54  % (8765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8765)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (8765)Memory used [KB]: 10618
% 0.21/0.54  % (8765)Time elapsed: 0.083 s
% 0.21/0.54  % (8765)------------------------------
% 0.21/0.54  % (8765)------------------------------
% 0.21/0.54  % (8758)Success in time 0.173 s
%------------------------------------------------------------------------------

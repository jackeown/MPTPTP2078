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
% DateTime   : Thu Dec  3 13:21:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 355 expanded)
%              Number of leaves         :   34 ( 158 expanded)
%              Depth                    :   10
%              Number of atoms          :  705 (1883 expanded)
%              Number of equality atoms :   18 (  77 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f81,f85,f89,f93,f97,f101,f105,f113,f135,f142,f143,f155,f168,f172,f175,f184,f188,f193,f194,f202,f204,f206,f216])).

fof(f216,plain,
    ( spl3_4
    | ~ spl3_3
    | spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_19 ),
    inference(avatar_split_clause,[],[f214,f160,f91,f95,f99,f103,f83,f87])).

fof(f87,plain,
    ( spl3_4
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f83,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f103,plain,
    ( spl3_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f99,plain,
    ( spl3_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f95,plain,
    ( spl3_6
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f91,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f160,plain,
    ( spl3_19
  <=> v2_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f214,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | spl3_19 ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_19 ),
    inference(resolution,[],[f212,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
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

fof(f212,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_tdlat_3(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl3_19 ),
    inference(resolution,[],[f161,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f161,plain,
    ( ~ v2_tdlat_3(sK2(sK0,sK1))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f160])).

fof(f206,plain,
    ( ~ spl3_3
    | ~ spl3_22
    | ~ spl3_5
    | spl3_8
    | ~ spl3_1
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f205,f186,f73,f103,f91,f200,f83])).

fof(f200,plain,
    ( spl3_22
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f73,plain,
    ( spl3_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f186,plain,
    ( spl3_21
  <=> ! [X0] :
        ( ~ v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f205,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_21 ),
    inference(resolution,[],[f187,f79])).

fof(f79,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f186])).

fof(f204,plain,
    ( spl3_8
    | ~ spl3_5
    | spl3_4
    | ~ spl3_3
    | spl3_22 ),
    inference(avatar_split_clause,[],[f203,f200,f83,f87,f91,f103])).

fof(f203,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_22 ),
    inference(resolution,[],[f201,f63])).

fof(f201,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( ~ spl3_3
    | ~ spl3_22
    | ~ spl3_5
    | spl3_8
    | spl3_1
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f198,f182,f73,f103,f91,f200,f83])).

fof(f182,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_tex_2(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f198,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1
    | ~ spl3_20 ),
    inference(resolution,[],[f183,f74])).

fof(f74,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f183,plain,
    ( ! [X0] :
        ( v2_tex_2(sK1,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f182])).

fof(f194,plain,
    ( ~ spl3_15
    | spl3_2
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f156,f130,f111,f76,f133])).

fof(f133,plain,
    ( spl3_15
  <=> l1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f76,plain,
    ( spl3_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f111,plain,
    ( spl3_9
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f130,plain,
    ( spl3_14
  <=> v7_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f156,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f145,f112])).

fof(f112,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f145,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl3_14 ),
    inference(resolution,[],[f131,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f131,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f130])).

fof(f193,plain,
    ( spl3_16
    | spl3_10
    | spl3_14
    | ~ spl3_19
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f190,f150,f160,f130,f117,f147])).

fof(f147,plain,
    ( spl3_16
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f117,plain,
    ( spl3_10
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f150,plain,
    ( spl3_17
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f190,plain,
    ( ! [X1] :
        ( ~ v2_tdlat_3(sK2(sK0,sK1))
        | v7_struct_0(sK2(sK0,sK1))
        | v2_struct_0(sK2(sK0,sK1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl3_17 ),
    inference(resolution,[],[f151,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | ~ v2_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_tdlat_3(X1)
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_tdlat_3(X1)
          | v7_struct_0(X1)
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
         => ( ( v2_tdlat_3(X1)
              & ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc23_tex_2)).

fof(f151,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f150])).

fof(f188,plain,
    ( spl3_10
    | spl3_17
    | spl3_21
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f176,f111,f186,f150,f117])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(sK1,X0)
        | v1_tdlat_3(sK2(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_9 ),
    inference(superposition,[],[f71,f112])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(u1_struct_0(X1),X0)
      | v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f184,plain,
    ( spl3_10
    | spl3_20
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f180,f150,f111,f182,f117])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_tex_2(sK1,X0)
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f179,f112])).

fof(f179,plain,
    ( ! [X0] :
        ( v2_tex_2(sK1,X0)
        | ~ m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f177,f112])).

fof(f177,plain,
    ( ! [X0] :
        ( v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0)
        | ~ m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_17 ),
    inference(resolution,[],[f151,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f175,plain,
    ( spl3_4
    | ~ spl3_3
    | ~ spl3_5
    | spl3_8
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f174,f147,f103,f91,f83,f87])).

fof(f174,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ spl3_16 ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_16 ),
    inference(resolution,[],[f148,f63])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f147])).

fof(f172,plain,
    ( spl3_8
    | ~ spl3_5
    | spl3_4
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f171,f117,f83,f87,f91,f103])).

fof(f171,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f118,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f118,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f168,plain,
    ( spl3_8
    | spl3_4
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_5
    | spl3_18 ),
    inference(avatar_split_clause,[],[f166,f153,f91,f99,f83,f87,f103])).

fof(f153,plain,
    ( spl3_18
  <=> v2_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f166,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | spl3_18 ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_18 ),
    inference(resolution,[],[f157,f63])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl3_18 ),
    inference(resolution,[],[f154,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f154,plain,
    ( ~ v2_pre_topc(sK2(sK0,sK1))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,
    ( spl3_16
    | spl3_10
    | spl3_17
    | ~ spl3_18
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f144,f130,f153,f150,f117,f147])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK2(sK0,sK1))
        | v1_tdlat_3(sK2(sK0,sK1))
        | v2_struct_0(sK2(sK0,sK1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_14 ),
    inference(resolution,[],[f131,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f143,plain,
    ( ~ spl3_11
    | spl3_15 ),
    inference(avatar_split_clause,[],[f137,f133,f120])).

fof(f120,plain,
    ( spl3_11
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f137,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_15 ),
    inference(resolution,[],[f134,f53])).

fof(f53,plain,(
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

fof(f134,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f142,plain,
    ( spl3_8
    | spl3_4
    | ~ spl3_3
    | ~ spl3_5
    | spl3_11 ),
    inference(avatar_split_clause,[],[f139,f120,f91,f83,f87,f103])).

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
    inference(resolution,[],[f136,f63])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl3_11 ),
    inference(resolution,[],[f121,f55])).

fof(f55,plain,(
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

fof(f121,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f135,plain,
    ( spl3_14
    | ~ spl3_15
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f115,f111,f76,f133,f130])).

fof(f115,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ spl3_9 ),
    inference(superposition,[],[f56,f112])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f113,plain,
    ( spl3_8
    | ~ spl3_5
    | spl3_9
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f107,f87,f83,f111,f91,f103])).

fof(f107,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3
    | spl3_4 ),
    inference(resolution,[],[f106,f84])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | sK1 = u1_struct_0(sK2(X0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl3_4 ),
    inference(resolution,[],[f64,f88])).

fof(f88,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK2(X0,X1)) = X1
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f105,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f45,f103])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f101,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f46,f99])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f47,f95])).

fof(f47,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f49,f87])).

fof(f49,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f50,f83])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f51,f76,f73])).

fof(f51,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f52,f76,f73])).

fof(f52,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (16290)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (16289)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (16289)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f217,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f78,f81,f85,f89,f93,f97,f101,f105,f113,f135,f142,f143,f155,f168,f172,f175,f184,f188,f193,f194,f202,f204,f206,f216])).
% 0.21/0.46  fof(f216,plain,(
% 0.21/0.46    spl3_4 | ~spl3_3 | spl3_8 | ~spl3_7 | ~spl3_6 | ~spl3_5 | spl3_19),
% 0.21/0.46    inference(avatar_split_clause,[],[f214,f160,f91,f95,f99,f103,f83,f87])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl3_4 <=> v1_xboole_0(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    spl3_8 <=> v2_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl3_7 <=> v2_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    spl3_6 <=> v2_tdlat_3(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    spl3_5 <=> l1_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f160,plain,(
% 0.21/0.46    spl3_19 <=> v2_tdlat_3(sK2(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.46  fof(f214,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | spl3_19),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f213])).
% 0.21/0.46  fof(f213,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_19),
% 0.21/0.46    inference(resolution,[],[f212,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.21/0.46  fof(f212,plain,(
% 0.21/0.46    ( ! [X1] : (~m1_pre_topc(sK2(sK0,sK1),X1) | ~l1_pre_topc(X1) | ~v2_tdlat_3(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | spl3_19),
% 0.21/0.46    inference(resolution,[],[f161,f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    ~v2_tdlat_3(sK2(sK0,sK1)) | spl3_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f160])).
% 0.21/0.46  fof(f206,plain,(
% 0.21/0.46    ~spl3_3 | ~spl3_22 | ~spl3_5 | spl3_8 | ~spl3_1 | ~spl3_21),
% 0.21/0.46    inference(avatar_split_clause,[],[f205,f186,f73,f103,f91,f200,f83])).
% 0.21/0.46  fof(f200,plain,(
% 0.21/0.46    spl3_22 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl3_1 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    spl3_21 <=> ! [X0] : (~v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.46  fof(f205,plain,(
% 0.21/0.46    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_21)),
% 0.21/0.46    inference(resolution,[],[f187,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    v2_tex_2(sK1,sK0) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f73])).
% 0.21/0.46  fof(f187,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_21),
% 0.21/0.46    inference(avatar_component_clause,[],[f186])).
% 0.21/0.46  fof(f204,plain,(
% 0.21/0.46    spl3_8 | ~spl3_5 | spl3_4 | ~spl3_3 | spl3_22),
% 0.21/0.46    inference(avatar_split_clause,[],[f203,f200,f83,f87,f91,f103])).
% 0.21/0.46  fof(f203,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_22),
% 0.21/0.46    inference(resolution,[],[f201,f63])).
% 0.21/0.46  fof(f201,plain,(
% 0.21/0.46    ~m1_pre_topc(sK2(sK0,sK1),sK0) | spl3_22),
% 0.21/0.46    inference(avatar_component_clause,[],[f200])).
% 0.21/0.46  fof(f202,plain,(
% 0.21/0.46    ~spl3_3 | ~spl3_22 | ~spl3_5 | spl3_8 | spl3_1 | ~spl3_20),
% 0.21/0.46    inference(avatar_split_clause,[],[f198,f182,f73,f103,f91,f200,f83])).
% 0.21/0.46  fof(f182,plain,(
% 0.21/0.46    spl3_20 <=> ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_tex_2(sK1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_1 | ~spl3_20)),
% 0.21/0.46    inference(resolution,[],[f183,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ~v2_tex_2(sK1,sK0) | spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f73])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    ( ! [X0] : (v2_tex_2(sK1,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_20),
% 0.21/0.46    inference(avatar_component_clause,[],[f182])).
% 0.21/0.46  fof(f194,plain,(
% 0.21/0.46    ~spl3_15 | spl3_2 | ~spl3_9 | ~spl3_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f156,f130,f111,f76,f133])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    spl3_15 <=> l1_struct_0(sK2(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl3_2 <=> v1_zfmisc_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    spl3_9 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    spl3_14 <=> v7_struct_0(sK2(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.46  fof(f156,plain,(
% 0.21/0.46    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | (~spl3_9 | ~spl3_14)),
% 0.21/0.46    inference(forward_demodulation,[],[f145,f112])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f111])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | ~spl3_14),
% 0.21/0.46    inference(resolution,[],[f131,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    v7_struct_0(sK2(sK0,sK1)) | ~spl3_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f130])).
% 0.21/0.46  fof(f193,plain,(
% 0.21/0.46    spl3_16 | spl3_10 | spl3_14 | ~spl3_19 | ~spl3_17),
% 0.21/0.46    inference(avatar_split_clause,[],[f190,f150,f160,f130,f117,f147])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    spl3_16 <=> ! [X0] : (~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    spl3_10 <=> v2_struct_0(sK2(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f150,plain,(
% 0.21/0.46    spl3_17 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    ( ! [X1] : (~v2_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X1) | ~l1_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl3_17),
% 0.21/0.46    inference(resolution,[],[f151,f58])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_tdlat_3(X1) | ~v2_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_tdlat_3(X1) & ~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc23_tex_2)).
% 0.21/0.46  fof(f151,plain,(
% 0.21/0.46    v1_tdlat_3(sK2(sK0,sK1)) | ~spl3_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f150])).
% 0.21/0.46  fof(f188,plain,(
% 0.21/0.46    spl3_10 | spl3_17 | spl3_21 | ~spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f176,f111,f186,f150,f117])).
% 0.21/0.46  fof(f176,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_tex_2(sK1,X0) | v1_tdlat_3(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_9),
% 0.21/0.46    inference(superposition,[],[f71,f112])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v2_tex_2(u1_struct_0(X1),X0) | v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    spl3_10 | spl3_20 | ~spl3_9 | ~spl3_17),
% 0.21/0.46    inference(avatar_split_clause,[],[f180,f150,f111,f182,f117])).
% 0.21/0.46  fof(f180,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(sK1,X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl3_9 | ~spl3_17)),
% 0.21/0.46    inference(forward_demodulation,[],[f179,f112])).
% 0.21/0.46  fof(f179,plain,(
% 0.21/0.46    ( ! [X0] : (v2_tex_2(sK1,X0) | ~m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl3_9 | ~spl3_17)),
% 0.21/0.46    inference(forward_demodulation,[],[f177,f112])).
% 0.21/0.46  fof(f177,plain,(
% 0.21/0.46    ( ! [X0] : (v2_tex_2(u1_struct_0(sK2(sK0,sK1)),X0) | ~m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_17),
% 0.21/0.46    inference(resolution,[],[f151,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f44])).
% 0.21/0.46  fof(f175,plain,(
% 0.21/0.46    spl3_4 | ~spl3_3 | ~spl3_5 | spl3_8 | ~spl3_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f174,f147,f103,f91,f83,f87])).
% 0.21/0.46  fof(f174,plain,(
% 0.21/0.46    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~spl3_16),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f173])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_16),
% 0.21/0.46    inference(resolution,[],[f148,f63])).
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl3_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f147])).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    spl3_8 | ~spl3_5 | spl3_4 | ~spl3_3 | ~spl3_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f171,f117,f83,f87,f91,f103])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_10),
% 0.21/0.46    inference(resolution,[],[f118,f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f43])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    v2_struct_0(sK2(sK0,sK1)) | ~spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f117])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    spl3_8 | spl3_4 | ~spl3_3 | ~spl3_7 | ~spl3_5 | spl3_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f166,f153,f91,f99,f83,f87,f103])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    spl3_18 <=> v2_pre_topc(sK2(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | v2_struct_0(sK0) | spl3_18),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f165])).
% 0.21/0.46  fof(f165,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_18),
% 0.21/0.46    inference(resolution,[],[f157,f63])).
% 0.21/0.46  fof(f157,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl3_18),
% 0.21/0.46    inference(resolution,[],[f154,f69])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    ~v2_pre_topc(sK2(sK0,sK1)) | spl3_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f153])).
% 0.21/0.46  fof(f155,plain,(
% 0.21/0.46    spl3_16 | spl3_10 | spl3_17 | ~spl3_18 | ~spl3_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f144,f130,f153,f150,f117,f147])).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_pre_topc(sK2(sK0,sK1)) | v1_tdlat_3(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_14),
% 0.21/0.46    inference(resolution,[],[f131,f60])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v7_struct_0(X1) | ~v2_pre_topc(X1) | v1_tdlat_3(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    ~spl3_11 | spl3_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f137,f133,f120])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    spl3_11 <=> l1_pre_topc(sK2(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    ~l1_pre_topc(sK2(sK0,sK1)) | spl3_15),
% 0.21/0.46    inference(resolution,[],[f134,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    ~l1_struct_0(sK2(sK0,sK1)) | spl3_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f133])).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    spl3_8 | spl3_4 | ~spl3_3 | ~spl3_5 | spl3_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f139,f120,f91,f83,f87,f103])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | v2_struct_0(sK0) | spl3_11),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f138])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_11),
% 0.21/0.46    inference(resolution,[],[f136,f63])).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_pre_topc(sK2(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | spl3_11),
% 0.21/0.46    inference(resolution,[],[f121,f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ~l1_pre_topc(sK2(sK0,sK1)) | spl3_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f120])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    spl3_14 | ~spl3_15 | ~spl3_2 | ~spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f115,f111,f76,f133,f130])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    ~v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~spl3_9),
% 0.21/0.46    inference(superposition,[],[f56,f112])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    spl3_8 | ~spl3_5 | spl3_9 | ~spl3_3 | spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f107,f87,f83,f111,f91,f103])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_3 | spl3_4)),
% 0.21/0.46    inference(resolution,[],[f106,f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f83])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | sK1 = u1_struct_0(sK2(X0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | spl3_4),
% 0.21/0.46    inference(resolution,[],[f64,f88])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    ~v1_xboole_0(sK1) | spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f87])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1 | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f43])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    ~spl3_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f45,f103])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.46    inference(negated_conjecture,[],[f12])).
% 0.21/0.46  fof(f12,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f46,f99])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    v2_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f41])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f47,f95])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    v2_tdlat_3(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f41])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f48,f91])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f41])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ~spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f49,f87])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ~v1_xboole_0(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f41])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f50,f83])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f41])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl3_1 | spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f51,f76,f73])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f41])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f52,f76,f73])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f41])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (16289)------------------------------
% 0.21/0.46  % (16289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (16289)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (16289)Memory used [KB]: 10746
% 0.21/0.46  % (16289)Time elapsed: 0.062 s
% 0.21/0.46  % (16289)------------------------------
% 0.21/0.46  % (16289)------------------------------
% 0.21/0.47  % (16282)Success in time 0.108 s
%------------------------------------------------------------------------------

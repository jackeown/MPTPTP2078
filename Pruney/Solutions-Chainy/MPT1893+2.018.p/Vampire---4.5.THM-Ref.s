%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 325 expanded)
%              Number of leaves         :   40 ( 154 expanded)
%              Depth                    :    9
%              Number of atoms          :  519 (1352 expanded)
%              Number of equality atoms :   39 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f94,f99,f104,f109,f114,f119,f124,f133,f158,f174,f193,f202,f219,f253,f258,f270,f296,f312,f318,f346,f359])).

fof(f359,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | sK1 != k2_pre_topc(sK0,sK1)
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f346,plain,
    ( ~ spl3_10
    | spl3_16
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f345,f289,f169,f121])).

fof(f121,plain,
    ( spl3_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f169,plain,
    ( spl3_16
  <=> v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f289,plain,
    ( spl3_28
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f345,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_16
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f331,f152])).

fof(f152,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f141,f75])).

fof(f75,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f55,f74])).

fof(f74,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f57,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f141,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f56,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f331,plain,
    ( ~ v1_xboole_0(k3_subset_1(sK1,sK1))
    | spl3_16
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f171,f291])).

fof(f291,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f289])).

fof(f171,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f318,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_28
    | ~ spl3_17
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f317,f227,f178,f289,f96,f101])).

fof(f101,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f96,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f178,plain,
    ( spl3_17
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f227,plain,
    ( spl3_24
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f317,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_17
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f314,f180])).

fof(f180,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f178])).

fof(f314,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_24 ),
    inference(resolution,[],[f229,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f229,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f227])).

fof(f312,plain,
    ( spl3_24
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | spl3_9 ),
    inference(avatar_split_clause,[],[f311,f116,f111,f101,f96,f87,f82,f227])).

fof(f82,plain,
    ( spl3_2
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f87,plain,
    ( spl3_3
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f111,plain,
    ( spl3_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f116,plain,
    ( spl3_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f311,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f118,f113,f103,f84,f98,f89,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f89,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f84,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f103,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f113,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f118,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f296,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f250,f111,f106,f101,f96,f91,f87])).

fof(f91,plain,
    ( spl3_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f106,plain,
    ( spl3_7
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f250,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f113,f103,f108,f98,f93,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ v3_tdlat_3(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & v4_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & v4_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f93,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f108,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f270,plain,
    ( ~ spl3_3
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_14
    | spl3_22 ),
    inference(avatar_split_clause,[],[f269,f216,f154,f130,f101,f87])).

fof(f130,plain,
    ( spl3_11
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f154,plain,
    ( spl3_14
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f216,plain,
    ( spl3_22
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f269,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_14
    | spl3_22 ),
    inference(forward_demodulation,[],[f268,f156])).

fof(f156,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f268,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl3_6
    | ~ spl3_11
    | spl3_22 ),
    inference(unit_resulting_resolution,[],[f103,f132,f218,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f218,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f216])).

fof(f132,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f258,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_26
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f256,f227,f238,f96,f101])).

fof(f238,plain,
    ( spl3_26
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f256,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_24 ),
    inference(resolution,[],[f229,f60])).

fof(f253,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f252,f101,f96,f91,f178])).

fof(f252,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f103,f98,f93,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f219,plain,
    ( ~ spl3_22
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11
    | spl3_18 ),
    inference(avatar_split_clause,[],[f213,f190,f130,f111,f106,f101,f216])).

fof(f190,plain,
    ( spl3_18
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f213,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_11
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f113,f103,f108,f192,f132,f66])).

fof(f192,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f202,plain,
    ( ~ spl3_19
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | spl3_9 ),
    inference(avatar_split_clause,[],[f196,f116,f111,f101,f96,f82,f199])).

fof(f199,plain,
    ( spl3_19
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f196,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f118,f113,f103,f84,f98,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
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
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(f193,plain,
    ( ~ spl3_18
    | spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f187,f101,f96,f91,f190])).

fof(f187,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f103,f92,f98,f63])).

fof(f92,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f174,plain,
    ( ~ spl3_16
    | ~ spl3_1
    | ~ spl3_5
    | spl3_15 ),
    inference(avatar_split_clause,[],[f173,f165,f96,f77,f169])).

fof(f77,plain,
    ( spl3_1
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f165,plain,
    ( spl3_15
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f173,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_1
    | ~ spl3_5
    | spl3_15 ),
    inference(unit_resulting_resolution,[],[f79,f98,f166,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(k3_subset_1(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & v1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

fof(f166,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f165])).

fof(f79,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f158,plain,
    ( spl3_14
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f143,f96,f154])).

fof(f143,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_5 ),
    inference(resolution,[],[f71,f98])).

fof(f133,plain,
    ( spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f125,f96,f130])).

fof(f125,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f98,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f124,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f53,f121])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f119,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f45,f116])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    & v3_tex_2(sK1,sK0)
    & ( v4_pre_topc(sK1,sK0)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_subset_1(X1,u1_struct_0(X0))
            & v3_tex_2(X1,X0)
            & ( v4_pre_topc(X1,X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(sK0))
          & v3_tex_2(X1,sK0)
          & ( v4_pre_topc(X1,sK0)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( v1_subset_1(X1,u1_struct_0(sK0))
        & v3_tex_2(X1,sK0)
        & ( v4_pre_topc(X1,sK0)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( v1_subset_1(sK1,u1_struct_0(sK0))
      & v3_tex_2(sK1,sK0)
      & ( v4_pre_topc(sK1,sK0)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

fof(f114,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f46,f111])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f109,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f50,f91,f87])).

fof(f50,plain,
    ( v4_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f51,f82])).

fof(f51,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f52,f77])).

fof(f52,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:38:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (17909)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (17905)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (17907)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (17908)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (17917)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (17919)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (17911)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (17916)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (17914)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (17906)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (17915)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (17913)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (17909)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f80,f85,f94,f99,f104,f109,f114,f119,f124,f133,f158,f174,f193,f202,f219,f253,f258,f270,f296,f312,f318,f346,f359])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | sK1 != k2_pre_topc(sK0,sK1) | v1_xboole_0(sK1) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    ~spl3_10 | spl3_16 | ~spl3_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f345,f289,f169,f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl3_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    spl3_16 <=> v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    spl3_28 <=> u1_struct_0(sK0) = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.50  fof(f345,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0) | (spl3_16 | ~spl3_28)),
% 0.21/0.50    inference(forward_demodulation,[],[f331,f152])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f141,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f55,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f57,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f56,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    ~v1_xboole_0(k3_subset_1(sK1,sK1)) | (spl3_16 | ~spl3_28)),
% 0.21/0.50    inference(backward_demodulation,[],[f171,f291])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    u1_struct_0(sK0) = sK1 | ~spl3_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f289])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ~v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) | spl3_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f169])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    ~spl3_6 | ~spl3_5 | spl3_28 | ~spl3_17 | ~spl3_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f317,f227,f178,f289,f96,f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl3_6 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl3_17 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    spl3_24 <=> v1_tops_1(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.50  fof(f317,plain,(
% 0.21/0.50    u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_17 | ~spl3_24)),
% 0.21/0.50    inference(forward_demodulation,[],[f314,f180])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f178])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_24),
% 0.21/0.50    inference(resolution,[],[f229,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    v1_tops_1(sK1,sK0) | ~spl3_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f227])).
% 0.21/0.51  fof(f312,plain,(
% 0.21/0.51    spl3_24 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_8 | spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f311,f116,f111,f101,f96,f87,f82,f227])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl3_2 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl3_3 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl3_8 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl3_9 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    v1_tops_1(sK1,sK0) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_8 | spl3_9)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f118,f113,f103,f84,f98,f89,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    v3_pre_topc(sK1,sK0) | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f87])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    v3_tex_2(sK1,sK0) | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f82])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl3_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f101])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    v2_pre_topc(sK0) | ~spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f111])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ~v2_struct_0(sK0) | spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f116])).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f250,f111,f106,f101,f96,f91,f87])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl3_4 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl3_7 <=> v3_tdlat_3(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    v3_pre_topc(sK1,sK0) | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f113,f103,f108,f98,f93,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~v3_tdlat_3(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & v4_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & v4_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(rectify,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    v4_pre_topc(sK1,sK0) | ~spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    v3_tdlat_3(sK0) | ~spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f106])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    ~spl3_3 | ~spl3_6 | ~spl3_11 | ~spl3_14 | spl3_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f269,f216,f154,f130,f101,f87])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    spl3_11 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl3_14 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    spl3_22 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    ~v3_pre_topc(sK1,sK0) | (~spl3_6 | ~spl3_11 | ~spl3_14 | spl3_22)),
% 0.21/0.51    inference(forward_demodulation,[],[f268,f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f154])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | (~spl3_6 | ~spl3_11 | spl3_22)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f103,f132,f218,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl3_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f216])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f130])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    ~spl3_6 | ~spl3_5 | spl3_26 | ~spl3_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f256,f227,f238,f96,f101])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    spl3_26 <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_24),
% 0.21/0.51    inference(resolution,[],[f229,f60])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    spl3_17 | ~spl3_4 | ~spl3_5 | ~spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f252,f101,f96,f91,f178])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    sK1 = k2_pre_topc(sK0,sK1) | (~spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f103,f98,f93,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    ~spl3_22 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_11 | spl3_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f213,f190,f130,f111,f106,f101,f216])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    spl3_18 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_11 | spl3_18)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f113,f103,f108,f192,f132,f66])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl3_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f190])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    ~spl3_19 | ~spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_8 | spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f196,f116,f111,f101,f96,f82,f199])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    spl3_19 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ~v1_xboole_0(sK1) | (~spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_8 | spl3_9)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f118,f113,f103,f84,f98,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v3_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    ~spl3_18 | spl3_4 | ~spl3_5 | ~spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f187,f101,f96,f91,f190])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f103,f92,f98,f63])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~v4_pre_topc(sK1,sK0) | spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ~spl3_16 | ~spl3_1 | ~spl3_5 | spl3_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f173,f165,f96,f77,f169])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl3_1 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl3_15 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ~v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_1 | ~spl3_5 | spl3_15)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f79,f98,f166,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(k3_subset_1(X0,X1)) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & v1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k3_subset_1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ~v1_xboole_0(u1_struct_0(sK0)) | spl3_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f165])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f77])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    spl3_14 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f143,f96,f154])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_5),
% 0.21/0.51    inference(resolution,[],[f71,f98])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    spl3_11 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f125,f96,f130])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f98,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f53,f121])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ~spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f116])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    (v1_subset_1(sK1,u1_struct_0(sK0)) & v3_tex_2(sK1,sK0) & (v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f37,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v1_subset_1(X1,u1_struct_0(sK0)) & v3_tex_2(X1,sK0) & (v4_pre_topc(X1,sK0) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ? [X1] : (v1_subset_1(X1,u1_struct_0(sK0)) & v3_tex_2(X1,sK0) & (v4_pre_topc(X1,sK0) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (v1_subset_1(sK1,u1_struct_0(sK0)) & v3_tex_2(sK1,sK0) & (v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f16])).
% 0.21/0.51  fof(f16,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f111])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f106])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    v3_tdlat_3(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f101])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f96])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl3_3 | spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f91,f87])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f82])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v3_tex_2(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f52,f77])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (17909)------------------------------
% 0.21/0.51  % (17909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17909)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (17909)Memory used [KB]: 6396
% 0.21/0.51  % (17909)Time elapsed: 0.072 s
% 0.21/0.51  % (17909)------------------------------
% 0.21/0.51  % (17909)------------------------------
% 0.21/0.51  % (17914)Refutation not found, incomplete strategy% (17914)------------------------------
% 0.21/0.51  % (17914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17914)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17914)Memory used [KB]: 10746
% 0.21/0.51  % (17914)Time elapsed: 0.077 s
% 0.21/0.51  % (17914)------------------------------
% 0.21/0.51  % (17914)------------------------------
% 0.21/0.51  % (17902)Success in time 0.144 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 13:22:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 291 expanded)
%              Number of leaves         :   45 ( 128 expanded)
%              Depth                    :    8
%              Number of atoms          :  647 (1349 expanded)
%              Number of equality atoms :   47 (  62 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f393,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f120,f125,f133,f137,f141,f146,f150,f179,f198,f216,f220,f240,f244,f248,f284,f299,f326,f344,f359,f377,f392])).

fof(f392,plain,
    ( ~ spl4_10
    | spl4_31
    | ~ spl4_39
    | ~ spl4_43 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | ~ spl4_10
    | spl4_31
    | ~ spl4_39
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f124,f390])).

fof(f390,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_31
    | ~ spl4_39
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f380,f376])).

fof(f376,plain,
    ( ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl4_43
  <=> ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f380,plain,
    ( ~ v1_xboole_0(k3_subset_1(sK1,sK1))
    | spl4_31
    | ~ spl4_39 ),
    inference(superposition,[],[f239,f358])).

fof(f358,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl4_39
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f239,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl4_31
  <=> v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f124,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f377,plain,
    ( spl4_43
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f202,f177,f144,f135,f375])).

fof(f135,plain,
    ( spl4_13
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f144,plain,
    ( spl4_15
  <=> ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f177,plain,
    ( spl4_22
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f202,plain,
    ( ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0)
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f200,f145])).

fof(f145,plain,
    ( ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f200,plain,
    ( ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))
    | ~ spl4_13
    | ~ spl4_22 ),
    inference(unit_resulting_resolution,[],[f136,f178])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f177])).

fof(f136,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f359,plain,
    ( spl4_39
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_28
    | ~ spl4_36
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f347,f341,f311,f218,f108,f93,f356])).

fof(f93,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f108,plain,
    ( spl4_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f218,plain,
    ( spl4_28
  <=> ! [X1,X0] :
        ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
        | ~ v1_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f311,plain,
    ( spl4_36
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f341,plain,
    ( spl4_37
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f347,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_28
    | ~ spl4_36
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f346,f313])).

fof(f313,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f311])).

fof(f346,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_28
    | ~ spl4_37 ),
    inference(unit_resulting_resolution,[],[f95,f110,f343,f219])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
        | ~ v1_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f218])).

fof(f343,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f341])).

fof(f110,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f95,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f344,plain,
    ( spl4_37
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f320,f297,f113,f108,f98,f93,f83,f78,f341])).

fof(f78,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f83,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f98,plain,
    ( spl4_5
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f113,plain,
    ( spl4_8
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f297,plain,
    ( spl4_34
  <=> ! [X1,X0] :
        ( v1_tops_1(X1,X0)
        | ~ v3_tex_2(X1,X0)
        | ~ v3_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f320,plain,
    ( v1_tops_1(sK1,sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f80,f85,f95,f100,f110,f115,f298])).

fof(f298,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_tex_2(X1,X0)
        | ~ v3_pre_topc(X1,X0)
        | v1_tops_1(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f297])).

fof(f115,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f100,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f85,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f80,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f326,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_27
    | ~ spl4_32
    | spl4_36 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_27
    | ~ spl4_32
    | spl4_36 ),
    inference(subsumption_resolution,[],[f95,f323])).

fof(f323,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_27
    | ~ spl4_32
    | spl4_36 ),
    inference(subsumption_resolution,[],[f318,f321])).

fof(f321,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f85,f95,f90,f110,f115,f243])).

fof(f243,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X2,X0)
        | v4_pre_topc(X2,X0)
        | ~ v3_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl4_32
  <=> ! [X0,X2] :
        ( v4_pre_topc(X2,X0)
        | ~ v3_pre_topc(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f90,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_3
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f318,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | ~ spl4_27
    | spl4_36 ),
    inference(subsumption_resolution,[],[f292,f312])).

fof(f312,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f311])).

fof(f292,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | ~ spl4_27 ),
    inference(resolution,[],[f110,f215])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) = X1
        | ~ l1_pre_topc(X0) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl4_27
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f299,plain,(
    spl4_34 ),
    inference(avatar_split_clause,[],[f64,f297])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
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
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(f284,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | spl4_8
    | ~ spl4_9
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | spl4_8
    | ~ spl4_9
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f110,f259])).

fof(f259,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_8
    | ~ spl4_9
    | ~ spl4_33 ),
    inference(unit_resulting_resolution,[],[f85,f95,f90,f114,f119,f247])).

fof(f247,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X2,X0)
        | v3_pre_topc(X2,X0)
        | ~ v3_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl4_33
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f119,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_9
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f114,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f248,plain,(
    spl4_33 ),
    inference(avatar_split_clause,[],[f69,f246])).

fof(f69,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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

fof(f244,plain,(
    spl4_32 ),
    inference(avatar_split_clause,[],[f65,f242])).

fof(f65,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK2(X0),X0)
            & v3_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK2(X0),X0)
        & v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

fof(f240,plain,
    ( ~ spl4_31
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f203,f196,f108,f103,f237])).

fof(f103,plain,
    ( spl4_6
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f196,plain,
    ( spl4_26
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(k3_subset_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f203,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f105,f110,f197])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(k3_subset_1(X0,X1))
        | ~ v1_subset_1(X1,X0) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f196])).

fof(f105,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f220,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f61,f218])).

fof(f61,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f216,plain,(
    spl4_27 ),
    inference(avatar_split_clause,[],[f59,f214])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f198,plain,
    ( spl4_26
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f151,f148,f196])).

fof(f148,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k3_subset_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_subset_1(X1,X0) )
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f74,f149])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_subset_1(X1,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & v1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tex_2)).

fof(f179,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f73,f177])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f150,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f63,f148])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f146,plain,
    ( spl4_15
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f142,f139,f131,f144])).

fof(f131,plain,
    ( spl4_12
  <=> ! [X0] : k2_subset_1(X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f139,plain,
    ( spl4_14
  <=> ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f142,plain,
    ( ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f140,f132])).

fof(f132,plain,
    ( ! [X0] : k2_subset_1(X0) = X0
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f140,plain,
    ( ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f76,f139])).

fof(f76,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f58,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f137,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f57,f135])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f133,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f56,f131])).

fof(f56,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f125,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f54,f122])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f120,plain,
    ( spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f51,f117,f113])).

fof(f51,plain,
    ( v4_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    & v3_tex_2(sK1,sK0)
    & ( v4_pre_topc(sK1,sK0)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

fof(f111,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f50,f108])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f106,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f53,f103])).

fof(f53,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f52,f98])).

fof(f52,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f49,f93])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f48,f88])).

fof(f48,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f47,f83])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f46,f78])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (17141)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.43  % (17138)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.44  % (17138)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f393,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f120,f125,f133,f137,f141,f146,f150,f179,f198,f216,f220,f240,f244,f248,f284,f299,f326,f344,f359,f377,f392])).
% 0.20/0.44  fof(f392,plain,(
% 0.20/0.44    ~spl4_10 | spl4_31 | ~spl4_39 | ~spl4_43),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f391])).
% 0.20/0.44  fof(f391,plain,(
% 0.20/0.44    $false | (~spl4_10 | spl4_31 | ~spl4_39 | ~spl4_43)),
% 0.20/0.44    inference(subsumption_resolution,[],[f124,f390])).
% 0.20/0.44  fof(f390,plain,(
% 0.20/0.44    ~v1_xboole_0(k1_xboole_0) | (spl4_31 | ~spl4_39 | ~spl4_43)),
% 0.20/0.44    inference(forward_demodulation,[],[f380,f376])).
% 0.20/0.44  fof(f376,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) ) | ~spl4_43),
% 0.20/0.44    inference(avatar_component_clause,[],[f375])).
% 0.20/0.44  fof(f375,plain,(
% 0.20/0.44    spl4_43 <=> ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.20/0.44  fof(f380,plain,(
% 0.20/0.44    ~v1_xboole_0(k3_subset_1(sK1,sK1)) | (spl4_31 | ~spl4_39)),
% 0.20/0.44    inference(superposition,[],[f239,f358])).
% 0.20/0.44  fof(f358,plain,(
% 0.20/0.44    u1_struct_0(sK0) = sK1 | ~spl4_39),
% 0.20/0.44    inference(avatar_component_clause,[],[f356])).
% 0.20/0.44  fof(f356,plain,(
% 0.20/0.44    spl4_39 <=> u1_struct_0(sK0) = sK1),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.20/0.44  fof(f239,plain,(
% 0.20/0.44    ~v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) | spl4_31),
% 0.20/0.44    inference(avatar_component_clause,[],[f237])).
% 0.20/0.44  fof(f237,plain,(
% 0.20/0.44    spl4_31 <=> v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.20/0.44  fof(f124,plain,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0) | ~spl4_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f122])).
% 0.20/0.44  fof(f122,plain,(
% 0.20/0.44    spl4_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.44  fof(f377,plain,(
% 0.20/0.44    spl4_43 | ~spl4_13 | ~spl4_15 | ~spl4_22),
% 0.20/0.44    inference(avatar_split_clause,[],[f202,f177,f144,f135,f375])).
% 0.20/0.44  fof(f135,plain,(
% 0.20/0.44    spl4_13 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.44  fof(f144,plain,(
% 0.20/0.44    spl4_15 <=> ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.44  fof(f177,plain,(
% 0.20/0.44    spl4_22 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.44  fof(f202,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) ) | (~spl4_13 | ~spl4_15 | ~spl4_22)),
% 0.20/0.44    inference(forward_demodulation,[],[f200,f145])).
% 0.20/0.44  fof(f145,plain,(
% 0.20/0.44    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) ) | ~spl4_15),
% 0.20/0.44    inference(avatar_component_clause,[],[f144])).
% 0.20/0.44  fof(f200,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) ) | (~spl4_13 | ~spl4_22)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f136,f178])).
% 0.20/0.44  fof(f178,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_22),
% 0.20/0.44    inference(avatar_component_clause,[],[f177])).
% 0.20/0.44  fof(f136,plain,(
% 0.20/0.44    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl4_13),
% 0.20/0.44    inference(avatar_component_clause,[],[f135])).
% 0.20/0.44  fof(f359,plain,(
% 0.20/0.44    spl4_39 | ~spl4_4 | ~spl4_7 | ~spl4_28 | ~spl4_36 | ~spl4_37),
% 0.20/0.44    inference(avatar_split_clause,[],[f347,f341,f311,f218,f108,f93,f356])).
% 0.20/0.44  fof(f93,plain,(
% 0.20/0.44    spl4_4 <=> l1_pre_topc(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.44  fof(f108,plain,(
% 0.20/0.44    spl4_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.44  fof(f218,plain,(
% 0.20/0.44    spl4_28 <=> ! [X1,X0] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.44  fof(f311,plain,(
% 0.20/0.44    spl4_36 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.44  fof(f341,plain,(
% 0.20/0.44    spl4_37 <=> v1_tops_1(sK1,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.20/0.44  fof(f347,plain,(
% 0.20/0.44    u1_struct_0(sK0) = sK1 | (~spl4_4 | ~spl4_7 | ~spl4_28 | ~spl4_36 | ~spl4_37)),
% 0.20/0.44    inference(forward_demodulation,[],[f346,f313])).
% 0.20/0.44  fof(f313,plain,(
% 0.20/0.44    sK1 = k2_pre_topc(sK0,sK1) | ~spl4_36),
% 0.20/0.44    inference(avatar_component_clause,[],[f311])).
% 0.20/0.44  fof(f346,plain,(
% 0.20/0.44    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl4_4 | ~spl4_7 | ~spl4_28 | ~spl4_37)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f95,f110,f343,f219])).
% 0.20/0.44  fof(f219,plain,(
% 0.20/0.44    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_28),
% 0.20/0.44    inference(avatar_component_clause,[],[f218])).
% 0.20/0.44  fof(f343,plain,(
% 0.20/0.44    v1_tops_1(sK1,sK0) | ~spl4_37),
% 0.20/0.44    inference(avatar_component_clause,[],[f341])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f108])).
% 0.20/0.44  fof(f95,plain,(
% 0.20/0.44    l1_pre_topc(sK0) | ~spl4_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f93])).
% 0.20/0.44  fof(f344,plain,(
% 0.20/0.44    spl4_37 | spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_34),
% 0.20/0.44    inference(avatar_split_clause,[],[f320,f297,f113,f108,f98,f93,f83,f78,f341])).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    spl4_1 <=> v2_struct_0(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.44  fof(f83,plain,(
% 0.20/0.44    spl4_2 <=> v2_pre_topc(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.44  fof(f98,plain,(
% 0.20/0.44    spl4_5 <=> v3_tex_2(sK1,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.44  fof(f113,plain,(
% 0.20/0.44    spl4_8 <=> v3_pre_topc(sK1,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.44  fof(f297,plain,(
% 0.20/0.44    spl4_34 <=> ! [X1,X0] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.20/0.44  fof(f320,plain,(
% 0.20/0.44    v1_tops_1(sK1,sK0) | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_34)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f80,f85,f95,f100,f110,f115,f298])).
% 0.20/0.44  fof(f298,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | v1_tops_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl4_34),
% 0.20/0.44    inference(avatar_component_clause,[],[f297])).
% 0.20/0.44  fof(f115,plain,(
% 0.20/0.44    v3_pre_topc(sK1,sK0) | ~spl4_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f113])).
% 0.20/0.44  fof(f100,plain,(
% 0.20/0.44    v3_tex_2(sK1,sK0) | ~spl4_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f98])).
% 0.20/0.44  fof(f85,plain,(
% 0.20/0.44    v2_pre_topc(sK0) | ~spl4_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f83])).
% 0.20/0.44  fof(f80,plain,(
% 0.20/0.44    ~v2_struct_0(sK0) | spl4_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f78])).
% 0.20/0.44  fof(f326,plain,(
% 0.20/0.44    ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_8 | ~spl4_27 | ~spl4_32 | spl4_36),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f325])).
% 0.20/0.44  fof(f325,plain,(
% 0.20/0.44    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_8 | ~spl4_27 | ~spl4_32 | spl4_36)),
% 0.20/0.44    inference(subsumption_resolution,[],[f95,f323])).
% 0.20/0.44  fof(f323,plain,(
% 0.20/0.44    ~l1_pre_topc(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_8 | ~spl4_27 | ~spl4_32 | spl4_36)),
% 0.20/0.44    inference(subsumption_resolution,[],[f318,f321])).
% 0.20/0.44  fof(f321,plain,(
% 0.20/0.44    v4_pre_topc(sK1,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_8 | ~spl4_32)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f85,f95,f90,f110,f115,f243])).
% 0.20/0.44  fof(f243,plain,(
% 0.20/0.44    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | v4_pre_topc(X2,X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_32),
% 0.20/0.44    inference(avatar_component_clause,[],[f242])).
% 0.20/0.44  fof(f242,plain,(
% 0.20/0.44    spl4_32 <=> ! [X0,X2] : (v4_pre_topc(X2,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.44  fof(f90,plain,(
% 0.20/0.44    v3_tdlat_3(sK0) | ~spl4_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f88])).
% 0.20/0.44  fof(f88,plain,(
% 0.20/0.44    spl4_3 <=> v3_tdlat_3(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.44  fof(f318,plain,(
% 0.20/0.44    ~v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl4_7 | ~spl4_27 | spl4_36)),
% 0.20/0.44    inference(subsumption_resolution,[],[f292,f312])).
% 0.20/0.44  fof(f312,plain,(
% 0.20/0.44    sK1 != k2_pre_topc(sK0,sK1) | spl4_36),
% 0.20/0.44    inference(avatar_component_clause,[],[f311])).
% 0.20/0.44  fof(f292,plain,(
% 0.20/0.44    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl4_7 | ~spl4_27)),
% 0.20/0.44    inference(resolution,[],[f110,f215])).
% 0.20/0.44  fof(f215,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) ) | ~spl4_27),
% 0.20/0.44    inference(avatar_component_clause,[],[f214])).
% 0.20/0.44  fof(f214,plain,(
% 0.20/0.44    spl4_27 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.44  fof(f299,plain,(
% 0.20/0.44    spl4_34),
% 0.20/0.44    inference(avatar_split_clause,[],[f64,f297])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,axiom,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 0.20/0.44  fof(f284,plain,(
% 0.20/0.44    ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7 | spl4_8 | ~spl4_9 | ~spl4_33),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f283])).
% 0.20/0.44  fof(f283,plain,(
% 0.20/0.44    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7 | spl4_8 | ~spl4_9 | ~spl4_33)),
% 0.20/0.44    inference(subsumption_resolution,[],[f110,f259])).
% 0.20/0.44  fof(f259,plain,(
% 0.20/0.44    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_8 | ~spl4_9 | ~spl4_33)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f85,f95,f90,f114,f119,f247])).
% 0.20/0.44  fof(f247,plain,(
% 0.20/0.44    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | v3_pre_topc(X2,X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl4_33),
% 0.20/0.44    inference(avatar_component_clause,[],[f246])).
% 0.20/0.44  fof(f246,plain,(
% 0.20/0.44    spl4_33 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.20/0.44  fof(f119,plain,(
% 0.20/0.44    v4_pre_topc(sK1,sK0) | ~spl4_9),
% 0.20/0.44    inference(avatar_component_clause,[],[f117])).
% 0.20/0.44  fof(f117,plain,(
% 0.20/0.44    spl4_9 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.44  fof(f114,plain,(
% 0.20/0.44    ~v3_pre_topc(sK1,sK0) | spl4_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f113])).
% 0.20/0.44  fof(f248,plain,(
% 0.20/0.44    spl4_33),
% 0.20/0.44    inference(avatar_split_clause,[],[f69,f246])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f45])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(rectify,[],[f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(nnf_transformation,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(flattening,[],[f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,axiom,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.20/0.44  fof(f244,plain,(
% 0.20/0.44    spl4_32),
% 0.20/0.44    inference(avatar_split_clause,[],[f65,f242])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f41])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ! [X0] : (((v3_tdlat_3(X0) | (~v4_pre_topc(sK2(X0),X0) & v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK2(X0),X0) & v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(rectify,[],[f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(nnf_transformation,[],[f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.44    inference(flattening,[],[f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,axiom,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v4_pre_topc(X1,X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).
% 0.20/0.44  fof(f240,plain,(
% 0.20/0.44    ~spl4_31 | ~spl4_6 | ~spl4_7 | ~spl4_26),
% 0.20/0.44    inference(avatar_split_clause,[],[f203,f196,f108,f103,f237])).
% 0.20/0.44  fof(f103,plain,(
% 0.20/0.44    spl4_6 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.44  fof(f196,plain,(
% 0.20/0.44    spl4_26 <=> ! [X1,X0] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.44  fof(f203,plain,(
% 0.20/0.44    ~v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl4_6 | ~spl4_7 | ~spl4_26)),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f105,f110,f197])).
% 0.20/0.44  fof(f197,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(k3_subset_1(X0,X1)) | ~v1_subset_1(X1,X0)) ) | ~spl4_26),
% 0.20/0.44    inference(avatar_component_clause,[],[f196])).
% 0.20/0.44  fof(f105,plain,(
% 0.20/0.44    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f103])).
% 0.20/0.44  fof(f220,plain,(
% 0.20/0.44    spl4_28),
% 0.20/0.44    inference(avatar_split_clause,[],[f61,f218])).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f37])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(nnf_transformation,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.20/0.44  fof(f216,plain,(
% 0.20/0.44    spl4_27),
% 0.20/0.44    inference(avatar_split_clause,[],[f59,f214])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(flattening,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.44  fof(f198,plain,(
% 0.20/0.44    spl4_26 | ~spl4_16),
% 0.20/0.44    inference(avatar_split_clause,[],[f151,f148,f196])).
% 0.20/0.44  fof(f148,plain,(
% 0.20/0.44    spl4_16 <=> ! [X1,X0] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.44  fof(f151,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) ) | ~spl4_16),
% 0.20/0.44    inference(subsumption_resolution,[],[f74,f149])).
% 0.20/0.44  fof(f149,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | ~v1_xboole_0(X0)) ) | ~spl4_16),
% 0.20/0.44    inference(avatar_component_clause,[],[f148])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.44    inference(flattening,[],[f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,axiom,(
% 0.20/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & v1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k3_subset_1(X0,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tex_2)).
% 0.20/0.44  fof(f179,plain,(
% 0.20/0.44    spl4_22),
% 0.20/0.44    inference(avatar_split_clause,[],[f73,f177])).
% 0.20/0.44  fof(f73,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.44  fof(f150,plain,(
% 0.20/0.44    spl4_16),
% 0.20/0.44    inference(avatar_split_clause,[],[f63,f148])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.20/0.44  fof(f146,plain,(
% 0.20/0.44    spl4_15 | ~spl4_12 | ~spl4_14),
% 0.20/0.44    inference(avatar_split_clause,[],[f142,f139,f131,f144])).
% 0.20/0.44  fof(f131,plain,(
% 0.20/0.44    spl4_12 <=> ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.44  fof(f139,plain,(
% 0.20/0.44    spl4_14 <=> ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.44  fof(f142,plain,(
% 0.20/0.44    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) ) | (~spl4_12 | ~spl4_14)),
% 0.20/0.44    inference(forward_demodulation,[],[f140,f132])).
% 0.20/0.44  fof(f132,plain,(
% 0.20/0.44    ( ! [X0] : (k2_subset_1(X0) = X0) ) | ~spl4_12),
% 0.20/0.44    inference(avatar_component_clause,[],[f131])).
% 0.20/0.44  fof(f140,plain,(
% 0.20/0.44    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) ) | ~spl4_14),
% 0.20/0.44    inference(avatar_component_clause,[],[f139])).
% 0.20/0.44  fof(f141,plain,(
% 0.20/0.44    spl4_14),
% 0.20/0.44    inference(avatar_split_clause,[],[f76,f139])).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.20/0.44    inference(forward_demodulation,[],[f58,f55])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.44  fof(f137,plain,(
% 0.20/0.44    spl4_13),
% 0.20/0.44    inference(avatar_split_clause,[],[f57,f135])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.44  fof(f133,plain,(
% 0.20/0.44    spl4_12),
% 0.20/0.44    inference(avatar_split_clause,[],[f56,f131])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.44  fof(f125,plain,(
% 0.20/0.44    spl4_10),
% 0.20/0.44    inference(avatar_split_clause,[],[f54,f122])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    v1_xboole_0(k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.44  fof(f120,plain,(
% 0.20/0.44    spl4_8 | spl4_9),
% 0.20/0.44    inference(avatar_split_clause,[],[f51,f117,f113])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    (v1_subset_1(sK1,u1_struct_0(sK0)) & v3_tex_2(sK1,sK0) & (v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f35,f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v1_subset_1(X1,u1_struct_0(sK0)) & v3_tex_2(X1,sK0) & (v4_pre_topc(X1,sK0) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ? [X1] : (v1_subset_1(X1,u1_struct_0(sK0)) & v3_tex_2(X1,sK0) & (v4_pre_topc(X1,sK0) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (v1_subset_1(sK1,u1_struct_0(sK0)) & v3_tex_2(sK1,sK0) & (v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,negated_conjecture,(
% 0.20/0.44    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.20/0.44    inference(negated_conjecture,[],[f15])).
% 0.20/0.44  fof(f15,conjecture,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).
% 0.20/0.44  fof(f111,plain,(
% 0.20/0.44    spl4_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f50,f108])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    inference(cnf_transformation,[],[f36])).
% 0.20/0.44  fof(f106,plain,(
% 0.20/0.44    spl4_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f53,f103])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.44    inference(cnf_transformation,[],[f36])).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    spl4_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f52,f98])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    v3_tex_2(sK1,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f36])).
% 0.20/0.44  fof(f96,plain,(
% 0.20/0.44    spl4_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f49,f93])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    l1_pre_topc(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f36])).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    spl4_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f48,f88])).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    v3_tdlat_3(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f36])).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f47,f83])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    v2_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f36])).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    ~spl4_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f46,f78])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ~v2_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f36])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (17138)------------------------------
% 0.20/0.45  % (17138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (17138)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (17138)Memory used [KB]: 6268
% 0.20/0.45  % (17138)Time elapsed: 0.023 s
% 0.20/0.45  % (17138)------------------------------
% 0.20/0.45  % (17138)------------------------------
% 0.20/0.45  % (17124)Success in time 0.09 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 342 expanded)
%              Number of leaves         :   26 ( 111 expanded)
%              Depth                    :   25
%              Number of atoms          : 1278 (3284 expanded)
%              Number of equality atoms :   10 (  99 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f59,f63,f67,f71,f75,f79,f83,f87,f95,f99,f103,f107,f164,f172,f180,f184,f192,f199,f205,f215,f260,f280])).

fof(f280,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f278,f195])).

fof(f195,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl7_24
  <=> r1_tmap_1(sK3,sK0,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f278,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f277,f66])).

fof(f66,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl7_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f277,plain,
    ( v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f276,f171])).

fof(f171,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl7_18
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f276,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f275,f163])).

fof(f163,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl7_16
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f275,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f274,f98])).

fof(f98,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_12
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f274,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f273,f214])).

fof(f214,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl7_26
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f273,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f272,f191])).

fof(f191,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl7_23
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f272,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f271,f179])).

fof(f179,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl7_20
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f271,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f270,f54])).

fof(f54,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f270,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f269,f102])).

fof(f102,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl7_13
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f269,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f268,f58])).

fof(f58,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl7_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f268,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f267,f106])).

fof(f106,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_14
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f267,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f266,f62])).

fof(f62,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f266,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f265,f86])).

fof(f86,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f264,f82])).

fof(f82,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f264,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f263,f78])).

fof(f78,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f263,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f262,f74])).

fof(f74,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl7_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f262,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_5
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f261,f70])).

fof(f70,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f261,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_25 ),
    inference(resolution,[],[f201,f48])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | v2_struct_0(X0)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f201,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl7_25
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f260,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_24
    | spl7_25
    | ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_24
    | spl7_25
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f258,f163])).

fof(f258,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_24
    | spl7_25
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f257,f198])).

fof(f198,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f197])).

fof(f257,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f256,f171])).

fof(f256,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_24
    | ~ spl7_26 ),
    inference(resolution,[],[f255,f204])).

fof(f204,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK3,sK0,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f254,f98])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
        | ~ r1_tmap_1(sK3,sK0,sK4,X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f253,f214])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
        | ~ r1_tmap_1(sK3,sK0,sK4,X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f252,f78])).

fof(f252,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
        | ~ r1_tmap_1(sK3,sK0,sK4,X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_20
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f251,f179])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
        | ~ r1_tmap_1(sK3,sK0,sK4,X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f250,f54])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
        | ~ r1_tmap_1(sK3,sK0,sK4,X0) )
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f249,f102])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
        | ~ r1_tmap_1(sK3,sK0,sK4,X0) )
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f248,f58])).

fof(f248,plain,
    ( ! [X0] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
        | ~ r1_tmap_1(sK3,sK0,sK4,X0) )
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f247,f86])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
        | ~ r1_tmap_1(sK3,sK0,sK4,X0) )
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f246,f82])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0)
        | ~ r1_tmap_1(sK3,sK0,sK4,X0) )
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(resolution,[],[f152,f191])).

fof(f152,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | r1_tmap_1(sK2,X0,k3_tmap_1(sK1,X0,X1,sK2,X2),X3)
        | ~ r1_tmap_1(X1,X0,X2,X3) )
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f151,f66])).

fof(f151,plain,
    ( ! [X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | r1_tmap_1(sK2,X0,k3_tmap_1(sK1,X0,X1,sK2,X2),X3)
        | ~ r1_tmap_1(X1,X0,X2,X3) )
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f150,f62])).

fof(f150,plain,
    ( ! [X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK2)
        | v2_struct_0(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | r1_tmap_1(sK2,X0,k3_tmap_1(sK1,X0,X1,sK2,X2),X3)
        | ~ r1_tmap_1(X1,X0,X2,X3) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f149,f74])).

fof(f149,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK2)
        | v2_struct_0(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | r1_tmap_1(sK2,X0,k3_tmap_1(sK1,X0,X1,sK2,X2),X3)
        | ~ r1_tmap_1(X1,X0,X2,X3) )
    | ~ spl7_5
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f146,f70])).

fof(f146,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK2)
        | v2_struct_0(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | r1_tmap_1(sK2,X0,k3_tmap_1(sK1,X0,X1,sK2,X2),X3)
        | ~ r1_tmap_1(X1,X0,X2,X3) )
    | ~ spl7_14 ),
    inference(resolution,[],[f106,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | v2_struct_0(X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ r1_tmap_1(X3,X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f13])).

% (32711)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (32709)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (32720)Refutation not found, incomplete strategy% (32720)------------------------------
% (32720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32720)Termination reason: Refutation not found, incomplete strategy

% (32720)Memory used [KB]: 10618
% (32720)Time elapsed: 0.080 s
% (32720)------------------------------
% (32720)------------------------------
% (32714)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (32707)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (32715)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (32703)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (32713)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (32702)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (32713)Refutation not found, incomplete strategy% (32713)------------------------------
% (32713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32713)Termination reason: Refutation not found, incomplete strategy

% (32713)Memory used [KB]: 1663
% (32713)Time elapsed: 0.093 s
% (32713)------------------------------
% (32713)------------------------------
fof(f215,plain,
    ( spl7_26
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f209,f182,f105,f101,f93,f73,f69,f65,f57,f213])).

fof(f93,plain,
    ( spl7_11
  <=> v1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f182,plain,
    ( spl7_21
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f209,plain,
    ( v1_tsep_1(sK2,sK3)
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f208,f58])).

fof(f208,plain,
    ( v2_struct_0(sK3)
    | v1_tsep_1(sK2,sK3)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f206,f102])).

fof(f206,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | v1_tsep_1(sK2,sK3)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_21 ),
    inference(resolution,[],[f113,f183])).

fof(f183,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | v1_tsep_1(sK2,X0) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f112,f106])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | v1_tsep_1(sK2,X0) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f111,f66])).

fof(f111,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | v1_tsep_1(sK2,X0) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f110,f74])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | v1_tsep_1(sK2,X0) )
    | ~ spl7_5
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f108,f70])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | v1_tsep_1(sK2,X0) )
    | ~ spl7_11 ),
    inference(resolution,[],[f94,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | v1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f94,plain,
    ( v1_tsep_1(sK2,sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f205,plain,
    ( spl7_24
    | spl7_25 ),
    inference(avatar_split_clause,[],[f203,f197,f194])).

fof(f203,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f51,f198])).

fof(f51,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(forward_demodulation,[],[f18,f21])).

fof(f21,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & m1_pre_topc(X2,X1)
                            & v1_tsep_1(X2,X1) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X0,X4,X5)
                                    <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).

fof(f18,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f199,plain,
    ( ~ spl7_24
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f50,f197,f194])).

fof(f50,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(forward_demodulation,[],[f19,f21])).

fof(f19,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f192,plain,(
    spl7_23 ),
    inference(avatar_split_clause,[],[f25,f190])).

fof(f25,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f184,plain,
    ( spl7_21
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f135,f101,f97,f73,f182])).

fof(f135,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f118,f131])).

fof(f131,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f127,f74])).

fof(f127,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3)
    | ~ spl7_13 ),
    inference(resolution,[],[f102,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f118,plain,
    ( ~ l1_pre_topc(sK3)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_12 ),
    inference(resolution,[],[f98,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f180,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f24,f178])).

fof(f24,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f172,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f49,f170])).

fof(f49,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f20,f21])).

fof(f20,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f164,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f22,f162])).

fof(f22,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f107,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f32,f105])).

fof(f32,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f103,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f30,f101])).

fof(f30,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f28,f97])).

fof(f28,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f26,f93])).

fof(f26,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f87,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f83,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f37,f81])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f79,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f33,f65])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (32704)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (32720)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (32706)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (32712)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (32700)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (32719)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (32700)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f55,f59,f63,f67,f71,f75,f79,f83,f87,f95,f99,f103,f107,f164,f172,f180,f184,f192,f199,f205,f215,f260,f280])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_20 | ~spl7_23 | spl7_24 | ~spl7_25 | ~spl7_26),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f279])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    $false | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_20 | ~spl7_23 | spl7_24 | ~spl7_25 | ~spl7_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f278,f195])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ~r1_tmap_1(sK3,sK0,sK4,sK5) | spl7_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f194])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    spl7_24 <=> r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_20 | ~spl7_23 | ~spl7_25 | ~spl7_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f277,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ~v2_struct_0(sK1) | spl7_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl7_4 <=> v2_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_20 | ~spl7_23 | ~spl7_25 | ~spl7_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f276,f171])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl7_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f170])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl7_18 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_20 | ~spl7_23 | ~spl7_25 | ~spl7_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f275,f163])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl7_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    spl7_16 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_20 | ~spl7_23 | ~spl7_25 | ~spl7_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f274,f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK3) | ~spl7_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl7_12 <=> m1_pre_topc(sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_20 | ~spl7_23 | ~spl7_25 | ~spl7_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f273,f214])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    v1_tsep_1(sK2,sK3) | ~spl7_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f213])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    spl7_26 <=> v1_tsep_1(sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_20 | ~spl7_23 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f272,f191])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~spl7_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f190])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    spl7_23 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_20 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f271,f179])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~spl7_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f178])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    spl7_20 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f270,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    v1_funct_1(sK4) | ~spl7_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl7_1 <=> v1_funct_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f269,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    m1_pre_topc(sK3,sK1) | ~spl7_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl7_13 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_14 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f268,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ~v2_struct_0(sK3) | spl7_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl7_2 <=> v2_struct_0(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_14 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f267,f106])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK1) | ~spl7_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl7_14 <=> m1_pre_topc(sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f266,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ~v2_struct_0(sK2) | spl7_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl7_3 <=> v2_struct_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f265,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl7_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl7_9 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f264,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl7_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl7_8 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f263,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~v2_struct_0(sK0) | spl7_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl7_7 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_6 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f262,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    l1_pre_topc(sK1) | ~spl7_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl7_6 <=> l1_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f261,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    v2_pre_topc(sK1) | ~spl7_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl7_5 <=> v2_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | ~spl7_25),
% 0.21/0.49    inference(resolution,[],[f201,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | v2_struct_0(X0) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.21/0.49    inference(equality_resolution,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~spl7_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f197])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    spl7_25 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_20 | ~spl7_23 | ~spl7_24 | spl7_25 | ~spl7_26),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f259])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    $false | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_20 | ~spl7_23 | ~spl7_24 | spl7_25 | ~spl7_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f258,f163])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_18 | ~spl7_20 | ~spl7_23 | ~spl7_24 | spl7_25 | ~spl7_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f257,f198])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | spl7_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f197])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_18 | ~spl7_20 | ~spl7_23 | ~spl7_24 | ~spl7_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f256,f171])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_20 | ~spl7_23 | ~spl7_24 | ~spl7_26)),
% 0.21/0.49    inference(resolution,[],[f255,f204])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    r1_tmap_1(sK3,sK0,sK4,sK5) | ~spl7_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f194])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_20 | ~spl7_23 | ~spl7_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f254,f98])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | ~r1_tmap_1(sK3,sK0,sK4,X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_20 | ~spl7_23 | ~spl7_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f253,f214])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | ~r1_tmap_1(sK3,sK0,sK4,X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_20 | ~spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f252,f78])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | ~r1_tmap_1(sK3,sK0,sK4,X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_20 | ~spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f251,f179])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | ~r1_tmap_1(sK3,sK0,sK4,X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f250,f54])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | ~r1_tmap_1(sK3,sK0,sK4,X0)) ) | (spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f249,f102])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | ~r1_tmap_1(sK3,sK0,sK4,X0)) ) | (spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_14 | ~spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f248,f58])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    ( ! [X0] : (v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | ~r1_tmap_1(sK3,sK0,sK4,X0)) ) | (spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_14 | ~spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f247,f86])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | ~r1_tmap_1(sK3,sK0,sK4,X0)) ) | (spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_14 | ~spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f246,f82])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X0) | ~r1_tmap_1(sK3,sK0,sK4,X0)) ) | (spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_14 | ~spl7_23)),
% 0.21/0.49    inference(resolution,[],[f152,f191])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | v2_struct_0(X0) | ~v1_tsep_1(sK2,X1) | ~m1_pre_topc(sK2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK2)) | r1_tmap_1(sK2,X0,k3_tmap_1(sK1,X0,X1,sK2,X2),X3) | ~r1_tmap_1(X1,X0,X2,X3)) ) | (spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f151,f66])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_tsep_1(sK2,X1) | ~m1_pre_topc(sK2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK2)) | r1_tmap_1(sK2,X0,k3_tmap_1(sK1,X0,X1,sK2,X2),X3) | ~r1_tmap_1(X1,X0,X2,X3)) ) | (spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f150,f62])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK2) | v2_struct_0(sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_tsep_1(sK2,X1) | ~m1_pre_topc(sK2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK2)) | r1_tmap_1(sK2,X0,k3_tmap_1(sK1,X0,X1,sK2,X2),X3) | ~r1_tmap_1(X1,X0,X2,X3)) ) | (~spl7_5 | ~spl7_6 | ~spl7_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f149,f74])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(sK1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK2) | v2_struct_0(sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_tsep_1(sK2,X1) | ~m1_pre_topc(sK2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK2)) | r1_tmap_1(sK2,X0,k3_tmap_1(sK1,X0,X1,sK2,X2),X3) | ~r1_tmap_1(X1,X0,X2,X3)) ) | (~spl7_5 | ~spl7_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f146,f70])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK2) | v2_struct_0(sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_tsep_1(sK2,X1) | ~m1_pre_topc(sK2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK2)) | r1_tmap_1(sK2,X0,k3_tmap_1(sK1,X0,X1,sK2,X2),X3) | ~r1_tmap_1(X1,X0,X2,X3)) ) | ~spl7_14),
% 0.21/0.49    inference(resolution,[],[f106,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X6)) )),
% 0.21/0.49    inference(equality_resolution,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  % (32711)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (32709)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (32720)Refutation not found, incomplete strategy% (32720)------------------------------
% 0.21/0.49  % (32720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32720)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32720)Memory used [KB]: 10618
% 0.21/0.49  % (32720)Time elapsed: 0.080 s
% 0.21/0.49  % (32720)------------------------------
% 0.21/0.49  % (32720)------------------------------
% 0.21/0.49  % (32714)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (32707)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (32715)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (32703)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (32713)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (32702)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (32713)Refutation not found, incomplete strategy% (32713)------------------------------
% 0.21/0.50  % (32713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32713)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32713)Memory used [KB]: 1663
% 0.21/0.50  % (32713)Time elapsed: 0.093 s
% 0.21/0.50  % (32713)------------------------------
% 0.21/0.50  % (32713)------------------------------
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    spl7_26 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f209,f182,f105,f101,f93,f73,f69,f65,f57,f213])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl7_11 <=> v1_tsep_1(sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    spl7_21 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    v1_tsep_1(sK2,sK3) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f208,f58])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    v2_struct_0(sK3) | v1_tsep_1(sK2,sK3) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f206,f102])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | v1_tsep_1(sK2,sK3) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_14 | ~spl7_21)),
% 0.21/0.51    inference(resolution,[],[f113,f183])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl7_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f182])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | v1_tsep_1(sK2,X0)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f112,f106])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f66])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | (~spl7_5 | ~spl7_6 | ~spl7_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f110,f74])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | (~spl7_5 | ~spl7_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f108,f70])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | ~spl7_11),
% 0.21/0.51    inference(resolution,[],[f94,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_tsep_1(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    v1_tsep_1(sK2,sK1) | ~spl7_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f93])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    spl7_24 | spl7_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f203,f197,f194])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    r1_tmap_1(sK3,sK0,sK4,sK5) | spl7_25),
% 0.21/0.51    inference(subsumption_resolution,[],[f51,f198])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.51    inference(forward_demodulation,[],[f18,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    sK5 = sK6),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    ~spl7_24 | ~spl7_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f197,f194])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.51    inference(forward_demodulation,[],[f19,f21])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    spl7_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f25,f190])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    spl7_21 | ~spl7_6 | ~spl7_12 | ~spl7_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f135,f101,f97,f73,f182])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | (~spl7_6 | ~spl7_12 | ~spl7_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f118,f131])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    l1_pre_topc(sK3) | (~spl7_6 | ~spl7_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f74])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | l1_pre_topc(sK3) | ~spl7_13),
% 0.21/0.51    inference(resolution,[],[f102,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ~l1_pre_topc(sK3) | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl7_12),
% 0.21/0.51    inference(resolution,[],[f98,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    spl7_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f178])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    spl7_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f170])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.51    inference(forward_demodulation,[],[f20,f21])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    spl7_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f22,f162])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl7_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f105])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl7_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f101])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    m1_pre_topc(sK3,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl7_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f97])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl7_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f93])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    v1_tsep_1(sK2,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl7_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f85])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl7_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f81])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ~spl7_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f77])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl7_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f73])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    l1_pre_topc(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f69])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    v2_pre_topc(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ~spl7_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f65])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ~spl7_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f61])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ~v2_struct_0(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ~spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f57])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ~v2_struct_0(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl7_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f23,f53])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    v1_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (32700)------------------------------
% 0.21/0.51  % (32700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32700)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (32700)Memory used [KB]: 6396
% 0.21/0.51  % (32700)Time elapsed: 0.077 s
% 0.21/0.51  % (32700)------------------------------
% 0.21/0.51  % (32700)------------------------------
% 0.21/0.51  % (32696)Success in time 0.149 s
%------------------------------------------------------------------------------

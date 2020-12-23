%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1776+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:31 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 351 expanded)
%              Number of leaves         :   28 ( 116 expanded)
%              Depth                    :   25
%              Number of atoms          : 1331 (3192 expanded)
%              Number of equality atoms :   12 (  98 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f72,f77,f82,f87,f92,f97,f107,f112,f113,f124,f129,f135,f140,f145,f156,f166,f194,f207,f214,f228,f240])).

fof(f240,plain,
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
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | spl7_21
    | ~ spl7_25 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
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
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | spl7_21
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f238,f56])).

fof(f56,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl7_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f238,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_1
    | spl7_2
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
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | spl7_21
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f237,f139])).

fof(f139,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl7_18
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f237,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ spl7_1
    | spl7_2
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
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | spl7_21
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f236,f106])).

fof(f106,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_13
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f236,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | spl7_21
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f235,f190])).

fof(f190,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl7_25
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f235,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | spl7_21 ),
    inference(subsumption_resolution,[],[f234,f101])).

fof(f101,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f99])).

% (20863)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f99,plain,
    ( spl7_12
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f234,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | spl7_21 ),
    inference(resolution,[],[f233,f154])).

fof(f154,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl7_21
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f233,plain,
    ( ! [X0] :
        ( r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),sK5)
        | ~ m1_pre_topc(X0,sK1)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f232,f66])).

fof(f66,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl7_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f232,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),sK5)
        | ~ v2_pre_topc(sK1) )
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f231,f61])).

fof(f61,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f231,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(sK1)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),sK5)
        | ~ v2_pre_topc(sK1) )
    | ~ spl7_1
    | spl7_2
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f230,f71])).

fof(f71,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f230,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),sK5)
        | ~ v2_pre_topc(sK1) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(resolution,[],[f226,f111])).

fof(f111,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_14
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f225,f128])).

fof(f128,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_16
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f224,f144])).

fof(f144,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl7_19
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f224,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f223,f134])).

fof(f134,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_17
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f222,f51])).

fof(f51,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl7_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f221,f86])).

fof(f86,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_8
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f220,f81])).

fof(f81,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f219,f76])).

fof(f76,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_1
    | ~ spl7_20 ),
    inference(resolution,[],[f151,f115])).

fof(f115,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ r1_tmap_1(X8,X6,sK4,X9)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X5)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X5)
        | v2_struct_0(X5)
        | ~ v1_funct_2(sK4,u1_struct_0(X8),u1_struct_0(X6))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6))))
        | ~ v1_tsep_1(X7,X8)
        | ~ m1_pre_topc(X7,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | r1_tmap_1(X7,X6,k3_tmap_1(X5,X6,X8,X7,sK4),X9)
        | ~ v2_pre_topc(X5) )
    | ~ spl7_1 ),
    inference(resolution,[],[f46,f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f3])).

% (20859)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f46,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f151,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl7_20
  <=> r1_tmap_1(sK3,sK0,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f228,plain,
    ( ~ spl7_10
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f215,f151])).

fof(f215,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_10
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f147,f155])).

fof(f155,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f153])).

fof(f147,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f15,f91])).

fof(f91,plain,
    ( sK5 = sK6
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_10
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f15,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).

fof(f214,plain,
    ( spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f212,f71])).

fof(f212,plain,
    ( ~ l1_pre_topc(sK1)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f211,f96])).

fof(f96,plain,
    ( v1_tsep_1(sK2,sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl7_11
  <=> v1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f211,plain,
    ( ~ v1_tsep_1(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f210,f101])).

fof(f210,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f209,f66])).

fof(f209,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | spl7_4
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f208,f61])).

fof(f208,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(resolution,[],[f193,f111])).

fof(f193,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_tsep_1(sK2,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl7_26
  <=> ! [X1] :
        ( ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_tsep_1(sK2,X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f207,plain,
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
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | spl7_20
    | ~ spl7_21
    | ~ spl7_25 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
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
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | spl7_20
    | ~ spl7_21
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f205,f111])).

fof(f205,plain,
    ( ~ m1_pre_topc(sK3,sK1)
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
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | spl7_20
    | ~ spl7_21
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f204,f101])).

fof(f204,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
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
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | spl7_20
    | ~ spl7_21
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f203,f71])).

fof(f203,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | spl7_20
    | ~ spl7_21
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f202,f66])).

fof(f202,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | spl7_20
    | ~ spl7_21
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f201,f61])).

fof(f201,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | spl7_20
    | ~ spl7_21
    | ~ spl7_25 ),
    inference(resolution,[],[f200,f155])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK5)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f199,f150])).

fof(f150,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f149])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK5)
        | r1_tmap_1(sK3,sK0,sK4,sK5) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f198,f139])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK5)
        | r1_tmap_1(sK3,sK0,sK4,sK5) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_25 ),
    inference(resolution,[],[f197,f128])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),X1)
        | r1_tmap_1(sK3,sK0,sK4,X1) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f196,f106])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),X1)
        | r1_tmap_1(sK3,sK0,sK4,X1) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f195,f56])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),X1)
        | r1_tmap_1(sK3,sK0,sK4,X1) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_25 ),
    inference(resolution,[],[f190,f172])).

fof(f172,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_tsep_1(X1,sK3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK0,sK4,X2) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f171,f134])).

fof(f171,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK0,sK4,X2) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f170,f51])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK0,sK4,X2) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f169,f86])).

fof(f169,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK0,sK4,X2) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f168,f81])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK0,sK4,X2) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f167,f76])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK0,sK4,X2) )
    | ~ spl7_1
    | ~ spl7_19 ),
    inference(resolution,[],[f114,f144])).

fof(f114,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X2,X3)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4) )
    | ~ spl7_1 ),
    inference(resolution,[],[f46,f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f9])).

fof(f194,plain,
    ( spl7_25
    | spl7_26
    | spl7_2
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f176,f163,f49,f192,f188])).

fof(f163,plain,
    ( spl7_22
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f176,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | v1_tsep_1(sK2,sK3) )
    | spl7_2
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f174,f51])).

fof(f174,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | v1_tsep_1(sK2,sK3) )
    | ~ spl7_22 ),
    inference(resolution,[],[f165,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | v1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f165,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f163])).

fof(f166,plain,
    ( spl7_22
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f161,f109,f104,f99,f69,f64,f163])).

fof(f161,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f160,f111])).

fof(f160,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(resolution,[],[f157,f106])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X0,sK1)
        | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(resolution,[],[f117,f101])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_pre_topc(X0,X1)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f116,f66])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X1,sK1)
        | ~ m1_pre_topc(X0,X1)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f156,plain,
    ( spl7_20
    | spl7_21
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f146,f89,f153,f149])).

fof(f146,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f14,f91])).

fof(f14,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f145,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f21,f142])).

fof(f21,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f140,plain,
    ( spl7_18
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f130,f121,f89,f137])).

fof(f121,plain,
    ( spl7_15
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f130,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f123,f91])).

fof(f123,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f121])).

fof(f135,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f20,f132])).

fof(f20,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f129,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f18,f126])).

fof(f18,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f124,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f16,f121])).

fof(f16,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f113,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f28,f99])).

fof(f28,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f112,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f26,f109])).

fof(f26,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f107,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f24,f104])).

fof(f24,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f97,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f22,f94])).

fof(f22,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f92,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f17,f89])).

fof(f17,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f34,f84])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f82,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f33,f79])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

% (20855)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f77,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f32,f74])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f67,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f30,f64])).

fof(f30,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f57,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f27,f54])).

fof(f27,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f47,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------

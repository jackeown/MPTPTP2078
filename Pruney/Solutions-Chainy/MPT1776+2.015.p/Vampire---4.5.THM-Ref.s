%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 365 expanded)
%              Number of leaves         :   30 ( 128 expanded)
%              Depth                    :   25
%              Number of atoms          : 1304 (3278 expanded)
%              Number of equality atoms :   13 (  99 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f67,f71,f75,f79,f83,f87,f91,f95,f103,f107,f111,f115,f183,f191,f195,f199,f203,f216,f231,f259,f283,f303])).

fof(f303,plain,
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
    | ~ spl7_19
    | ~ spl7_21
    | spl7_23
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
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
    | ~ spl7_19
    | ~ spl7_21
    | spl7_23
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f301,f212])).

% (22517)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (22521)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (22519)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f212,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl7_23
  <=> r1_tmap_1(sK3,sK0,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

% (22511)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f301,plain,
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
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f300,f74])).

fof(f74,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl7_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f300,plain,
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
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f299,f190])).

fof(f190,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl7_18
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f299,plain,
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
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f298,f182])).

fof(f182,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_16
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f298,plain,
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
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f297,f106])).

fof(f106,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_12
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f297,plain,
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
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f296,f258])).

fof(f258,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl7_32
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f296,plain,
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
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f295,f202])).

fof(f202,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl7_21
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f295,plain,
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
    | ~ spl7_19
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f294,f194])).

fof(f194,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl7_19
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f294,plain,
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
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f293,f62])).

fof(f62,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f293,plain,
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
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f292,f110])).

fof(f110,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_13
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f292,plain,
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
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f291,f66])).

fof(f66,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl7_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f291,plain,
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
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f290,f114])).

fof(f114,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_14
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f290,plain,
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
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f289,f70])).

fof(f70,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f289,plain,
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
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f288,f94])).

fof(f94,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f288,plain,
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
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f287,f90])).

fof(f90,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f287,plain,
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
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f286,f86])).

fof(f86,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f286,plain,
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
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f285,f82])).

fof(f82,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f285,plain,
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
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f284,f78])).

fof(f78,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f284,plain,
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
    | ~ spl7_24 ),
    inference(resolution,[],[f218,f56])).

fof(f56,plain,(
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
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f218,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl7_24
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f283,plain,
    ( spl7_24
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
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f282,f201,f193,f189,f181,f109,f105,f93,f89,f85,f81,f77,f73,f69,f65,f61,f214])).

fof(f282,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
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
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f59,f278])).

fof(f278,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
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
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f277,f106])).

fof(f277,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
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
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f276,f70])).

fof(f276,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f272,f182])).

fof(f272,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(resolution,[],[f268,f190])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X1)
        | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) )
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f267,f86])).

fof(f267,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X1)
        | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) )
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f266,f194])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X1)
        | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) )
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f265,f62])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X1)
        | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f264,f94])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X1)
        | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_13
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f263,f90])).

fof(f263,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(sK3,sK0,sK4,X1)
        | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_21 ),
    inference(resolution,[],[f158,f202])).

fof(f158,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5))))
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ m1_subset_1(X8,u1_struct_0(sK3))
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_pre_topc(X6,sK3)
        | ~ r1_tmap_1(sK3,X5,X7,X8)
        | r1_tmap_1(X6,X5,k3_tmap_1(sK1,X5,sK3,X6,X7),X8) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f157,f148])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | m1_pre_topc(X0,sK1) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f147,f78])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK3)
        | m1_pre_topc(X0,sK1) )
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f137,f82])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK3)
        | m1_pre_topc(X0,sK1) )
    | ~ spl7_13 ),
    inference(resolution,[],[f110,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f157,plain,
    ( ! [X6,X8,X7,X5] :
        ( v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK1)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5))))
        | ~ m1_subset_1(X8,u1_struct_0(sK3))
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_pre_topc(X6,sK3)
        | ~ r1_tmap_1(sK3,X5,X7,X8)
        | r1_tmap_1(X6,X5,k3_tmap_1(sK1,X5,sK3,X6,X7),X8) )
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f156,f74])).

fof(f156,plain,
    ( ! [X6,X8,X7,X5] :
        ( v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK1)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK1)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5))))
        | ~ m1_subset_1(X8,u1_struct_0(sK3))
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_pre_topc(X6,sK3)
        | ~ r1_tmap_1(sK3,X5,X7,X8)
        | r1_tmap_1(X6,X5,k3_tmap_1(sK1,X5,sK3,X6,X7),X8) )
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f155,f66])).

fof(f155,plain,
    ( ! [X6,X8,X7,X5] :
        ( v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK3)
        | v2_struct_0(sK1)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK1)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5))))
        | ~ m1_subset_1(X8,u1_struct_0(sK3))
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_pre_topc(X6,sK3)
        | ~ r1_tmap_1(sK3,X5,X7,X8)
        | r1_tmap_1(X6,X5,k3_tmap_1(sK1,X5,sK3,X6,X7),X8) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f154,f82])).

fof(f154,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK3)
        | v2_struct_0(sK1)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK1)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5))))
        | ~ m1_subset_1(X8,u1_struct_0(sK3))
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_pre_topc(X6,sK3)
        | ~ r1_tmap_1(sK3,X5,X7,X8)
        | r1_tmap_1(X6,X5,k3_tmap_1(sK1,X5,sK3,X6,X7),X8) )
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f140,f78])).

fof(f140,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK3)
        | v2_struct_0(sK1)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK1)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5))))
        | ~ m1_subset_1(X8,u1_struct_0(sK3))
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_pre_topc(X6,sK3)
        | ~ r1_tmap_1(sK3,X5,X7,X8)
        | r1_tmap_1(X6,X5,k3_tmap_1(sK1,X5,sK3,X6,X7),X8) )
    | ~ spl7_13 ),
    inference(resolution,[],[f110,f54])).

fof(f54,plain,(
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
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
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
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | X5 != X6
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f59,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(forward_demodulation,[],[f24,f27])).

fof(f27,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f24,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f12])).

fof(f259,plain,
    ( spl7_32
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f255,f229,f113,f109,f101,f81,f77,f73,f65,f257])).

fof(f101,plain,
    ( spl7_11
  <=> v1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f229,plain,
    ( spl7_26
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f255,plain,
    ( v1_tsep_1(sK2,sK3)
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f254,f66])).

fof(f254,plain,
    ( v2_struct_0(sK3)
    | v1_tsep_1(sK2,sK3)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f253,f110])).

fof(f253,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | v1_tsep_1(sK2,sK3)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(resolution,[],[f121,f230])).

fof(f230,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f229])).

fof(f121,plain,
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
    inference(subsumption_resolution,[],[f120,f114])).

fof(f120,plain,
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
    inference(subsumption_resolution,[],[f119,f74])).

fof(f119,plain,
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
    inference(subsumption_resolution,[],[f118,f82])).

fof(f118,plain,
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
    inference(subsumption_resolution,[],[f116,f78])).

fof(f116,plain,
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
    inference(resolution,[],[f102,f48])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f102,plain,
    ( v1_tsep_1(sK2,sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f231,plain,
    ( spl7_26
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f227,f197,f229])).

fof(f197,plain,
    ( spl7_20
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f227,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_20 ),
    inference(resolution,[],[f198,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f198,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f216,plain,
    ( ~ spl7_23
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f58,f214,f211])).

fof(f58,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(forward_demodulation,[],[f25,f27])).

fof(f25,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f12])).

fof(f203,plain,(
    spl7_21 ),
    inference(avatar_split_clause,[],[f31,f201])).

fof(f31,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f199,plain,
    ( spl7_20
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f144,f109,f105,f81,f197])).

fof(f144,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f128,f141])).

fof(f141,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f136,f82])).

fof(f136,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3)
    | ~ spl7_13 ),
    inference(resolution,[],[f110,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f128,plain,
    ( ~ l1_pre_topc(sK3)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl7_12 ),
    inference(resolution,[],[f106,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f195,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f30,f193])).

fof(f30,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f191,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f57,f189])).

fof(f57,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f26,f27])).

fof(f26,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f183,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f28,f181])).

fof(f28,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f115,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f38,f113])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f111,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f36,f109])).

fof(f36,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f107,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f34,f105])).

fof(f34,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f103,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f32,f101])).

fof(f32,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f95,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f44,f93])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f43,f89])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f87,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f42,f85])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f41,f81])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f39,f73])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f37,f69])).

fof(f37,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f35,f65])).

fof(f35,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (22514)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (22523)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (22522)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (22509)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (22512)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (22509)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f304,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f63,f67,f71,f75,f79,f83,f87,f91,f95,f103,f107,f111,f115,f183,f191,f195,f199,f203,f216,f231,f259,f283,f303])).
% 0.20/0.49  fof(f303,plain,(
% 0.20/0.49    ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | spl7_23 | ~spl7_24 | ~spl7_32),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f302])).
% 0.20/0.49  fof(f302,plain,(
% 0.20/0.49    $false | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | spl7_23 | ~spl7_24 | ~spl7_32)),
% 0.20/0.49    inference(subsumption_resolution,[],[f301,f212])).
% 0.20/0.49  % (22517)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (22521)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (22519)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    ~r1_tmap_1(sK3,sK0,sK4,sK5) | spl7_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f211])).
% 0.20/0.49  fof(f211,plain,(
% 0.20/0.49    spl7_23 <=> r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.49  % (22511)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  fof(f301,plain,(
% 0.20/0.49    r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_24 | ~spl7_32)),
% 0.20/0.49    inference(subsumption_resolution,[],[f300,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ~v2_struct_0(sK1) | spl7_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    spl7_4 <=> v2_struct_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.49  fof(f300,plain,(
% 0.20/0.49    v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_24 | ~spl7_32)),
% 0.20/0.49    inference(subsumption_resolution,[],[f299,f190])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl7_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f189])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    spl7_18 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_19 | ~spl7_21 | ~spl7_24 | ~spl7_32)),
% 0.20/0.49    inference(subsumption_resolution,[],[f298,f182])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl7_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f181])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    spl7_16 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.49  fof(f298,plain,(
% 0.20/0.49    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_19 | ~spl7_21 | ~spl7_24 | ~spl7_32)),
% 0.20/0.49    inference(subsumption_resolution,[],[f297,f106])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    m1_pre_topc(sK2,sK3) | ~spl7_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f105])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl7_12 <=> m1_pre_topc(sK2,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.49  fof(f297,plain,(
% 0.20/0.49    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_19 | ~spl7_21 | ~spl7_24 | ~spl7_32)),
% 0.20/0.49    inference(subsumption_resolution,[],[f296,f258])).
% 0.20/0.49  fof(f258,plain,(
% 0.20/0.49    v1_tsep_1(sK2,sK3) | ~spl7_32),
% 0.20/0.49    inference(avatar_component_clause,[],[f257])).
% 0.20/0.49  fof(f257,plain,(
% 0.20/0.49    spl7_32 <=> v1_tsep_1(sK2,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.20/0.49  fof(f296,plain,(
% 0.20/0.49    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_19 | ~spl7_21 | ~spl7_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f295,f202])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~spl7_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f201])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    spl7_21 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.20/0.49  fof(f295,plain,(
% 0.20/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_19 | ~spl7_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f294,f194])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~spl7_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f193])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    spl7_19 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.49  fof(f294,plain,(
% 0.20/0.49    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f293,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    v1_funct_1(sK4) | ~spl7_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    spl7_1 <=> v1_funct_1(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.49  fof(f293,plain,(
% 0.20/0.49    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f292,f110])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    m1_pre_topc(sK3,sK1) | ~spl7_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f109])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    spl7_13 <=> m1_pre_topc(sK3,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.49  fof(f292,plain,(
% 0.20/0.49    ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_14 | ~spl7_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f291,f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ~v2_struct_0(sK3) | spl7_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl7_2 <=> v2_struct_0(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.49  fof(f291,plain,(
% 0.20/0.49    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_14 | ~spl7_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f290,f114])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    m1_pre_topc(sK2,sK1) | ~spl7_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f113])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    spl7_14 <=> m1_pre_topc(sK2,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.49  fof(f290,plain,(
% 0.20/0.49    ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f289,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ~v2_struct_0(sK2) | spl7_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl7_3 <=> v2_struct_0(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.49  fof(f289,plain,(
% 0.20/0.49    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f288,f94])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    l1_pre_topc(sK0) | ~spl7_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    spl7_9 <=> l1_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.49  fof(f288,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f287,f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    v2_pre_topc(sK0) | ~spl7_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl7_8 <=> v2_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.49  fof(f287,plain,(
% 0.20/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f286,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ~v2_struct_0(sK0) | spl7_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl7_7 <=> v2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.49  fof(f286,plain,(
% 0.20/0.49    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_6 | ~spl7_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f285,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    l1_pre_topc(sK1) | ~spl7_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl7_6 <=> l1_pre_topc(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.49  fof(f285,plain,(
% 0.20/0.49    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_24)),
% 0.20/0.49    inference(subsumption_resolution,[],[f284,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    v2_pre_topc(sK1) | ~spl7_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl7_5 <=> v2_pre_topc(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.49  fof(f284,plain,(
% 0.20/0.49    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | ~spl7_24),
% 0.20/0.49    inference(resolution,[],[f218,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | v2_struct_0(X0) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.20/0.49    inference(equality_resolution,[],[f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~spl7_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f214])).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    spl7_24 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.20/0.49  fof(f283,plain,(
% 0.20/0.49    spl7_24 | ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f282,f201,f193,f189,f181,f109,f105,f93,f89,f85,f81,f77,f73,f69,f65,f61,f214])).
% 0.20/0.49  fof(f282,plain,(
% 0.20/0.49    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21)),
% 0.20/0.49    inference(subsumption_resolution,[],[f59,f278])).
% 0.20/0.49  fof(f278,plain,(
% 0.20/0.49    ~r1_tmap_1(sK3,sK0,sK4,sK5) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21)),
% 0.20/0.49    inference(subsumption_resolution,[],[f277,f106])).
% 0.20/0.49  fof(f277,plain,(
% 0.20/0.49    ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21)),
% 0.20/0.49    inference(subsumption_resolution,[],[f276,f70])).
% 0.20/0.49  fof(f276,plain,(
% 0.20/0.49    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21)),
% 0.20/0.49    inference(subsumption_resolution,[],[f272,f182])).
% 0.20/0.49  fof(f272,plain,(
% 0.20/0.49    ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_18 | ~spl7_19 | ~spl7_21)),
% 0.20/0.49    inference(resolution,[],[f268,f190])).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(sK3,sK0,sK4,X1) | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1)) ) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_19 | ~spl7_21)),
% 0.20/0.49    inference(subsumption_resolution,[],[f267,f86])).
% 0.20/0.49  fof(f267,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(sK3,sK0,sK4,X1) | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1)) ) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_19 | ~spl7_21)),
% 0.20/0.49    inference(subsumption_resolution,[],[f266,f194])).
% 0.20/0.49  fof(f266,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(sK3,sK0,sK4,X1) | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1)) ) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_21)),
% 0.20/0.49    inference(subsumption_resolution,[],[f265,f62])).
% 0.20/0.49  fof(f265,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(sK3,sK0,sK4,X1) | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_21)),
% 0.20/0.49    inference(subsumption_resolution,[],[f264,f94])).
% 0.20/0.49  fof(f264,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(sK3,sK0,sK4,X1) | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_13 | ~spl7_21)),
% 0.20/0.49    inference(subsumption_resolution,[],[f263,f90])).
% 0.20/0.49  fof(f263,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(sK3,sK0,sK4,X1) | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | ~spl7_21)),
% 0.20/0.49    inference(resolution,[],[f158,f202])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5)))) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5)) | v2_struct_0(X5) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_pre_topc(X6,sK3) | ~r1_tmap_1(sK3,X5,X7,X8) | r1_tmap_1(X6,X5,k3_tmap_1(sK1,X5,sK3,X6,X7),X8)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f157,f148])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK1)) ) | (~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f147,f78])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK1)) ) | (~spl7_6 | ~spl7_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f137,f82])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK1)) ) | ~spl7_13),
% 0.20/0.49    inference(resolution,[],[f110,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    ( ! [X6,X8,X7,X5] : (v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK1) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5)))) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_pre_topc(X6,sK3) | ~r1_tmap_1(sK3,X5,X7,X8) | r1_tmap_1(X6,X5,k3_tmap_1(sK1,X5,sK3,X6,X7),X8)) ) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f156,f74])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    ( ! [X6,X8,X7,X5] : (v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(sK1) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK1) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5)))) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_pre_topc(X6,sK3) | ~r1_tmap_1(sK3,X5,X7,X8) | r1_tmap_1(X6,X5,k3_tmap_1(sK1,X5,sK3,X6,X7),X8)) ) | (spl7_2 | ~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f155,f66])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    ( ! [X6,X8,X7,X5] : (v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(sK3) | v2_struct_0(sK1) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK1) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5)))) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_pre_topc(X6,sK3) | ~r1_tmap_1(sK3,X5,X7,X8) | r1_tmap_1(X6,X5,k3_tmap_1(sK1,X5,sK3,X6,X7),X8)) ) | (~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f154,f82])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    ( ! [X6,X8,X7,X5] : (~l1_pre_topc(sK1) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(sK3) | v2_struct_0(sK1) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK1) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5)))) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_pre_topc(X6,sK3) | ~r1_tmap_1(sK3,X5,X7,X8) | r1_tmap_1(X6,X5,k3_tmap_1(sK1,X5,sK3,X6,X7),X8)) ) | (~spl7_5 | ~spl7_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f140,f78])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ( ! [X6,X8,X7,X5] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(sK3) | v2_struct_0(sK1) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK1) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5)))) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_pre_topc(X6,sK3) | ~r1_tmap_1(sK3,X5,X7,X8) | r1_tmap_1(X6,X5,k3_tmap_1(sK1,X5,sK3,X6,X7),X8)) ) | ~spl7_13),
% 0.20/0.49    inference(resolution,[],[f110,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | v2_struct_0(X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X6) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 0.20/0.49    inference(equality_resolution,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | X5 != X6 | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X5) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.20/0.49    inference(forward_demodulation,[],[f24,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    sK5 = sK6),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f8])).
% 0.20/0.49  fof(f8,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f259,plain,(
% 0.20/0.49    spl7_32 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f255,f229,f113,f109,f101,f81,f77,f73,f65,f257])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    spl7_11 <=> v1_tsep_1(sK2,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.49  fof(f229,plain,(
% 0.20/0.49    spl7_26 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.20/0.49  fof(f255,plain,(
% 0.20/0.49    v1_tsep_1(sK2,sK3) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_26)),
% 0.20/0.49    inference(subsumption_resolution,[],[f254,f66])).
% 0.20/0.49  fof(f254,plain,(
% 0.20/0.49    v2_struct_0(sK3) | v1_tsep_1(sK2,sK3) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_26)),
% 0.20/0.49    inference(subsumption_resolution,[],[f253,f110])).
% 0.20/0.49  fof(f253,plain,(
% 0.20/0.49    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | v1_tsep_1(sK2,sK3) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_14 | ~spl7_26)),
% 0.20/0.49    inference(resolution,[],[f121,f230])).
% 0.20/0.49  fof(f230,plain,(
% 0.20/0.49    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl7_26),
% 0.20/0.49    inference(avatar_component_clause,[],[f229])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | v1_tsep_1(sK2,X0)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_14)),
% 0.20/0.49    inference(subsumption_resolution,[],[f120,f114])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11)),
% 0.20/0.49    inference(subsumption_resolution,[],[f119,f74])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | (~spl7_5 | ~spl7_6 | ~spl7_11)),
% 0.20/0.49    inference(subsumption_resolution,[],[f118,f82])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | (~spl7_5 | ~spl7_11)),
% 0.20/0.49    inference(subsumption_resolution,[],[f116,f78])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | ~spl7_11),
% 0.20/0.49    inference(resolution,[],[f102,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_tsep_1(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    v1_tsep_1(sK2,sK1) | ~spl7_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f101])).
% 0.20/0.49  fof(f231,plain,(
% 0.20/0.49    spl7_26 | ~spl7_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f227,f197,f229])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    spl7_20 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.49  fof(f227,plain,(
% 0.20/0.49    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl7_20),
% 0.20/0.49    inference(resolution,[],[f198,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.20/0.49    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl7_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f197])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    ~spl7_23 | ~spl7_24),
% 0.20/0.49    inference(avatar_split_clause,[],[f58,f214,f211])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.20/0.49    inference(forward_demodulation,[],[f25,f27])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    spl7_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f201])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    spl7_20 | ~spl7_6 | ~spl7_12 | ~spl7_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f144,f109,f105,f81,f197])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | (~spl7_6 | ~spl7_12 | ~spl7_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f128,f141])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    l1_pre_topc(sK3) | (~spl7_6 | ~spl7_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f136,f82])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ~l1_pre_topc(sK1) | l1_pre_topc(sK3) | ~spl7_13),
% 0.20/0.49    inference(resolution,[],[f110,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    ~l1_pre_topc(sK3) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl7_12),
% 0.20/0.49    inference(resolution,[],[f106,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    spl7_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f193])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    spl7_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f57,f189])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.20/0.49    inference(forward_demodulation,[],[f26,f27])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    spl7_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f28,f181])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl7_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f113])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    m1_pre_topc(sK2,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl7_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f109])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    m1_pre_topc(sK3,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    spl7_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f34,f105])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    spl7_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f101])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    v1_tsep_1(sK2,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    spl7_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f93])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl7_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f89])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ~spl7_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f42,f85])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl7_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f81])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    l1_pre_topc(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl7_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f40,f77])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    v2_pre_topc(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ~spl7_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f39,f73])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ~v2_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ~spl7_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f69])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ~v2_struct_0(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ~spl7_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f65])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ~v2_struct_0(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    spl7_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f29,f61])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    v1_funct_1(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (22509)------------------------------
% 0.20/0.49  % (22509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22509)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (22509)Memory used [KB]: 6396
% 0.20/0.49  % (22509)Time elapsed: 0.069 s
% 0.20/0.49  % (22509)------------------------------
% 0.20/0.49  % (22509)------------------------------
% 0.20/0.49  % (22529)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (22504)Success in time 0.141 s
%------------------------------------------------------------------------------

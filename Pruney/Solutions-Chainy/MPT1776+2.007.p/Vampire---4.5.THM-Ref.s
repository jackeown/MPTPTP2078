%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  261 ( 549 expanded)
%              Number of leaves         :   53 ( 236 expanded)
%              Depth                    :   16
%              Number of atoms          : 1706 (4160 expanded)
%              Number of equality atoms :   52 ( 158 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f410,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f89,f93,f97,f101,f109,f113,f117,f121,f125,f129,f133,f137,f144,f147,f151,f159,f163,f167,f171,f175,f183,f187,f192,f197,f201,f205,f215,f219,f233,f263,f270,f274,f284,f314,f336,f350,f367,f383,f400,f404,f409])).

fof(f409,plain,
    ( ~ spl7_46
    | spl7_3
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_44
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f408,f398,f282,f127,f111,f75,f312])).

fof(f312,plain,
    ( spl7_46
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f75,plain,
    ( spl7_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f111,plain,
    ( spl7_12
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f127,plain,
    ( spl7_16
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f282,plain,
    ( spl7_44
  <=> r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f398,plain,
    ( spl7_56
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_tsep_1(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f408,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | spl7_3
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_44
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f407,f112])).

fof(f112,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f407,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | spl7_3
    | ~ spl7_16
    | ~ spl7_44
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f406,f128])).

fof(f128,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f406,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | spl7_3
    | ~ spl7_44
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f405,f76])).

fof(f76,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f405,plain,
    ( v2_struct_0(sK2)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ spl7_44
    | ~ spl7_56 ),
    inference(resolution,[],[f403,f399])).

fof(f399,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_tsep_1(X0,sK3) )
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f398])).

fof(f403,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f282])).

fof(f404,plain,
    ( spl7_44
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f396,f261,f142,f111,f282])).

fof(f142,plain,
    ( spl7_20
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f261,plain,
    ( spl7_41
  <=> ! [X1] :
        ( k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4)
        | ~ m1_pre_topc(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f396,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f395,f112])).

fof(f395,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl7_20
    | ~ spl7_41 ),
    inference(superposition,[],[f146,f262])).

fof(f262,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4)
        | ~ m1_pre_topc(X1,sK3) )
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f261])).

fof(f146,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f142])).

fof(f400,plain,
    ( spl7_56
    | ~ spl7_39
    | ~ spl7_40
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f394,f217,f139,f135,f131,f123,f99,f95,f91,f71,f258,f255,f398])).

fof(f255,plain,
    ( spl7_39
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f258,plain,
    ( spl7_40
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f71,plain,
    ( spl7_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f91,plain,
    ( spl7_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f95,plain,
    ( spl7_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f99,plain,
    ( spl7_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f123,plain,
    ( spl7_15
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f131,plain,
    ( spl7_17
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f135,plain,
    ( spl7_18
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f139,plain,
    ( spl7_19
  <=> r1_tmap_1(sK3,sK0,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f217,plain,
    ( spl7_36
  <=> ! [X1,X3,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X2)
        | ~ v1_tsep_1(X2,X1)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3)
        | r1_tmap_1(X1,X0,sK4,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f394,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5) )
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f393,f96])).

fof(f96,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f393,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | spl7_2
    | spl7_7
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f392,f124])).

fof(f124,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f392,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | spl7_2
    | spl7_7
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f391,f136])).

fof(f136,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f135])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | spl7_2
    | spl7_7
    | ~ spl7_9
    | ~ spl7_17
    | spl7_19
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f390,f132])).

fof(f132,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f131])).

fof(f390,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | spl7_2
    | spl7_7
    | ~ spl7_9
    | spl7_19
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f389,f92])).

fof(f92,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f389,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | spl7_2
    | ~ spl7_9
    | spl7_19
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f388,f72])).

fof(f72,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f388,plain,
    ( ! [X0] :
        ( v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | ~ spl7_9
    | spl7_19
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f387,f100])).

fof(f100,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f387,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5)
        | ~ v2_pre_topc(sK0) )
    | spl7_19
    | ~ spl7_36 ),
    inference(resolution,[],[f140,f218])).

fof(f218,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tmap_1(X1,X0,sK4,X3)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X2)
        | ~ v1_tsep_1(X2,X1)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f217])).

fof(f140,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f139])).

fof(f383,plain,
    ( spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_50 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_50 ),
    inference(subsumption_resolution,[],[f381,f88])).

fof(f88,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl7_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f381,plain,
    ( ~ l1_pre_topc(sK1)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_50 ),
    inference(subsumption_resolution,[],[f380,f84])).

fof(f84,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f83])).

% (3864)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f83,plain,
    ( spl7_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f380,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | spl7_4
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_50 ),
    inference(subsumption_resolution,[],[f379,f120])).

fof(f120,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl7_14
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f379,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | spl7_4
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_50 ),
    inference(subsumption_resolution,[],[f378,f116])).

fof(f116,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl7_13
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f378,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | spl7_4
    | ~ spl7_11
    | ~ spl7_50 ),
    inference(subsumption_resolution,[],[f374,f80])).

fof(f80,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f374,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_11
    | ~ spl7_50 ),
    inference(resolution,[],[f335,f108])).

fof(f108,plain,
    ( v1_tsep_1(sK2,sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_11
  <=> v1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f335,plain,
    ( ! [X0] :
        ( ~ v1_tsep_1(sK2,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl7_50
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f367,plain,
    ( ~ spl7_39
    | ~ spl7_12
    | ~ spl7_25
    | spl7_52 ),
    inference(avatar_split_clause,[],[f362,f348,f165,f111,f255])).

fof(f165,plain,
    ( spl7_25
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f348,plain,
    ( spl7_52
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f362,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl7_12
    | ~ spl7_25
    | spl7_52 ),
    inference(subsumption_resolution,[],[f360,f112])).

fof(f360,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl7_25
    | spl7_52 ),
    inference(resolution,[],[f349,f166])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f165])).

fof(f349,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl7_52 ),
    inference(avatar_component_clause,[],[f348])).

fof(f350,plain,
    ( ~ spl7_52
    | ~ spl7_23
    | spl7_49 ),
    inference(avatar_split_clause,[],[f342,f331,f157,f348])).

fof(f157,plain,
    ( spl7_23
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f331,plain,
    ( spl7_49
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f342,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl7_23
    | spl7_49 ),
    inference(resolution,[],[f332,f158])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f157])).

fof(f332,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | spl7_49 ),
    inference(avatar_component_clause,[],[f331])).

fof(f336,plain,
    ( ~ spl7_49
    | spl7_50
    | spl7_2
    | ~ spl7_27
    | spl7_46 ),
    inference(avatar_split_clause,[],[f325,f312,f173,f71,f334,f331])).

fof(f173,plain,
    ( spl7_27
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
        | v1_tsep_1(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f325,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
        | v2_struct_0(X0) )
    | spl7_2
    | ~ spl7_27
    | spl7_46 ),
    inference(subsumption_resolution,[],[f324,f72])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
        | v2_struct_0(X0) )
    | ~ spl7_27
    | spl7_46 ),
    inference(resolution,[],[f313,f174])).

fof(f174,plain,
    ( ! [X2,X0,X1] :
        ( v1_tsep_1(X1,X2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
        | v2_struct_0(X0) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f173])).

fof(f313,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | spl7_46 ),
    inference(avatar_component_clause,[],[f312])).

fof(f314,plain,
    ( ~ spl7_46
    | ~ spl7_39
    | ~ spl7_40
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_32
    | spl7_44 ),
    inference(avatar_split_clause,[],[f307,f282,f195,f139,f135,f131,f127,f123,f111,f99,f95,f91,f75,f71,f67,f258,f255,f312])).

fof(f67,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f195,plain,
    ( spl7_32
  <=> ! [X1,X3,X5,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ v1_tsep_1(X3,X1)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
        | ~ r1_tmap_1(X1,X0,X2,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f307,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_32
    | spl7_44 ),
    inference(subsumption_resolution,[],[f306,f145])).

fof(f145,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f139])).

fof(f306,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_32
    | spl7_44 ),
    inference(subsumption_resolution,[],[f305,f92])).

fof(f305,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK0)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_32
    | spl7_44 ),
    inference(subsumption_resolution,[],[f304,f128])).

fof(f304,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_32
    | spl7_44 ),
    inference(subsumption_resolution,[],[f303,f124])).

fof(f303,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_32
    | spl7_44 ),
    inference(subsumption_resolution,[],[f302,f112])).

fof(f302,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_32
    | spl7_44 ),
    inference(subsumption_resolution,[],[f301,f76])).

fof(f301,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_32
    | spl7_44 ),
    inference(subsumption_resolution,[],[f300,f136])).

fof(f300,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_32
    | spl7_44 ),
    inference(subsumption_resolution,[],[f299,f132])).

fof(f299,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_32
    | spl7_44 ),
    inference(subsumption_resolution,[],[f298,f68])).

fof(f68,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f298,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_32
    | spl7_44 ),
    inference(subsumption_resolution,[],[f297,f72])).

fof(f297,plain,
    ( v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_32
    | spl7_44 ),
    inference(subsumption_resolution,[],[f296,f100])).

fof(f296,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_8
    | ~ spl7_32
    | spl7_44 ),
    inference(subsumption_resolution,[],[f295,f96])).

fof(f295,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_32
    | spl7_44 ),
    inference(resolution,[],[f283,f196])).

fof(f196,plain,
    ( ! [X2,X0,X5,X3,X1] :
        ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ v1_tsep_1(X3,X1)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | v2_struct_0(X0)
        | ~ r1_tmap_1(X1,X0,X2,X5) )
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f195])).

fof(f283,plain,
    ( ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | spl7_44 ),
    inference(avatar_component_clause,[],[f282])).

fof(f284,plain,
    ( ~ spl7_44
    | ~ spl7_12
    | spl7_20
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f276,f261,f142,f111,f282])).

fof(f276,plain,
    ( ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl7_12
    | spl7_20
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f275,f112])).

fof(f275,plain,
    ( ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | spl7_20
    | ~ spl7_41 ),
    inference(superposition,[],[f143,f262])).

fof(f143,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f142])).

fof(f274,plain,
    ( ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_24
    | spl7_40 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_24
    | spl7_40 ),
    inference(unit_resulting_resolution,[],[f84,f88,f116,f259,f162])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl7_24
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f259,plain,
    ( ~ v2_pre_topc(sK3)
    | spl7_40 ),
    inference(avatar_component_clause,[],[f258])).

fof(f270,plain,
    ( ~ spl7_6
    | ~ spl7_13
    | ~ spl7_21
    | spl7_39 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_21
    | spl7_39 ),
    inference(unit_resulting_resolution,[],[f88,f116,f256,f150])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl7_21
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f256,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_39 ),
    inference(avatar_component_clause,[],[f255])).

fof(f263,plain,
    ( ~ spl7_39
    | ~ spl7_40
    | spl7_41
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_29
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f244,f231,f181,f135,f131,f99,f95,f91,f71,f67,f261,f258,f255])).

fof(f181,plain,
    ( spl7_29
  <=> ! [X1,X3,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ m1_pre_topc(X3,X0)
        | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f231,plain,
    ( spl7_37
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f244,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4)
        | ~ m1_pre_topc(X1,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_29
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f243,f72])).

fof(f243,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4)
        | ~ m1_pre_topc(X1,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_29
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f242,f136])).

fof(f242,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4)
        | ~ m1_pre_topc(X1,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | v2_struct_0(sK3) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_29
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f241,f132])).

fof(f241,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4)
        | ~ m1_pre_topc(X1,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | v2_struct_0(sK3) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_29
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f240,f68])).

fof(f240,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4)
        | ~ m1_pre_topc(X1,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | v2_struct_0(sK3) )
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_29
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f239,f100])).

fof(f239,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4)
        | ~ m1_pre_topc(X1,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | v2_struct_0(sK3) )
    | spl7_7
    | ~ spl7_8
    | ~ spl7_29
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f238,f96])).

fof(f238,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4)
        | ~ m1_pre_topc(X1,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | v2_struct_0(sK3) )
    | spl7_7
    | ~ spl7_29
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f237,f92])).

fof(f237,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4)
        | ~ m1_pre_topc(X1,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | v2_struct_0(sK3) )
    | ~ spl7_29
    | ~ spl7_37 ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,
    ( ! [X1] :
        ( k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4)
        | ~ m1_pre_topc(X1,sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK3) )
    | ~ spl7_29
    | ~ spl7_37 ),
    inference(superposition,[],[f232,f182])).

fof(f182,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ m1_pre_topc(X3,X0)
        | v2_struct_0(X0) )
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f181])).

fof(f232,plain,
    ( ! [X0] :
        ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f231])).

fof(f233,plain,
    ( spl7_37
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f227,f213,f115,f87,f83,f79,f231])).

fof(f213,plain,
    ( spl7_35
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X1,sK3)
        | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f226,f84])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | spl7_4
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f225,f80])).

fof(f225,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f220,f88])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | ~ spl7_13
    | ~ spl7_35 ),
    inference(resolution,[],[f214,f116])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X1,sK3)
        | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1)) )
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f213])).

fof(f219,plain,
    ( spl7_36
    | ~ spl7_1
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f211,f203,f67,f217])).

fof(f203,plain,
    ( spl7_34
  <=> ! [X1,X3,X5,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ v1_tsep_1(X3,X1)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
        | r1_tmap_1(X1,X0,X2,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f211,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X2)
        | ~ v1_tsep_1(X2,X1)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(X3,u1_struct_0(X1))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3)
        | r1_tmap_1(X1,X0,sK4,X3) )
    | ~ spl7_1
    | ~ spl7_34 ),
    inference(resolution,[],[f204,f68])).

fof(f204,plain,
    ( ! [X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(X2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ v1_tsep_1(X3,X1)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
        | r1_tmap_1(X1,X0,X2,X5) )
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f203])).

fof(f215,plain,
    ( spl7_35
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f210,f199,f135,f131,f99,f95,f91,f213])).

fof(f199,plain,
    ( spl7_33
  <=> ! [X1,X3,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ m1_pre_topc(X3,X2)
        | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(X1,sK3)
        | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1)) )
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f209,f136])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK3)
        | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1)) )
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f208,f100])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK3)
        | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1)) )
    | spl7_7
    | ~ spl7_8
    | ~ spl7_17
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f207,f96])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK3)
        | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1)) )
    | spl7_7
    | ~ spl7_17
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f206,f92])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK3)
        | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1)) )
    | ~ spl7_17
    | ~ spl7_33 ),
    inference(resolution,[],[f200,f132])).

fof(f200,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ m1_pre_topc(X3,X2)
        | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3)) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f199])).

fof(f205,plain,(
    spl7_34 ),
    inference(avatar_split_clause,[],[f62,f203])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | r1_tmap_1(X1,X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f201,plain,
    ( spl7_33
    | ~ spl7_1
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f193,f190,f67,f199])).

fof(f190,plain,
    ( spl7_31
  <=> ! [X1,X3,X0,X2,X4] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X2,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ m1_pre_topc(X3,X2)
        | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f193,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ m1_pre_topc(X3,X2)
        | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3)) )
    | ~ spl7_1
    | ~ spl7_31 ),
    inference(resolution,[],[f191,f68])).

fof(f191,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_1(X4)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ m1_pre_topc(X3,X2)
        | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f190])).

fof(f197,plain,(
    spl7_32 ),
    inference(avatar_split_clause,[],[f61,f195])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f192,plain,
    ( spl7_31
    | ~ spl7_26
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f188,f185,f169,f190])).

fof(f169,plain,
    ( spl7_26
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X1)
        | m1_pre_topc(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f185,plain,
    ( spl7_30
  <=> ! [X1,X3,X0,X2,X4] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ m1_pre_topc(X3,X2)
        | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f188,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X2,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ m1_pre_topc(X3,X2)
        | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) )
    | ~ spl7_26
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f186,f170])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f169])).

fof(f186,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X3,X0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ m1_pre_topc(X3,X2)
        | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) )
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f185])).

fof(f187,plain,(
    spl7_30 ),
    inference(avatar_split_clause,[],[f51,f185])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f183,plain,(
    spl7_29 ),
    inference(avatar_split_clause,[],[f52,f181])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f175,plain,(
    spl7_27 ),
    inference(avatar_split_clause,[],[f55,f173])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | v1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f171,plain,(
    spl7_26 ),
    inference(avatar_split_clause,[],[f58,f169])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f167,plain,(
    spl7_25 ),
    inference(avatar_split_clause,[],[f50,f165])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f163,plain,(
    spl7_24 ),
    inference(avatar_split_clause,[],[f57,f161])).

% (3876)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
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
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f159,plain,(
    spl7_23 ),
    inference(avatar_split_clause,[],[f60,f157])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f151,plain,(
    spl7_21 ),
    inference(avatar_split_clause,[],[f49,f149])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f147,plain,
    ( spl7_19
    | spl7_20 ),
    inference(avatar_split_clause,[],[f65,f142,f139])).

fof(f65,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(forward_demodulation,[],[f28,f31])).

fof(f31,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f28,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f144,plain,
    ( ~ spl7_19
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f64,f142,f139])).

fof(f64,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(forward_demodulation,[],[f29,f31])).

fof(f29,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f137,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f35,f135])).

fof(f35,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f133,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f34,f131])).

fof(f34,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f129,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f63,f127])).

fof(f63,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f30,f31])).

fof(f30,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f125,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f32,f123])).

fof(f32,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f121,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f42,f119])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f117,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f40,f115])).

% (3872)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f40,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f13])).

% (3873)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f113,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f38,f111])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f109,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f36,f107])).

fof(f36,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f101,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f48,f99])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f97,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f47,f95])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f93,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f46,f91])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f89,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f45,f87])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f85,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f44,f83])).

fof(f44,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f43,f79])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f41,f75])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f39,f71])).

fof(f39,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f33,f67])).

fof(f33,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:48:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (3877)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.47  % (3869)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (3866)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (3871)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  % (3870)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (3874)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (3879)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (3863)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (3869)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f410,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f89,f93,f97,f101,f109,f113,f117,f121,f125,f129,f133,f137,f144,f147,f151,f159,f163,f167,f171,f175,f183,f187,f192,f197,f201,f205,f215,f219,f233,f263,f270,f274,f284,f314,f336,f350,f367,f383,f400,f404,f409])).
% 0.22/0.49  fof(f409,plain,(
% 0.22/0.49    ~spl7_46 | spl7_3 | ~spl7_12 | ~spl7_16 | ~spl7_44 | ~spl7_56),
% 0.22/0.49    inference(avatar_split_clause,[],[f408,f398,f282,f127,f111,f75,f312])).
% 0.22/0.49  fof(f312,plain,(
% 0.22/0.49    spl7_46 <=> v1_tsep_1(sK2,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl7_3 <=> v2_struct_0(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    spl7_12 <=> m1_pre_topc(sK2,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    spl7_16 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.49  fof(f282,plain,(
% 0.22/0.49    spl7_44 <=> r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.22/0.49  fof(f398,plain,(
% 0.22/0.49    spl7_56 <=> ! [X0] : (v2_struct_0(X0) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~v1_tsep_1(X0,sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 0.22/0.49  fof(f408,plain,(
% 0.22/0.49    ~v1_tsep_1(sK2,sK3) | (spl7_3 | ~spl7_12 | ~spl7_16 | ~spl7_44 | ~spl7_56)),
% 0.22/0.49    inference(subsumption_resolution,[],[f407,f112])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK3) | ~spl7_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f111])).
% 0.22/0.49  fof(f407,plain,(
% 0.22/0.49    ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | (spl7_3 | ~spl7_16 | ~spl7_44 | ~spl7_56)),
% 0.22/0.49    inference(subsumption_resolution,[],[f406,f128])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl7_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f127])).
% 0.22/0.49  fof(f406,plain,(
% 0.22/0.49    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | (spl7_3 | ~spl7_44 | ~spl7_56)),
% 0.22/0.49    inference(subsumption_resolution,[],[f405,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ~v2_struct_0(sK2) | spl7_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f75])).
% 0.22/0.49  fof(f405,plain,(
% 0.22/0.49    v2_struct_0(sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | (~spl7_44 | ~spl7_56)),
% 0.22/0.49    inference(resolution,[],[f403,f399])).
% 0.22/0.49  fof(f399,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~v1_tsep_1(X0,sK3)) ) | ~spl7_56),
% 0.22/0.49    inference(avatar_component_clause,[],[f398])).
% 0.22/0.49  fof(f403,plain,(
% 0.22/0.49    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~spl7_44),
% 0.22/0.49    inference(avatar_component_clause,[],[f282])).
% 0.22/0.49  fof(f404,plain,(
% 0.22/0.49    spl7_44 | ~spl7_12 | ~spl7_20 | ~spl7_41),
% 0.22/0.49    inference(avatar_split_clause,[],[f396,f261,f142,f111,f282])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    spl7_20 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.22/0.49  fof(f261,plain,(
% 0.22/0.49    spl7_41 <=> ! [X1] : (k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4) | ~m1_pre_topc(X1,sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.22/0.49  fof(f396,plain,(
% 0.22/0.49    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | (~spl7_12 | ~spl7_20 | ~spl7_41)),
% 0.22/0.49    inference(subsumption_resolution,[],[f395,f112])).
% 0.22/0.49  fof(f395,plain,(
% 0.22/0.49    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~m1_pre_topc(sK2,sK3) | (~spl7_20 | ~spl7_41)),
% 0.22/0.49    inference(superposition,[],[f146,f262])).
% 0.22/0.49  fof(f262,plain,(
% 0.22/0.49    ( ! [X1] : (k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4) | ~m1_pre_topc(X1,sK3)) ) | ~spl7_41),
% 0.22/0.49    inference(avatar_component_clause,[],[f261])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~spl7_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f142])).
% 0.22/0.49  fof(f400,plain,(
% 0.22/0.49    spl7_56 | ~spl7_39 | ~spl7_40 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_17 | ~spl7_18 | spl7_19 | ~spl7_36),
% 0.22/0.49    inference(avatar_split_clause,[],[f394,f217,f139,f135,f131,f123,f99,f95,f91,f71,f258,f255,f398])).
% 0.22/0.49  fof(f255,plain,(
% 0.22/0.49    spl7_39 <=> l1_pre_topc(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.22/0.49  fof(f258,plain,(
% 0.22/0.49    spl7_40 <=> v2_pre_topc(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl7_2 <=> v2_struct_0(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl7_7 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl7_8 <=> v2_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl7_9 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    spl7_15 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    spl7_17 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    spl7_18 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    spl7_19 <=> r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    spl7_36 <=> ! [X1,X3,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | r1_tmap_1(X1,X0,sK4,X3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.22/0.49  fof(f394,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5)) ) | (spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_17 | ~spl7_18 | spl7_19 | ~spl7_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f393,f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    v2_pre_topc(sK0) | ~spl7_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f95])).
% 0.22/0.49  fof(f393,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5) | ~v2_pre_topc(sK0)) ) | (spl7_2 | spl7_7 | ~spl7_9 | ~spl7_15 | ~spl7_17 | ~spl7_18 | spl7_19 | ~spl7_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f392,f124])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl7_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f123])).
% 0.22/0.49  fof(f392,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5) | ~v2_pre_topc(sK0)) ) | (spl7_2 | spl7_7 | ~spl7_9 | ~spl7_17 | ~spl7_18 | spl7_19 | ~spl7_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f391,f136])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~spl7_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f135])).
% 0.22/0.49  fof(f391,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5) | ~v2_pre_topc(sK0)) ) | (spl7_2 | spl7_7 | ~spl7_9 | ~spl7_17 | spl7_19 | ~spl7_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f390,f132])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~spl7_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f131])).
% 0.22/0.49  fof(f390,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5) | ~v2_pre_topc(sK0)) ) | (spl7_2 | spl7_7 | ~spl7_9 | spl7_19 | ~spl7_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f389,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ~v2_struct_0(sK0) | spl7_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f91])).
% 0.22/0.49  fof(f389,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5) | ~v2_pre_topc(sK0)) ) | (spl7_2 | ~spl7_9 | spl7_19 | ~spl7_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f388,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ~v2_struct_0(sK3) | spl7_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f71])).
% 0.22/0.49  fof(f388,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5) | ~v2_pre_topc(sK0)) ) | (~spl7_9 | spl7_19 | ~spl7_36)),
% 0.22/0.49    inference(subsumption_resolution,[],[f387,f100])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    l1_pre_topc(sK0) | ~spl7_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f99])).
% 0.22/0.49  fof(f387,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK5) | ~v2_pre_topc(sK0)) ) | (spl7_19 | ~spl7_36)),
% 0.22/0.49    inference(resolution,[],[f140,f218])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X1,X0,sK4,X3) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | ~v2_pre_topc(X0)) ) | ~spl7_36),
% 0.22/0.49    inference(avatar_component_clause,[],[f217])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK0,sK4,sK5) | spl7_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f139])).
% 0.22/0.49  fof(f383,plain,(
% 0.22/0.49    spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_50),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f382])).
% 0.22/0.49  fof(f382,plain,(
% 0.22/0.49    $false | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f381,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    l1_pre_topc(sK1) | ~spl7_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl7_6 <=> l1_pre_topc(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.49  fof(f381,plain,(
% 0.22/0.49    ~l1_pre_topc(sK1) | (spl7_4 | ~spl7_5 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f380,f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    v2_pre_topc(sK1) | ~spl7_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f83])).
% 0.22/0.49  % (3864)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    spl7_5 <=> v2_pre_topc(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.49  fof(f380,plain,(
% 0.22/0.49    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | (spl7_4 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f379,f120])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK1) | ~spl7_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f119])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    spl7_14 <=> m1_pre_topc(sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.49  fof(f379,plain,(
% 0.22/0.49    ~m1_pre_topc(sK2,sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | (spl7_4 | ~spl7_11 | ~spl7_13 | ~spl7_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f378,f116])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    m1_pre_topc(sK3,sK1) | ~spl7_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f115])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    spl7_13 <=> m1_pre_topc(sK3,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.49  fof(f378,plain,(
% 0.22/0.49    ~m1_pre_topc(sK3,sK1) | ~m1_pre_topc(sK2,sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | (spl7_4 | ~spl7_11 | ~spl7_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f374,f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ~v2_struct_0(sK1) | spl7_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl7_4 <=> v2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.49  fof(f374,plain,(
% 0.22/0.49    v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK1) | ~m1_pre_topc(sK2,sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | (~spl7_11 | ~spl7_50)),
% 0.22/0.49    inference(resolution,[],[f335,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    v1_tsep_1(sK2,sK1) | ~spl7_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f107])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl7_11 <=> v1_tsep_1(sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.49  fof(f335,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_tsep_1(sK2,X0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl7_50),
% 0.22/0.49    inference(avatar_component_clause,[],[f334])).
% 0.22/0.49  fof(f334,plain,(
% 0.22/0.49    spl7_50 <=> ! [X0] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK2,X0) | ~v1_tsep_1(sK2,X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 0.22/0.49  fof(f367,plain,(
% 0.22/0.49    ~spl7_39 | ~spl7_12 | ~spl7_25 | spl7_52),
% 0.22/0.49    inference(avatar_split_clause,[],[f362,f348,f165,f111,f255])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    spl7_25 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.49  fof(f348,plain,(
% 0.22/0.49    spl7_52 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 0.22/0.49  fof(f362,plain,(
% 0.22/0.49    ~l1_pre_topc(sK3) | (~spl7_12 | ~spl7_25 | spl7_52)),
% 0.22/0.49    inference(subsumption_resolution,[],[f360,f112])).
% 0.22/0.49  fof(f360,plain,(
% 0.22/0.49    ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3) | (~spl7_25 | spl7_52)),
% 0.22/0.49    inference(resolution,[],[f349,f166])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl7_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f165])).
% 0.22/0.49  fof(f349,plain,(
% 0.22/0.49    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | spl7_52),
% 0.22/0.49    inference(avatar_component_clause,[],[f348])).
% 0.22/0.49  fof(f350,plain,(
% 0.22/0.49    ~spl7_52 | ~spl7_23 | spl7_49),
% 0.22/0.49    inference(avatar_split_clause,[],[f342,f331,f157,f348])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    spl7_23 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.49  fof(f331,plain,(
% 0.22/0.49    spl7_49 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 0.22/0.49  fof(f342,plain,(
% 0.22/0.49    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | (~spl7_23 | spl7_49)),
% 0.22/0.49    inference(resolution,[],[f332,f158])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl7_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f157])).
% 0.22/0.49  fof(f332,plain,(
% 0.22/0.49    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | spl7_49),
% 0.22/0.49    inference(avatar_component_clause,[],[f331])).
% 0.22/0.49  fof(f336,plain,(
% 0.22/0.49    ~spl7_49 | spl7_50 | spl7_2 | ~spl7_27 | spl7_46),
% 0.22/0.49    inference(avatar_split_clause,[],[f325,f312,f173,f71,f334,f331])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    spl7_27 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.22/0.49  fof(f325,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(X0)) ) | (spl7_2 | ~spl7_27 | spl7_46)),
% 0.22/0.49    inference(subsumption_resolution,[],[f324,f72])).
% 0.22/0.49  fof(f324,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X0) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(X0)) ) | (~spl7_27 | spl7_46)),
% 0.22/0.49    inference(resolution,[],[f313,f174])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v2_struct_0(X0)) ) | ~spl7_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f173])).
% 0.22/0.49  fof(f313,plain,(
% 0.22/0.49    ~v1_tsep_1(sK2,sK3) | spl7_46),
% 0.22/0.49    inference(avatar_component_clause,[],[f312])).
% 0.22/0.49  fof(f314,plain,(
% 0.22/0.49    ~spl7_46 | ~spl7_39 | ~spl7_40 | ~spl7_1 | spl7_2 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_32 | spl7_44),
% 0.22/0.49    inference(avatar_split_clause,[],[f307,f282,f195,f139,f135,f131,f127,f123,f111,f99,f95,f91,f75,f71,f67,f258,f255,f312])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl7_1 <=> v1_funct_1(sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    spl7_32 <=> ! [X1,X3,X5,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.22/0.49  fof(f307,plain,(
% 0.22/0.49    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_tsep_1(sK2,sK3) | (~spl7_1 | spl7_2 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_32 | spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f306,f145])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    r1_tmap_1(sK3,sK0,sK4,sK5) | ~spl7_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f139])).
% 0.22/0.49  fof(f306,plain,(
% 0.22/0.49    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_tsep_1(sK2,sK3) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | ~spl7_32 | spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f305,f92])).
% 0.22/0.49  fof(f305,plain,(
% 0.22/0.49    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK0) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | ~spl7_32 | spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f304,f128])).
% 0.22/0.49  fof(f304,plain,(
% 0.22/0.49    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_17 | ~spl7_18 | ~spl7_32 | spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f303,f124])).
% 0.22/0.49  fof(f303,plain,(
% 0.22/0.49    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_17 | ~spl7_18 | ~spl7_32 | spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f302,f112])).
% 0.22/0.49  fof(f302,plain,(
% 0.22/0.49    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_8 | ~spl7_9 | ~spl7_17 | ~spl7_18 | ~spl7_32 | spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f301,f76])).
% 0.22/0.49  fof(f301,plain,(
% 0.22/0.49    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_17 | ~spl7_18 | ~spl7_32 | spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f300,f136])).
% 0.22/0.49  fof(f300,plain,(
% 0.22/0.49    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_17 | ~spl7_32 | spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f299,f132])).
% 0.22/0.49  fof(f299,plain,(
% 0.22/0.49    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_32 | spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f298,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    v1_funct_1(sK4) | ~spl7_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f67])).
% 0.22/0.49  fof(f298,plain,(
% 0.22/0.49    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_32 | spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f297,f72])).
% 0.22/0.49  fof(f297,plain,(
% 0.22/0.49    v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_8 | ~spl7_9 | ~spl7_32 | spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f296,f100])).
% 0.22/0.49  fof(f296,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_8 | ~spl7_32 | spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f295,f96])).
% 0.22/0.49  fof(f295,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_32 | spl7_44)),
% 0.22/0.49    inference(resolution,[],[f283,f196])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | v2_struct_0(X0) | ~r1_tmap_1(X1,X0,X2,X5)) ) | ~spl7_32),
% 0.22/0.49    inference(avatar_component_clause,[],[f195])).
% 0.22/0.49  fof(f283,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | spl7_44),
% 0.22/0.49    inference(avatar_component_clause,[],[f282])).
% 0.22/0.49  fof(f284,plain,(
% 0.22/0.49    ~spl7_44 | ~spl7_12 | spl7_20 | ~spl7_41),
% 0.22/0.49    inference(avatar_split_clause,[],[f276,f261,f142,f111,f282])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | (~spl7_12 | spl7_20 | ~spl7_41)),
% 0.22/0.49    inference(subsumption_resolution,[],[f275,f112])).
% 0.22/0.49  fof(f275,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | ~m1_pre_topc(sK2,sK3) | (spl7_20 | ~spl7_41)),
% 0.22/0.49    inference(superposition,[],[f143,f262])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | spl7_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f142])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    ~spl7_5 | ~spl7_6 | ~spl7_13 | ~spl7_24 | spl7_40),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f272])).
% 0.22/0.49  fof(f272,plain,(
% 0.22/0.49    $false | (~spl7_5 | ~spl7_6 | ~spl7_13 | ~spl7_24 | spl7_40)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f84,f88,f116,f259,f162])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0)) ) | ~spl7_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f161])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    spl7_24 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.49  fof(f259,plain,(
% 0.22/0.49    ~v2_pre_topc(sK3) | spl7_40),
% 0.22/0.49    inference(avatar_component_clause,[],[f258])).
% 0.22/0.49  fof(f270,plain,(
% 0.22/0.49    ~spl7_6 | ~spl7_13 | ~spl7_21 | spl7_39),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f268])).
% 0.22/0.49  fof(f268,plain,(
% 0.22/0.49    $false | (~spl7_6 | ~spl7_13 | ~spl7_21 | spl7_39)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f88,f116,f256,f150])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl7_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f149])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    spl7_21 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.49  fof(f256,plain,(
% 0.22/0.49    ~l1_pre_topc(sK3) | spl7_39),
% 0.22/0.49    inference(avatar_component_clause,[],[f255])).
% 0.22/0.49  fof(f263,plain,(
% 0.22/0.49    ~spl7_39 | ~spl7_40 | spl7_41 | ~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_17 | ~spl7_18 | ~spl7_29 | ~spl7_37),
% 0.22/0.49    inference(avatar_split_clause,[],[f244,f231,f181,f135,f131,f99,f95,f91,f71,f67,f261,f258,f255])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    spl7_29 <=> ! [X1,X3,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    spl7_37 <=> ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.22/0.49  fof(f244,plain,(
% 0.22/0.49    ( ! [X1] : (k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4) | ~m1_pre_topc(X1,sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3)) ) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_17 | ~spl7_18 | ~spl7_29 | ~spl7_37)),
% 0.22/0.49    inference(subsumption_resolution,[],[f243,f72])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    ( ! [X1] : (k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4) | ~m1_pre_topc(X1,sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)) ) | (~spl7_1 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_17 | ~spl7_18 | ~spl7_29 | ~spl7_37)),
% 0.22/0.49    inference(subsumption_resolution,[],[f242,f136])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    ( ! [X1] : (k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4) | ~m1_pre_topc(X1,sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK3)) ) | (~spl7_1 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_17 | ~spl7_29 | ~spl7_37)),
% 0.22/0.49    inference(subsumption_resolution,[],[f241,f132])).
% 0.22/0.49  fof(f241,plain,(
% 0.22/0.49    ( ! [X1] : (k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4) | ~m1_pre_topc(X1,sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK3)) ) | (~spl7_1 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_29 | ~spl7_37)),
% 0.22/0.49    inference(subsumption_resolution,[],[f240,f68])).
% 0.22/0.49  fof(f240,plain,(
% 0.22/0.49    ( ! [X1] : (k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4) | ~m1_pre_topc(X1,sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK3)) ) | (spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_29 | ~spl7_37)),
% 0.22/0.49    inference(subsumption_resolution,[],[f239,f100])).
% 0.22/0.49  fof(f239,plain,(
% 0.22/0.49    ( ! [X1] : (k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4) | ~m1_pre_topc(X1,sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK3)) ) | (spl7_7 | ~spl7_8 | ~spl7_29 | ~spl7_37)),
% 0.22/0.49    inference(subsumption_resolution,[],[f238,f96])).
% 0.22/0.49  fof(f238,plain,(
% 0.22/0.49    ( ! [X1] : (k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4) | ~m1_pre_topc(X1,sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK3)) ) | (spl7_7 | ~spl7_29 | ~spl7_37)),
% 0.22/0.49    inference(subsumption_resolution,[],[f237,f92])).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    ( ! [X1] : (k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4) | ~m1_pre_topc(X1,sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | v2_struct_0(sK3)) ) | (~spl7_29 | ~spl7_37)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f234])).
% 0.22/0.49  fof(f234,plain,(
% 0.22/0.49    ( ! [X1] : (k2_tmap_1(sK3,sK0,sK4,X1) = k3_tmap_1(sK1,sK0,sK3,X1,sK4) | ~m1_pre_topc(X1,sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | v2_struct_0(sK3)) ) | (~spl7_29 | ~spl7_37)),
% 0.22/0.49    inference(superposition,[],[f232,f182])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0)) ) | ~spl7_29),
% 0.22/0.49    inference(avatar_component_clause,[],[f181])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) | ~m1_pre_topc(X0,sK3)) ) | ~spl7_37),
% 0.22/0.49    inference(avatar_component_clause,[],[f231])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    spl7_37 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | ~spl7_35),
% 0.22/0.49    inference(avatar_split_clause,[],[f227,f213,f115,f87,f83,f79,f231])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    spl7_35 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | ~spl7_35)),
% 0.22/0.49    inference(subsumption_resolution,[],[f226,f84])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (spl7_4 | ~spl7_6 | ~spl7_13 | ~spl7_35)),
% 0.22/0.49    inference(subsumption_resolution,[],[f225,f80])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (~spl7_6 | ~spl7_13 | ~spl7_35)),
% 0.22/0.49    inference(subsumption_resolution,[],[f220,f88])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (~spl7_13 | ~spl7_35)),
% 0.22/0.49    inference(resolution,[],[f214,f116])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1))) ) | ~spl7_35),
% 0.22/0.49    inference(avatar_component_clause,[],[f213])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    spl7_36 | ~spl7_1 | ~spl7_34),
% 0.22/0.49    inference(avatar_split_clause,[],[f211,f203,f67,f217])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    spl7_34 <=> ! [X1,X3,X5,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X5))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | r1_tmap_1(X1,X0,sK4,X3)) ) | (~spl7_1 | ~spl7_34)),
% 0.22/0.49    inference(resolution,[],[f204,f68])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X5)) ) | ~spl7_34),
% 0.22/0.49    inference(avatar_component_clause,[],[f203])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    spl7_35 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_17 | ~spl7_18 | ~spl7_33),
% 0.22/0.49    inference(avatar_split_clause,[],[f210,f199,f135,f131,f99,f95,f91,f213])).
% 0.22/0.49  fof(f199,plain,(
% 0.22/0.49    spl7_33 <=> ! [X1,X3,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1))) ) | (spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_17 | ~spl7_18 | ~spl7_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f209,f136])).
% 0.22/0.49  fof(f209,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1))) ) | (spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_17 | ~spl7_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f208,f100])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1))) ) | (spl7_7 | ~spl7_8 | ~spl7_17 | ~spl7_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f207,f96])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1))) ) | (spl7_7 | ~spl7_17 | ~spl7_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f206,f92])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK0,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X1))) ) | (~spl7_17 | ~spl7_33)),
% 0.22/0.49    inference(resolution,[],[f200,f132])).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) ) | ~spl7_33),
% 0.22/0.49    inference(avatar_component_clause,[],[f199])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    spl7_34),
% 0.22/0.49    inference(avatar_split_clause,[],[f62,f203])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.22/0.49    inference(equality_resolution,[],[f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    spl7_33 | ~spl7_1 | ~spl7_31),
% 0.22/0.49    inference(avatar_split_clause,[],[f193,f190,f67,f199])).
% 0.22/0.49  fof(f190,plain,(
% 0.22/0.49    spl7_31 <=> ! [X1,X3,X0,X2,X4] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) ) | (~spl7_1 | ~spl7_31)),
% 0.22/0.49    inference(resolution,[],[f191,f68])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) ) | ~spl7_31),
% 0.22/0.49    inference(avatar_component_clause,[],[f190])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    spl7_32),
% 0.22/0.49    inference(avatar_split_clause,[],[f61,f195])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5)) )),
% 0.22/0.49    inference(equality_resolution,[],[f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    spl7_31 | ~spl7_26 | ~spl7_30),
% 0.22/0.49    inference(avatar_split_clause,[],[f188,f185,f169,f190])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    spl7_26 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    spl7_30 <=> ! [X1,X3,X0,X2,X4] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) ) | (~spl7_26 | ~spl7_30)),
% 0.22/0.49    inference(subsumption_resolution,[],[f186,f170])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | ~v2_pre_topc(X0)) ) | ~spl7_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f169])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) ) | ~spl7_30),
% 0.22/0.49    inference(avatar_component_clause,[],[f185])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    spl7_30),
% 0.22/0.49    inference(avatar_split_clause,[],[f51,f185])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    spl7_29),
% 0.22/0.49    inference(avatar_split_clause,[],[f52,f181])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    spl7_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f55,f173])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    spl7_26),
% 0.22/0.49    inference(avatar_split_clause,[],[f58,f169])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    spl7_25),
% 0.22/0.49    inference(avatar_split_clause,[],[f50,f165])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    spl7_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f57,f161])).
% 0.22/0.49  % (3876)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    spl7_23),
% 0.22/0.49    inference(avatar_split_clause,[],[f60,f157])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    spl7_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f49,f149])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    spl7_19 | spl7_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f65,f142,f139])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.22/0.49    inference(forward_demodulation,[],[f28,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    sK5 = sK6),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    ~spl7_19 | ~spl7_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f64,f142,f139])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.22/0.49    inference(forward_demodulation,[],[f29,f31])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    spl7_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f135])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    spl7_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f131])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    spl7_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f63,f127])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.49    inference(forward_demodulation,[],[f30,f31])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    spl7_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f123])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    spl7_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f119])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    spl7_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f115])).
% 0.22/0.49  % (3872)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    m1_pre_topc(sK3,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  % (3873)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    spl7_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f111])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl7_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f107])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    v1_tsep_1(sK2,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    spl7_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f48,f99])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    spl7_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f47,f95])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ~spl7_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f46,f91])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl7_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f45,f87])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    l1_pre_topc(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl7_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f83])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    v2_pre_topc(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ~spl7_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f79])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ~v2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ~spl7_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f75])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ~v2_struct_0(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ~spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f71])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ~v2_struct_0(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl7_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f67])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    v1_funct_1(sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (3869)------------------------------
% 0.22/0.49  % (3869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3869)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (3869)Memory used [KB]: 10874
% 0.22/0.49  % (3869)Time elapsed: 0.061 s
% 0.22/0.49  % (3869)------------------------------
% 0.22/0.49  % (3869)------------------------------
% 0.22/0.49  % (3865)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (3859)Success in time 0.128 s
%------------------------------------------------------------------------------

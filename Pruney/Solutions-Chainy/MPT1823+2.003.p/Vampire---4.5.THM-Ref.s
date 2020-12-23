%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:47 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  395 (1084 expanded)
%              Number of leaves         :   68 ( 528 expanded)
%              Depth                    :   17
%              Number of atoms          : 3212 (7133 expanded)
%              Number of equality atoms :   91 ( 349 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f152,f179,f185,f190,f214,f220,f245,f254,f258,f276,f281,f285,f290,f311,f333,f349,f354,f367,f371,f393,f397,f419,f427,f454,f458,f463,f572,f601,f636,f651,f1988,f2002,f2047,f2069,f2123,f2128,f2135,f2140])).

fof(f2140,plain,
    ( ~ spl6_6
    | spl6_168 ),
    inference(avatar_contradiction_clause,[],[f2139])).

fof(f2139,plain,
    ( $false
    | ~ spl6_6
    | spl6_168 ),
    inference(subsumption_resolution,[],[f2137,f105])).

fof(f105,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f2137,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_168 ),
    inference(resolution,[],[f2134,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2134,plain,
    ( ~ l1_struct_0(sK1)
    | spl6_168 ),
    inference(avatar_component_clause,[],[f2132])).

fof(f2132,plain,
    ( spl6_168
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_168])])).

fof(f2135,plain,
    ( ~ spl6_168
    | spl6_4
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f2130,f208,f93,f2132])).

fof(f93,plain,
    ( spl6_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f208,plain,
    ( spl6_22
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f2130,plain,
    ( ~ l1_struct_0(sK1)
    | spl6_4
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f2129,f95])).

fof(f95,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f2129,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_22 ),
    inference(resolution,[],[f210,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f210,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f2128,plain,
    ( spl6_22
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_23
    | spl6_167 ),
    inference(avatar_split_clause,[],[f2127,f2120,f212,f143,f138,f118,f208])).

fof(f118,plain,
    ( spl6_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f138,plain,
    ( spl6_13
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f143,plain,
    ( spl6_14
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f212,plain,
    ( spl6_23
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | r1_funct_2(X1,X2,u1_struct_0(sK0),u1_struct_0(sK1),X0,X0)
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f2120,plain,
    ( spl6_167
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_167])])).

fof(f2127,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_23
    | spl6_167 ),
    inference(subsumption_resolution,[],[f2126,f140])).

fof(f140,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f138])).

fof(f2126,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_14
    | ~ spl6_23
    | spl6_167 ),
    inference(subsumption_resolution,[],[f2125,f120])).

fof(f120,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f2125,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_14
    | ~ spl6_23
    | spl6_167 ),
    inference(subsumption_resolution,[],[f2124,f145])).

fof(f145,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f2124,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_23
    | spl6_167 ),
    inference(resolution,[],[f2122,f213])).

fof(f213,plain,
    ( ! [X2,X0,X1] :
        ( r1_funct_2(X1,X2,u1_struct_0(sK0),u1_struct_0(sK1),X0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,X2) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f212])).

fof(f2122,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | spl6_167 ),
    inference(avatar_component_clause,[],[f2120])).

fof(f2123,plain,
    ( ~ spl6_167
    | spl6_18
    | ~ spl6_162 ),
    inference(avatar_split_clause,[],[f2080,f1977,f182,f2120])).

fof(f182,plain,
    ( spl6_18
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f1977,plain,
    ( spl6_162
  <=> sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_162])])).

fof(f2080,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | spl6_18
    | ~ spl6_162 ),
    inference(backward_demodulation,[],[f184,f1979])).

fof(f1979,plain,
    ( sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ spl6_162 ),
    inference(avatar_component_clause,[],[f1977])).

fof(f184,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f182])).

fof(f2069,plain,
    ( spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_46
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_164 ),
    inference(avatar_contradiction_clause,[],[f2068])).

fof(f2068,plain,
    ( $false
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_46
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2067,f95])).

fof(f2067,plain,
    ( v2_struct_0(sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_46
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2066,f100])).

fof(f100,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f2066,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_6
    | ~ spl6_30
    | ~ spl6_46
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2065,f105])).

fof(f2065,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_30
    | ~ spl6_46
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2064,f426])).

fof(f426,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl6_46
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f2064,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_30
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2063,f571])).

fof(f571,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f569])).

fof(f569,plain,
    ( spl6_53
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f2063,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_30
    | ~ spl6_50
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2062,f635])).

fof(f635,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f633])).

fof(f633,plain,
    ( spl6_60
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f2062,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_30
    | ~ spl6_50
    | ~ spl6_54
    | ~ spl6_61
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2061,f462])).

fof(f462,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl6_50
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f2061,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_30
    | ~ spl6_54
    | ~ spl6_61
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2060,f600])).

fof(f600,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f598])).

fof(f598,plain,
    ( spl6_54
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f2060,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_30
    | ~ spl6_61
    | spl6_164 ),
    inference(subsumption_resolution,[],[f2058,f650])).

fof(f650,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f648])).

fof(f648,plain,
    ( spl6_61
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f2058,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_30
    | spl6_164 ),
    inference(resolution,[],[f1987,f284])).

fof(f284,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl6_30
  <=> ! [X1,X0,X2] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f1987,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_164 ),
    inference(avatar_component_clause,[],[f1985])).

fof(f1985,plain,
    ( spl6_164
  <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_164])])).

fof(f2047,plain,
    ( spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_33
    | ~ spl6_46
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_163 ),
    inference(avatar_contradiction_clause,[],[f2046])).

fof(f2046,plain,
    ( $false
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_33
    | ~ spl6_46
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_163 ),
    inference(subsumption_resolution,[],[f2045,f95])).

fof(f2045,plain,
    ( v2_struct_0(sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_33
    | ~ spl6_46
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_163 ),
    inference(subsumption_resolution,[],[f2044,f100])).

fof(f2044,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_6
    | ~ spl6_33
    | ~ spl6_46
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_163 ),
    inference(subsumption_resolution,[],[f2043,f105])).

fof(f2043,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_33
    | ~ spl6_46
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_163 ),
    inference(subsumption_resolution,[],[f2042,f426])).

fof(f2042,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_33
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_163 ),
    inference(subsumption_resolution,[],[f2041,f571])).

fof(f2041,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_33
    | ~ spl6_50
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_163 ),
    inference(subsumption_resolution,[],[f2040,f635])).

fof(f2040,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_33
    | ~ spl6_50
    | ~ spl6_54
    | ~ spl6_61
    | spl6_163 ),
    inference(subsumption_resolution,[],[f2039,f462])).

fof(f2039,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_33
    | ~ spl6_54
    | ~ spl6_61
    | spl6_163 ),
    inference(subsumption_resolution,[],[f2038,f600])).

fof(f2038,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_33
    | ~ spl6_61
    | spl6_163 ),
    inference(subsumption_resolution,[],[f2036,f650])).

fof(f2036,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_33
    | spl6_163 ),
    inference(resolution,[],[f1983,f310])).

fof(f310,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl6_33
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f1983,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl6_163 ),
    inference(avatar_component_clause,[],[f1981])).

fof(f1981,plain,
    ( spl6_163
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_163])])).

fof(f2002,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_46
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_161 ),
    inference(avatar_contradiction_clause,[],[f2000])).

fof(f2000,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_46
    | ~ spl6_50
    | ~ spl6_53
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_61
    | spl6_161 ),
    inference(unit_resulting_resolution,[],[f80,f85,f90,f95,f100,f105,f110,f115,f125,f130,f426,f462,f571,f600,f635,f650,f1975,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f1975,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | spl6_161 ),
    inference(avatar_component_clause,[],[f1973])).

fof(f1973,plain,
    ( spl6_161
  <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_161])])).

fof(f130,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_11
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f125,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f115,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_8
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f110,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f90,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f85,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f80,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1988,plain,
    ( ~ spl6_161
    | spl6_162
    | ~ spl6_163
    | ~ spl6_164
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45
    | ~ spl6_48
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f539,f456,f451,f416,f143,f138,f103,f98,f93,f1985,f1981,f1977,f1973])).

fof(f416,plain,
    ( spl6_45
  <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f451,plain,
    ( spl6_48
  <=> k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f456,plain,
    ( spl6_49
  <=> ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | sK4 = k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))
        | ~ m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f539,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45
    | ~ spl6_48
    | ~ spl6_49 ),
    inference(forward_demodulation,[],[f538,f418])).

fof(f418,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f416])).

fof(f538,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45
    | ~ spl6_48
    | ~ spl6_49 ),
    inference(forward_demodulation,[],[f537,f418])).

fof(f537,plain,
    ( sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45
    | ~ spl6_48
    | ~ spl6_49 ),
    inference(forward_demodulation,[],[f536,f418])).

fof(f536,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45
    | ~ spl6_48
    | ~ spl6_49 ),
    inference(forward_demodulation,[],[f535,f418])).

fof(f535,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_48
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f534,f140])).

fof(f534,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_48
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f533,f95])).

fof(f533,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | v2_struct_0(sK1)
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_48
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f532,f100])).

fof(f532,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_48
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f531,f105])).

fof(f531,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_14
    | ~ spl6_48
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f527,f145])).

fof(f527,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_48
    | ~ spl6_49 ),
    inference(superposition,[],[f457,f453])).

fof(f453,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f451])).

fof(f457,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | sK4 = k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))
        | ~ m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) )
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f456])).

fof(f651,plain,
    ( spl6_61
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f556,f451,f176,f143,f138,f128,f118,f103,f98,f93,f88,f83,f78,f648])).

fof(f176,plain,
    ( spl6_17
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f556,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f555,f80])).

fof(f555,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f554,f85])).

fof(f554,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f553,f90])).

fof(f553,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f552,f95])).

fof(f552,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f551,f100])).

fof(f551,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f550,f105])).

fof(f550,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f549,f178])).

fof(f178,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f176])).

fof(f549,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f548,f130])).

fof(f548,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f547,f120])).

fof(f547,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f546,f140])).

fof(f546,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f529,f145])).

fof(f529,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_48 ),
    inference(superposition,[],[f68,f453])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f636,plain,
    ( spl6_60
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f515,f416,f176,f143,f138,f123,f118,f103,f98,f93,f88,f83,f78,f633])).

fof(f515,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f514,f80])).

fof(f514,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f513,f85])).

fof(f513,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f512,f90])).

fof(f512,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f511,f95])).

fof(f511,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f510,f100])).

fof(f510,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f509,f105])).

fof(f509,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f508,f178])).

fof(f508,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f507,f125])).

fof(f507,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f506,f120])).

fof(f506,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f505,f140])).

fof(f505,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f493,f145])).

fof(f493,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_45 ),
    inference(superposition,[],[f68,f418])).

fof(f601,plain,
    ( spl6_54
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f567,f451,f176,f143,f138,f128,f118,f103,f98,f93,f88,f83,f78,f598])).

fof(f567,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f566,f80])).

fof(f566,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f565,f85])).

fof(f565,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f564,f90])).

fof(f564,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f563,f95])).

fof(f563,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f562,f100])).

fof(f562,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f561,f105])).

fof(f561,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f560,f178])).

fof(f560,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f559,f130])).

fof(f559,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f558,f120])).

fof(f558,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f557,f140])).

fof(f557,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f530,f145])).

fof(f530,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_48 ),
    inference(superposition,[],[f67,f453])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f572,plain,
    ( spl6_53
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f526,f416,f176,f143,f138,f123,f118,f103,f98,f93,f88,f83,f78,f569])).

fof(f526,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f525,f80])).

fof(f525,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f524,f85])).

fof(f524,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f523,f90])).

fof(f523,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f522,f95])).

fof(f522,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f521,f100])).

fof(f521,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f520,f105])).

fof(f520,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f519,f178])).

fof(f519,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f518,f125])).

fof(f518,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f517,f120])).

fof(f517,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f516,f140])).

fof(f516,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f494,f145])).

fof(f494,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_45 ),
    inference(superposition,[],[f67,f418])).

fof(f463,plain,
    ( spl6_50
    | ~ spl6_11
    | ~ spl6_31
    | ~ spl6_38
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f449,f395,f364,f287,f128,f460])).

fof(f287,plain,
    ( spl6_31
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f364,plain,
    ( spl6_38
  <=> k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f395,plain,
    ( spl6_43
  <=> ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f449,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ spl6_11
    | ~ spl6_31
    | ~ spl6_38
    | ~ spl6_43 ),
    inference(backward_demodulation,[],[f289,f406])).

fof(f406,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f402,f366])).

fof(f366,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f364])).

fof(f402,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ spl6_11
    | ~ spl6_43 ),
    inference(resolution,[],[f396,f130])).

fof(f396,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f395])).

fof(f289,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f287])).

fof(f458,plain,
    ( spl6_49
    | ~ spl6_9
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f400,f391,f118,f456])).

fof(f391,plain,
    ( spl6_42
  <=> ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f400,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | sK4 = k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))
        | ~ m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) )
    | ~ spl6_9
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f399,f120])).

fof(f399,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | sK4 = k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))
        | ~ m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ v1_funct_1(sK4) )
    | ~ spl6_42 ),
    inference(duplicate_literal_removal,[],[f398])).

fof(f398,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | sK4 = k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))
        | ~ m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(sK4) )
    | ~ spl6_42 ),
    inference(resolution,[],[f392,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f392,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f391])).

fof(f454,plain,
    ( spl6_48
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f406,f395,f364,f128,f451])).

fof(f427,plain,
    ( spl6_46
    | ~ spl6_10
    | ~ spl6_29
    | ~ spl6_37
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f414,f395,f351,f278,f123,f424])).

fof(f278,plain,
    ( spl6_29
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f351,plain,
    ( spl6_37
  <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f414,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ spl6_10
    | ~ spl6_29
    | ~ spl6_37
    | ~ spl6_43 ),
    inference(backward_demodulation,[],[f280,f405])).

fof(f405,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ spl6_10
    | ~ spl6_37
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f401,f353])).

fof(f353,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f351])).

fof(f401,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl6_10
    | ~ spl6_43 ),
    inference(resolution,[],[f396,f125])).

fof(f280,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f278])).

fof(f419,plain,
    ( spl6_45
    | ~ spl6_10
    | ~ spl6_37
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f405,f395,f351,f123,f416])).

fof(f397,plain,
    ( spl6_43
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f381,f369,f176,f88,f83,f78,f395])).

fof(f369,plain,
    ( spl6_39
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f381,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f380,f80])).

fof(f380,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f379,f85])).

fof(f379,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f378,f90])).

fof(f378,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_17
    | ~ spl6_39 ),
    inference(duplicate_literal_removal,[],[f377])).

fof(f377,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_17
    | ~ spl6_39 ),
    inference(resolution,[],[f370,f178])).

fof(f370,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK0,X1)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f369])).

fof(f393,plain,
    ( spl6_42
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f362,f347,f133,f128,f123,f113,f108,f88,f83,f78,f391])).

fof(f133,plain,
    ( spl6_12
  <=> sK0 = k1_tsep_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f347,plain,
    ( spl6_36
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
        | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
        | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),sK4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK4)))
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f362,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f361,f80])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f360,f85])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f359,f90])).

fof(f359,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f358,f110])).

fof(f358,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f357,f125])).

fof(f357,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f356,f115])).

fof(f356,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f355,f130])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_36 ),
    inference(superposition,[],[f348,f135])).

fof(f135,plain,
    ( sK0 = k1_tsep_1(sK0,sK2,sK3)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f348,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
        | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
        | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),sK4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK4)))
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f347])).

fof(f371,plain,
    ( spl6_39
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f295,f274,f143,f138,f103,f98,f93,f369])).

fof(f274,plain,
    ( spl6_28
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4)
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f294,f95])).

fof(f294,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f293,f100])).

fof(f293,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f292,f105])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f291,f140])).

fof(f291,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_14
    | ~ spl6_28 ),
    inference(resolution,[],[f275,f145])).

fof(f275,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ m1_pre_topc(X0,X1)
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4)
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f274])).

fof(f367,plain,
    ( spl6_38
    | ~ spl6_11
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f341,f331,f128,f364])).

fof(f331,plain,
    ( spl6_35
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f341,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ spl6_11
    | ~ spl6_35 ),
    inference(resolution,[],[f332,f130])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f331])).

fof(f354,plain,
    ( spl6_37
    | ~ spl6_10
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f340,f331,f123,f351])).

fof(f340,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl6_10
    | ~ spl6_35 ),
    inference(resolution,[],[f332,f125])).

fof(f349,plain,
    ( spl6_36
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f246,f118,f347])).

fof(f246,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
        | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
        | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),sK4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK4)))
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_9 ),
    inference(resolution,[],[f59,f120])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_tmap_1)).

fof(f333,plain,
    ( spl6_35
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f266,f252,f143,f138,f103,f98,f93,f88,f83,f78,f331])).

fof(f252,plain,
    ( spl6_26
  <=> ! [X1,X0,X2] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f265,f80])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f264,f85])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f263,f90])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f262,f95])).

fof(f262,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f261,f100])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f260,f105])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f259,f140])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(resolution,[],[f253,f145])).

fof(f253,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ m1_pre_topc(X0,X1)
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f252])).

fof(f311,plain,
    ( spl6_33
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f241,f133,f128,f123,f113,f108,f88,f83,f78,f309])).

fof(f241,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f240,f80])).

fof(f240,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f239,f85])).

fof(f239,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f238,f90])).

fof(f238,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f237,f110])).

fof(f237,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f236,f125])).

fof(f236,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f235,f115])).

fof(f235,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f234,f130])).

fof(f234,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12 ),
    inference(superposition,[],[f72,f135])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f290,plain,
    ( spl6_31
    | ~ spl6_11
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f268,f256,f128,f287])).

fof(f256,plain,
    ( spl6_27
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f268,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ spl6_11
    | ~ spl6_27 ),
    inference(resolution,[],[f257,f130])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f256])).

fof(f285,plain,
    ( spl6_30
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f228,f133,f128,f123,f113,f108,f88,f83,f78,f283])).

fof(f228,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f227,f80])).

fof(f227,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f226,f85])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f225,f90])).

fof(f225,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f224,f110])).

fof(f224,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f223,f125])).

fof(f223,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f222,f115])).

fof(f222,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f221,f130])).

fof(f221,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12 ),
    inference(superposition,[],[f71,f135])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f281,plain,
    ( spl6_29
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f267,f256,f123,f278])).

fof(f267,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(resolution,[],[f257,f125])).

fof(f276,plain,
    ( spl6_28
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f215,f118,f274])).

fof(f215,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4)
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl6_9 ),
    inference(resolution,[],[f58,f120])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f258,plain,
    ( spl6_27
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f250,f243,f176,f88,f83,f78,f256])).

fof(f243,plain,
    ( spl6_25
  <=> ! [X1,X0] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f249,f80])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f248,f85])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_17
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f247,f90])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_17
    | ~ spl6_25 ),
    inference(resolution,[],[f244,f178])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(X1,X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f243])).

fof(f254,plain,
    ( spl6_26
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f199,f118,f252])).

fof(f199,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_9 ),
    inference(resolution,[],[f60,f120])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f245,plain,
    ( spl6_25
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f233,f218,f143,f138,f103,f98,f93,f243])).

fof(f218,plain,
    ( spl6_24
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK4))
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f232,f95])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f231,f100])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f230,f105])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f229,f140])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_14
    | ~ spl6_24 ),
    inference(resolution,[],[f219,f145])).

fof(f219,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK4))
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f218])).

fof(f220,plain,
    ( spl6_24
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f196,f118,f218])).

fof(f196,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK4))
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl6_9 ),
    inference(resolution,[],[f66,f120])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f214,plain,
    ( spl6_22
    | spl6_23
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f191,f187,f212,f208])).

fof(f187,plain,
    ( spl6_19
  <=> sP5(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_2(X0,X1,X2)
        | ~ v1_funct_1(X0)
        | v1_xboole_0(u1_struct_0(sK1))
        | v1_xboole_0(X2)
        | r1_funct_2(X1,X2,u1_struct_0(sK0),u1_struct_0(sK1),X0,X0) )
    | ~ spl6_19 ),
    inference(resolution,[],[f189,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1)
      | r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    inference(general_splitting,[],[f69,f74_D])).

fof(f74,plain,(
    ! [X2,X5,X3] :
      ( ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | sP5(X3,X2) ) ),
    inference(cnf_transformation,[],[f74_D])).

fof(f74_D,plain,(
    ! [X2,X3] :
      ( ! [X5] :
          ( ~ v1_funct_1(X5)
          | ~ v1_funct_2(X5,X2,X3)
          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    <=> ~ sP5(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

fof(f189,plain,
    ( sP5(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f187])).

fof(f190,plain,
    ( spl6_19
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f155,f150,f143,f138,f187])).

fof(f150,plain,
    ( spl6_15
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK4,X0,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | sP5(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f155,plain,
    ( sP5(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f154,f140])).

fof(f154,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | sP5(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(resolution,[],[f151,f145])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK4,X0,X1)
        | sP5(X1,X0) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f150])).

fof(f185,plain,
    ( ~ spl6_18
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f180,f133,f182])).

fof(f180,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f55,f135])).

fof(f55,plain,(
    ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & sK0 = k1_tsep_1(sK0,sK2,sK3)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f38,f37,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & k1_tsep_1(X0,X2,X3) = X0
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & sK0 = k1_tsep_1(sK0,X2,X3)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3)))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & sK0 = k1_tsep_1(sK0,X2,X3)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,X2,X3,k2_tmap_1(sK0,sK1,X4,X2),k2_tmap_1(sK0,sK1,X4,X3)))
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & sK0 = k1_tsep_1(sK0,X2,X3)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,X2,X3,k2_tmap_1(sK0,sK1,X4,X2),k2_tmap_1(sK0,sK1,X4,X3)))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & sK0 = k1_tsep_1(sK0,X2,X3)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,X3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,X3)))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & sK0 = k1_tsep_1(sK0,sK2,X3)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,X3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,X3)))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & sK0 = k1_tsep_1(sK0,sK2,X3)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,sK3)))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & sK0 = k1_tsep_1(sK0,sK2,sK3)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X4] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,sK3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
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
                   => ( k1_tsep_1(X0,X2,X3) = X0
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
                 => ( k1_tsep_1(X0,X2,X3) = X0
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_tmap_1)).

fof(f179,plain,
    ( spl6_17
    | spl6_1
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f174,f133,f128,f123,f113,f108,f88,f78,f176])).

fof(f174,plain,
    ( m1_pre_topc(sK0,sK0)
    | spl6_1
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f173,f80])).

fof(f173,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f172,f90])).

fof(f172,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f171,f110])).

fof(f171,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f170,f125])).

fof(f170,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f169,f115])).

fof(f169,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f168,f130])).

fof(f168,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_12 ),
    inference(superposition,[],[f63,f135])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f152,plain,
    ( spl6_15
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f147,f118,f150])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK4,X0,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | sP5(X1,X0) )
    | ~ spl6_9 ),
    inference(resolution,[],[f74,f120])).

fof(f146,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f54,f143])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f141,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f53,f138])).

fof(f53,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f136,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f51,f133])).

fof(f51,plain,(
    sK0 = k1_tsep_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f131,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f50,f128])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f126,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f48,f123])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f121,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f52,f118])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f116,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f49,f113])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f111,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f47,f108])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f46,f103])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f45,f98])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f44,f93])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f43,f88])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f42,f83])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f41,f78])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:43:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (28902)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.46  % (28894)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (28892)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (28900)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (28890)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (28889)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (28885)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (28883)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (28882)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (28903)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (28888)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (28884)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (28881)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (28891)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (28898)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (28896)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (28881)Refutation not found, incomplete strategy% (28881)------------------------------
% 0.21/0.52  % (28881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28881)Memory used [KB]: 10746
% 0.21/0.52  % (28881)Time elapsed: 0.115 s
% 0.21/0.52  % (28881)------------------------------
% 0.21/0.52  % (28881)------------------------------
% 0.21/0.52  % (28886)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (28895)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (28899)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (28906)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (28897)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (28904)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (28905)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (28887)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (28886)Refutation not found, incomplete strategy% (28886)------------------------------
% 0.21/0.54  % (28886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28886)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28886)Memory used [KB]: 6268
% 0.21/0.54  % (28886)Time elapsed: 0.137 s
% 0.21/0.54  % (28886)------------------------------
% 0.21/0.54  % (28886)------------------------------
% 0.21/0.54  % (28901)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (28893)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.55  % (28887)Refutation not found, incomplete strategy% (28887)------------------------------
% 0.21/0.55  % (28887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28887)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28887)Memory used [KB]: 10874
% 0.21/0.55  % (28887)Time elapsed: 0.116 s
% 0.21/0.55  % (28887)------------------------------
% 0.21/0.55  % (28887)------------------------------
% 2.09/0.64  % (28890)Refutation not found, incomplete strategy% (28890)------------------------------
% 2.09/0.64  % (28890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.64  % (28890)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.64  
% 2.09/0.64  % (28890)Memory used [KB]: 6396
% 2.09/0.64  % (28890)Time elapsed: 0.220 s
% 2.09/0.64  % (28890)------------------------------
% 2.09/0.64  % (28890)------------------------------
% 2.09/0.69  % (28883)Refutation found. Thanks to Tanya!
% 2.09/0.69  % SZS status Theorem for theBenchmark
% 2.09/0.69  % SZS output start Proof for theBenchmark
% 2.09/0.69  fof(f2141,plain,(
% 2.09/0.69    $false),
% 2.09/0.69    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f152,f179,f185,f190,f214,f220,f245,f254,f258,f276,f281,f285,f290,f311,f333,f349,f354,f367,f371,f393,f397,f419,f427,f454,f458,f463,f572,f601,f636,f651,f1988,f2002,f2047,f2069,f2123,f2128,f2135,f2140])).
% 2.09/0.69  fof(f2140,plain,(
% 2.09/0.69    ~spl6_6 | spl6_168),
% 2.09/0.69    inference(avatar_contradiction_clause,[],[f2139])).
% 2.09/0.69  fof(f2139,plain,(
% 2.09/0.69    $false | (~spl6_6 | spl6_168)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2137,f105])).
% 2.09/0.69  fof(f105,plain,(
% 2.09/0.69    l1_pre_topc(sK1) | ~spl6_6),
% 2.09/0.69    inference(avatar_component_clause,[],[f103])).
% 2.09/0.69  fof(f103,plain,(
% 2.09/0.69    spl6_6 <=> l1_pre_topc(sK1)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.09/0.69  fof(f2137,plain,(
% 2.09/0.69    ~l1_pre_topc(sK1) | spl6_168),
% 2.09/0.69    inference(resolution,[],[f2134,f56])).
% 2.09/0.69  fof(f56,plain,(
% 2.09/0.69    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f15])).
% 2.09/0.69  fof(f15,plain,(
% 2.09/0.69    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.09/0.69    inference(ennf_transformation,[],[f2])).
% 2.09/0.69  fof(f2,axiom,(
% 2.09/0.69    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.09/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.09/0.69  fof(f2134,plain,(
% 2.09/0.69    ~l1_struct_0(sK1) | spl6_168),
% 2.09/0.69    inference(avatar_component_clause,[],[f2132])).
% 2.09/0.69  fof(f2132,plain,(
% 2.09/0.69    spl6_168 <=> l1_struct_0(sK1)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_168])])).
% 2.09/0.69  fof(f2135,plain,(
% 2.09/0.69    ~spl6_168 | spl6_4 | ~spl6_22),
% 2.09/0.69    inference(avatar_split_clause,[],[f2130,f208,f93,f2132])).
% 2.09/0.69  fof(f93,plain,(
% 2.09/0.69    spl6_4 <=> v2_struct_0(sK1)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.09/0.69  fof(f208,plain,(
% 2.09/0.69    spl6_22 <=> v1_xboole_0(u1_struct_0(sK1))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 2.09/0.69  fof(f2130,plain,(
% 2.09/0.69    ~l1_struct_0(sK1) | (spl6_4 | ~spl6_22)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2129,f95])).
% 2.09/0.69  fof(f95,plain,(
% 2.09/0.69    ~v2_struct_0(sK1) | spl6_4),
% 2.09/0.69    inference(avatar_component_clause,[],[f93])).
% 2.09/0.69  fof(f2129,plain,(
% 2.09/0.69    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl6_22),
% 2.09/0.69    inference(resolution,[],[f210,f57])).
% 2.09/0.69  fof(f57,plain,(
% 2.09/0.69    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f17])).
% 2.09/0.69  fof(f17,plain,(
% 2.09/0.69    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.09/0.69    inference(flattening,[],[f16])).
% 2.09/0.69  fof(f16,plain,(
% 2.09/0.69    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.09/0.69    inference(ennf_transformation,[],[f3])).
% 2.09/0.69  fof(f3,axiom,(
% 2.09/0.69    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.09/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 2.09/0.69  fof(f210,plain,(
% 2.09/0.69    v1_xboole_0(u1_struct_0(sK1)) | ~spl6_22),
% 2.09/0.69    inference(avatar_component_clause,[],[f208])).
% 2.09/0.69  fof(f2128,plain,(
% 2.09/0.69    spl6_22 | ~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_23 | spl6_167),
% 2.09/0.69    inference(avatar_split_clause,[],[f2127,f2120,f212,f143,f138,f118,f208])).
% 2.09/0.69  fof(f118,plain,(
% 2.09/0.69    spl6_9 <=> v1_funct_1(sK4)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.09/0.69  fof(f138,plain,(
% 2.09/0.69    spl6_13 <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.09/0.69  fof(f143,plain,(
% 2.09/0.69    spl6_14 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.09/0.69  fof(f212,plain,(
% 2.09/0.69    spl6_23 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_funct_2(X1,X2,u1_struct_0(sK0),u1_struct_0(sK1),X0,X0) | v1_xboole_0(X2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 2.09/0.69  fof(f2120,plain,(
% 2.09/0.69    spl6_167 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_167])])).
% 2.09/0.69  fof(f2127,plain,(
% 2.09/0.69    v1_xboole_0(u1_struct_0(sK1)) | (~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_23 | spl6_167)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2126,f140])).
% 2.09/0.69  fof(f140,plain,(
% 2.09/0.69    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl6_13),
% 2.09/0.69    inference(avatar_component_clause,[],[f138])).
% 2.09/0.69  fof(f2126,plain,(
% 2.09/0.69    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_9 | ~spl6_14 | ~spl6_23 | spl6_167)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2125,f120])).
% 2.09/0.69  fof(f120,plain,(
% 2.09/0.69    v1_funct_1(sK4) | ~spl6_9),
% 2.09/0.69    inference(avatar_component_clause,[],[f118])).
% 2.09/0.69  fof(f2125,plain,(
% 2.09/0.69    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_14 | ~spl6_23 | spl6_167)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2124,f145])).
% 2.09/0.69  fof(f145,plain,(
% 2.09/0.69    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl6_14),
% 2.09/0.69    inference(avatar_component_clause,[],[f143])).
% 2.09/0.69  fof(f2124,plain,(
% 2.09/0.69    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_23 | spl6_167)),
% 2.09/0.69    inference(resolution,[],[f2122,f213])).
% 2.09/0.69  fof(f213,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (r1_funct_2(X1,X2,u1_struct_0(sK0),u1_struct_0(sK1),X0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(X2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2)) ) | ~spl6_23),
% 2.09/0.69    inference(avatar_component_clause,[],[f212])).
% 2.09/0.69  fof(f2122,plain,(
% 2.09/0.69    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) | spl6_167),
% 2.09/0.69    inference(avatar_component_clause,[],[f2120])).
% 2.09/0.69  fof(f2123,plain,(
% 2.09/0.69    ~spl6_167 | spl6_18 | ~spl6_162),
% 2.09/0.69    inference(avatar_split_clause,[],[f2080,f1977,f182,f2120])).
% 2.09/0.69  fof(f182,plain,(
% 2.09/0.69    spl6_18 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 2.09/0.69  fof(f1977,plain,(
% 2.09/0.69    spl6_162 <=> sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_162])])).
% 2.09/0.69  fof(f2080,plain,(
% 2.09/0.69    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) | (spl6_18 | ~spl6_162)),
% 2.09/0.69    inference(backward_demodulation,[],[f184,f1979])).
% 2.09/0.69  fof(f1979,plain,(
% 2.09/0.69    sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) | ~spl6_162),
% 2.09/0.69    inference(avatar_component_clause,[],[f1977])).
% 2.09/0.69  fof(f184,plain,(
% 2.09/0.69    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) | spl6_18),
% 2.09/0.69    inference(avatar_component_clause,[],[f182])).
% 2.09/0.69  fof(f2069,plain,(
% 2.09/0.69    spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_30 | ~spl6_46 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_164),
% 2.09/0.69    inference(avatar_contradiction_clause,[],[f2068])).
% 2.09/0.69  fof(f2068,plain,(
% 2.09/0.69    $false | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_30 | ~spl6_46 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_164)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2067,f95])).
% 2.09/0.69  fof(f2067,plain,(
% 2.09/0.69    v2_struct_0(sK1) | (~spl6_5 | ~spl6_6 | ~spl6_30 | ~spl6_46 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_164)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2066,f100])).
% 2.09/0.69  fof(f100,plain,(
% 2.09/0.69    v2_pre_topc(sK1) | ~spl6_5),
% 2.09/0.69    inference(avatar_component_clause,[],[f98])).
% 2.09/0.69  fof(f98,plain,(
% 2.09/0.69    spl6_5 <=> v2_pre_topc(sK1)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.09/0.69  fof(f2066,plain,(
% 2.09/0.69    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_6 | ~spl6_30 | ~spl6_46 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_164)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2065,f105])).
% 2.09/0.69  fof(f2065,plain,(
% 2.09/0.69    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_30 | ~spl6_46 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_164)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2064,f426])).
% 2.09/0.69  fof(f426,plain,(
% 2.09/0.69    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~spl6_46),
% 2.09/0.69    inference(avatar_component_clause,[],[f424])).
% 2.09/0.69  fof(f424,plain,(
% 2.09/0.69    spl6_46 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 2.09/0.69  fof(f2064,plain,(
% 2.09/0.69    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_30 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_164)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2063,f571])).
% 2.09/0.69  fof(f571,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl6_53),
% 2.09/0.69    inference(avatar_component_clause,[],[f569])).
% 2.09/0.69  fof(f569,plain,(
% 2.09/0.69    spl6_53 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 2.09/0.69  fof(f2063,plain,(
% 2.09/0.69    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_30 | ~spl6_50 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_164)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2062,f635])).
% 2.09/0.69  fof(f635,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~spl6_60),
% 2.09/0.69    inference(avatar_component_clause,[],[f633])).
% 2.09/0.69  fof(f633,plain,(
% 2.09/0.69    spl6_60 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 2.09/0.69  fof(f2062,plain,(
% 2.09/0.69    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_30 | ~spl6_50 | ~spl6_54 | ~spl6_61 | spl6_164)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2061,f462])).
% 2.09/0.69  fof(f462,plain,(
% 2.09/0.69    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~spl6_50),
% 2.09/0.69    inference(avatar_component_clause,[],[f460])).
% 2.09/0.69  fof(f460,plain,(
% 2.09/0.69    spl6_50 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 2.09/0.69  fof(f2061,plain,(
% 2.09/0.69    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_30 | ~spl6_54 | ~spl6_61 | spl6_164)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2060,f600])).
% 2.09/0.69  fof(f600,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl6_54),
% 2.09/0.69    inference(avatar_component_clause,[],[f598])).
% 2.09/0.69  fof(f598,plain,(
% 2.09/0.69    spl6_54 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 2.09/0.69  fof(f2060,plain,(
% 2.09/0.69    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_30 | ~spl6_61 | spl6_164)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2058,f650])).
% 2.09/0.69  fof(f650,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl6_61),
% 2.09/0.69    inference(avatar_component_clause,[],[f648])).
% 2.09/0.69  fof(f648,plain,(
% 2.09/0.69    spl6_61 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 2.09/0.69  fof(f2058,plain,(
% 2.09/0.69    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_30 | spl6_164)),
% 2.09/0.69    inference(resolution,[],[f1987,f284])).
% 2.09/0.69  fof(f284,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_30),
% 2.09/0.69    inference(avatar_component_clause,[],[f283])).
% 2.09/0.69  fof(f283,plain,(
% 2.09/0.69    spl6_30 <=> ! [X1,X0,X2] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 2.09/0.69  fof(f1987,plain,(
% 2.09/0.69    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | spl6_164),
% 2.09/0.69    inference(avatar_component_clause,[],[f1985])).
% 2.09/0.69  fof(f1985,plain,(
% 2.09/0.69    spl6_164 <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_164])])).
% 2.09/0.69  fof(f2047,plain,(
% 2.09/0.69    spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_33 | ~spl6_46 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_163),
% 2.09/0.69    inference(avatar_contradiction_clause,[],[f2046])).
% 2.09/0.69  fof(f2046,plain,(
% 2.09/0.69    $false | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_33 | ~spl6_46 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_163)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2045,f95])).
% 2.09/0.69  fof(f2045,plain,(
% 2.09/0.69    v2_struct_0(sK1) | (~spl6_5 | ~spl6_6 | ~spl6_33 | ~spl6_46 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_163)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2044,f100])).
% 2.09/0.69  fof(f2044,plain,(
% 2.09/0.69    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_6 | ~spl6_33 | ~spl6_46 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_163)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2043,f105])).
% 2.09/0.69  fof(f2043,plain,(
% 2.09/0.69    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_33 | ~spl6_46 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_163)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2042,f426])).
% 2.09/0.69  fof(f2042,plain,(
% 2.09/0.69    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_33 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_163)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2041,f571])).
% 2.09/0.69  fof(f2041,plain,(
% 2.09/0.69    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_33 | ~spl6_50 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_163)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2040,f635])).
% 2.09/0.69  fof(f2040,plain,(
% 2.09/0.69    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_33 | ~spl6_50 | ~spl6_54 | ~spl6_61 | spl6_163)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2039,f462])).
% 2.09/0.69  fof(f2039,plain,(
% 2.09/0.69    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_33 | ~spl6_54 | ~spl6_61 | spl6_163)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2038,f600])).
% 2.09/0.69  fof(f2038,plain,(
% 2.09/0.69    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_33 | ~spl6_61 | spl6_163)),
% 2.09/0.69    inference(subsumption_resolution,[],[f2036,f650])).
% 2.09/0.69  fof(f2036,plain,(
% 2.09/0.69    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_33 | spl6_163)),
% 2.09/0.69    inference(resolution,[],[f1983,f310])).
% 2.09/0.69  fof(f310,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_33),
% 2.09/0.69    inference(avatar_component_clause,[],[f309])).
% 2.09/0.69  fof(f309,plain,(
% 2.09/0.69    spl6_33 <=> ! [X1,X0,X2] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 2.09/0.69  fof(f1983,plain,(
% 2.09/0.69    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl6_163),
% 2.09/0.69    inference(avatar_component_clause,[],[f1981])).
% 2.09/0.69  fof(f1981,plain,(
% 2.09/0.69    spl6_163 <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_163])])).
% 2.09/0.69  fof(f2002,plain,(
% 2.09/0.69    spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_46 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_161),
% 2.09/0.69    inference(avatar_contradiction_clause,[],[f2000])).
% 2.09/0.69  fof(f2000,plain,(
% 2.09/0.69    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_46 | ~spl6_50 | ~spl6_53 | ~spl6_54 | ~spl6_60 | ~spl6_61 | spl6_161)),
% 2.09/0.69    inference(unit_resulting_resolution,[],[f80,f85,f90,f95,f100,f105,f110,f115,f125,f130,f426,f462,f571,f600,f635,f650,f1975,f70])).
% 2.09/0.69  fof(f70,plain,(
% 2.09/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f33])).
% 2.09/0.69  fof(f33,plain,(
% 2.09/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.69    inference(flattening,[],[f32])).
% 2.09/0.69  fof(f32,plain,(
% 2.09/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.69    inference(ennf_transformation,[],[f7])).
% 2.09/0.69  fof(f7,axiom,(
% 2.09/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.09/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 2.09/0.69  fof(f1975,plain,(
% 2.09/0.69    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) | spl6_161),
% 2.09/0.69    inference(avatar_component_clause,[],[f1973])).
% 2.09/0.69  fof(f1973,plain,(
% 2.09/0.69    spl6_161 <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_161])])).
% 2.09/0.69  fof(f130,plain,(
% 2.09/0.69    m1_pre_topc(sK3,sK0) | ~spl6_11),
% 2.09/0.69    inference(avatar_component_clause,[],[f128])).
% 2.09/0.69  fof(f128,plain,(
% 2.09/0.69    spl6_11 <=> m1_pre_topc(sK3,sK0)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.09/0.69  fof(f125,plain,(
% 2.09/0.69    m1_pre_topc(sK2,sK0) | ~spl6_10),
% 2.09/0.69    inference(avatar_component_clause,[],[f123])).
% 2.09/0.69  fof(f123,plain,(
% 2.09/0.69    spl6_10 <=> m1_pre_topc(sK2,sK0)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.09/0.69  fof(f115,plain,(
% 2.09/0.69    ~v2_struct_0(sK3) | spl6_8),
% 2.09/0.69    inference(avatar_component_clause,[],[f113])).
% 2.09/0.69  fof(f113,plain,(
% 2.09/0.69    spl6_8 <=> v2_struct_0(sK3)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.09/0.69  fof(f110,plain,(
% 2.09/0.69    ~v2_struct_0(sK2) | spl6_7),
% 2.09/0.69    inference(avatar_component_clause,[],[f108])).
% 2.09/0.69  fof(f108,plain,(
% 2.09/0.69    spl6_7 <=> v2_struct_0(sK2)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.09/0.69  fof(f90,plain,(
% 2.09/0.69    l1_pre_topc(sK0) | ~spl6_3),
% 2.09/0.69    inference(avatar_component_clause,[],[f88])).
% 2.09/0.69  fof(f88,plain,(
% 2.09/0.69    spl6_3 <=> l1_pre_topc(sK0)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.09/0.69  fof(f85,plain,(
% 2.09/0.69    v2_pre_topc(sK0) | ~spl6_2),
% 2.09/0.69    inference(avatar_component_clause,[],[f83])).
% 2.09/0.69  fof(f83,plain,(
% 2.09/0.69    spl6_2 <=> v2_pre_topc(sK0)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.09/0.69  fof(f80,plain,(
% 2.09/0.69    ~v2_struct_0(sK0) | spl6_1),
% 2.09/0.69    inference(avatar_component_clause,[],[f78])).
% 2.09/0.69  fof(f78,plain,(
% 2.09/0.69    spl6_1 <=> v2_struct_0(sK0)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.09/0.69  fof(f1988,plain,(
% 2.09/0.69    ~spl6_161 | spl6_162 | ~spl6_163 | ~spl6_164 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_45 | ~spl6_48 | ~spl6_49),
% 2.09/0.69    inference(avatar_split_clause,[],[f539,f456,f451,f416,f143,f138,f103,f98,f93,f1985,f1981,f1977,f1973])).
% 2.09/0.69  fof(f416,plain,(
% 2.09/0.69    spl6_45 <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 2.09/0.69  fof(f451,plain,(
% 2.09/0.69    spl6_48 <=> k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 2.09/0.69  fof(f456,plain,(
% 2.09/0.69    spl6_49 <=> ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | sK4 = k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)) | ~m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 2.09/0.69  fof(f539,plain,(
% 2.09/0.69    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_45 | ~spl6_48 | ~spl6_49)),
% 2.09/0.69    inference(forward_demodulation,[],[f538,f418])).
% 2.09/0.69  fof(f418,plain,(
% 2.09/0.69    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~spl6_45),
% 2.09/0.69    inference(avatar_component_clause,[],[f416])).
% 2.09/0.69  fof(f538,plain,(
% 2.09/0.69    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_45 | ~spl6_48 | ~spl6_49)),
% 2.09/0.69    inference(forward_demodulation,[],[f537,f418])).
% 2.09/0.69  fof(f537,plain,(
% 2.09/0.69    sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_45 | ~spl6_48 | ~spl6_49)),
% 2.09/0.69    inference(forward_demodulation,[],[f536,f418])).
% 2.09/0.69  fof(f536,plain,(
% 2.09/0.69    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_45 | ~spl6_48 | ~spl6_49)),
% 2.09/0.69    inference(forward_demodulation,[],[f535,f418])).
% 2.09/0.69  fof(f535,plain,(
% 2.09/0.69    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_48 | ~spl6_49)),
% 2.09/0.69    inference(subsumption_resolution,[],[f534,f140])).
% 2.09/0.69  fof(f534,plain,(
% 2.09/0.69    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_14 | ~spl6_48 | ~spl6_49)),
% 2.09/0.69    inference(subsumption_resolution,[],[f533,f95])).
% 2.09/0.69  fof(f533,plain,(
% 2.09/0.69    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))) | v2_struct_0(sK1) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_5 | ~spl6_6 | ~spl6_14 | ~spl6_48 | ~spl6_49)),
% 2.09/0.69    inference(subsumption_resolution,[],[f532,f100])).
% 2.09/0.69  fof(f532,plain,(
% 2.09/0.69    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_6 | ~spl6_14 | ~spl6_48 | ~spl6_49)),
% 2.09/0.69    inference(subsumption_resolution,[],[f531,f105])).
% 2.09/0.69  fof(f531,plain,(
% 2.09/0.69    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_14 | ~spl6_48 | ~spl6_49)),
% 2.09/0.69    inference(subsumption_resolution,[],[f527,f145])).
% 2.09/0.69  fof(f527,plain,(
% 2.09/0.69    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_48 | ~spl6_49)),
% 2.09/0.69    inference(superposition,[],[f457,f453])).
% 2.09/0.69  fof(f453,plain,(
% 2.09/0.69    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | ~spl6_48),
% 2.09/0.69    inference(avatar_component_clause,[],[f451])).
% 2.09/0.69  fof(f457,plain,(
% 2.09/0.69    ( ! [X0] : (~v1_funct_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | sK4 = k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)) | ~m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))) ) | ~spl6_49),
% 2.09/0.69    inference(avatar_component_clause,[],[f456])).
% 2.09/0.69  fof(f651,plain,(
% 2.09/0.69    spl6_61 | spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48),
% 2.09/0.69    inference(avatar_split_clause,[],[f556,f451,f176,f143,f138,f128,f118,f103,f98,f93,f88,f83,f78,f648])).
% 2.09/0.69  fof(f176,plain,(
% 2.09/0.69    spl6_17 <=> m1_pre_topc(sK0,sK0)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 2.09/0.69  fof(f556,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f555,f80])).
% 2.09/0.69  fof(f555,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f554,f85])).
% 2.09/0.69  fof(f554,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f553,f90])).
% 2.09/0.69  fof(f553,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f552,f95])).
% 2.09/0.69  fof(f552,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f551,f100])).
% 2.09/0.69  fof(f551,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f550,f105])).
% 2.09/0.69  fof(f550,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f549,f178])).
% 2.09/0.69  fof(f178,plain,(
% 2.09/0.69    m1_pre_topc(sK0,sK0) | ~spl6_17),
% 2.09/0.69    inference(avatar_component_clause,[],[f176])).
% 2.09/0.69  fof(f549,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f548,f130])).
% 2.09/0.69  fof(f548,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f547,f120])).
% 2.09/0.69  fof(f547,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_13 | ~spl6_14 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f546,f140])).
% 2.09/0.69  fof(f546,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_14 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f529,f145])).
% 2.09/0.69  fof(f529,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_48),
% 2.09/0.69    inference(superposition,[],[f68,f453])).
% 2.09/0.69  fof(f68,plain,(
% 2.09/0.69    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f29])).
% 2.09/0.69  fof(f29,plain,(
% 2.09/0.69    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.69    inference(flattening,[],[f28])).
% 2.09/0.69  fof(f28,plain,(
% 2.09/0.69    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.69    inference(ennf_transformation,[],[f9])).
% 2.09/0.69  fof(f9,axiom,(
% 2.09/0.69    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.09/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.09/0.69  fof(f636,plain,(
% 2.09/0.69    spl6_60 | spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45),
% 2.09/0.69    inference(avatar_split_clause,[],[f515,f416,f176,f143,f138,f123,f118,f103,f98,f93,f88,f83,f78,f633])).
% 2.09/0.69  fof(f515,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f514,f80])).
% 2.09/0.69  fof(f514,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f513,f85])).
% 2.09/0.69  fof(f513,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f512,f90])).
% 2.09/0.69  fof(f512,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f511,f95])).
% 2.09/0.69  fof(f511,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f510,f100])).
% 2.09/0.69  fof(f510,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f509,f105])).
% 2.09/0.69  fof(f509,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f508,f178])).
% 2.09/0.69  fof(f508,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f507,f125])).
% 2.09/0.69  fof(f507,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f506,f120])).
% 2.09/0.69  fof(f506,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_13 | ~spl6_14 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f505,f140])).
% 2.09/0.69  fof(f505,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_14 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f493,f145])).
% 2.09/0.69  fof(f493,plain,(
% 2.09/0.69    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_45),
% 2.09/0.69    inference(superposition,[],[f68,f418])).
% 2.09/0.69  fof(f601,plain,(
% 2.09/0.69    spl6_54 | spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48),
% 2.09/0.69    inference(avatar_split_clause,[],[f567,f451,f176,f143,f138,f128,f118,f103,f98,f93,f88,f83,f78,f598])).
% 2.09/0.69  fof(f567,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f566,f80])).
% 2.09/0.69  fof(f566,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f565,f85])).
% 2.09/0.69  fof(f565,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f564,f90])).
% 2.09/0.69  fof(f564,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f563,f95])).
% 2.09/0.69  fof(f563,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f562,f100])).
% 2.09/0.69  fof(f562,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f561,f105])).
% 2.09/0.69  fof(f561,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f560,f178])).
% 2.09/0.69  fof(f560,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f559,f130])).
% 2.09/0.69  fof(f559,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f558,f120])).
% 2.09/0.69  fof(f558,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_13 | ~spl6_14 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f557,f140])).
% 2.09/0.69  fof(f557,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_14 | ~spl6_48)),
% 2.09/0.69    inference(subsumption_resolution,[],[f530,f145])).
% 2.09/0.69  fof(f530,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_48),
% 2.09/0.69    inference(superposition,[],[f67,f453])).
% 2.09/0.69  fof(f67,plain,(
% 2.09/0.69    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f29])).
% 2.09/0.69  fof(f572,plain,(
% 2.09/0.69    spl6_53 | spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45),
% 2.09/0.69    inference(avatar_split_clause,[],[f526,f416,f176,f143,f138,f123,f118,f103,f98,f93,f88,f83,f78,f569])).
% 2.09/0.69  fof(f526,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f525,f80])).
% 2.09/0.69  fof(f525,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f524,f85])).
% 2.09/0.69  fof(f524,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f523,f90])).
% 2.09/0.69  fof(f523,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f522,f95])).
% 2.09/0.69  fof(f522,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f521,f100])).
% 2.09/0.69  fof(f521,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f520,f105])).
% 2.09/0.69  fof(f520,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f519,f178])).
% 2.09/0.69  fof(f519,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_13 | ~spl6_14 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f518,f125])).
% 2.09/0.69  fof(f518,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f517,f120])).
% 2.09/0.69  fof(f517,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_13 | ~spl6_14 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f516,f140])).
% 2.09/0.69  fof(f516,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_14 | ~spl6_45)),
% 2.09/0.69    inference(subsumption_resolution,[],[f494,f145])).
% 2.09/0.69  fof(f494,plain,(
% 2.09/0.69    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_45),
% 2.09/0.69    inference(superposition,[],[f67,f418])).
% 2.09/0.69  fof(f463,plain,(
% 2.09/0.69    spl6_50 | ~spl6_11 | ~spl6_31 | ~spl6_38 | ~spl6_43),
% 2.09/0.69    inference(avatar_split_clause,[],[f449,f395,f364,f287,f128,f460])).
% 2.09/0.69  fof(f287,plain,(
% 2.09/0.69    spl6_31 <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 2.09/0.69  fof(f364,plain,(
% 2.09/0.69    spl6_38 <=> k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 2.09/0.69  fof(f395,plain,(
% 2.09/0.69    spl6_43 <=> ! [X0] : (k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 2.09/0.69  fof(f449,plain,(
% 2.09/0.69    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | (~spl6_11 | ~spl6_31 | ~spl6_38 | ~spl6_43)),
% 2.09/0.69    inference(backward_demodulation,[],[f289,f406])).
% 2.09/0.69  fof(f406,plain,(
% 2.09/0.69    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | (~spl6_11 | ~spl6_38 | ~spl6_43)),
% 2.09/0.69    inference(forward_demodulation,[],[f402,f366])).
% 2.09/0.69  fof(f366,plain,(
% 2.09/0.69    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~spl6_38),
% 2.09/0.69    inference(avatar_component_clause,[],[f364])).
% 2.09/0.69  fof(f402,plain,(
% 2.09/0.69    k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | (~spl6_11 | ~spl6_43)),
% 2.09/0.69    inference(resolution,[],[f396,f130])).
% 2.09/0.69  fof(f396,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl6_43),
% 2.09/0.69    inference(avatar_component_clause,[],[f395])).
% 2.09/0.69  fof(f289,plain,(
% 2.09/0.69    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~spl6_31),
% 2.09/0.69    inference(avatar_component_clause,[],[f287])).
% 2.09/0.69  fof(f458,plain,(
% 2.09/0.69    spl6_49 | ~spl6_9 | ~spl6_42),
% 2.09/0.69    inference(avatar_split_clause,[],[f400,f391,f118,f456])).
% 2.09/0.69  fof(f391,plain,(
% 2.09/0.69    spl6_42 <=> ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 2.09/0.69  fof(f400,plain,(
% 2.09/0.69    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | sK4 = k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)) | ~m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))) ) | (~spl6_9 | ~spl6_42)),
% 2.09/0.69    inference(subsumption_resolution,[],[f399,f120])).
% 2.09/0.69  fof(f399,plain,(
% 2.09/0.69    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | sK4 = k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)) | ~m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~v1_funct_1(sK4)) ) | ~spl6_42),
% 2.09/0.69    inference(duplicate_literal_removal,[],[f398])).
% 2.09/0.69  fof(f398,plain,(
% 2.09/0.69    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | sK4 = k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)) | ~m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(sK4)) ) | ~spl6_42),
% 2.09/0.69    inference(resolution,[],[f392,f64])).
% 2.09/0.69  fof(f64,plain,(
% 2.09/0.69    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f40])).
% 2.09/0.69  fof(f40,plain,(
% 2.09/0.69    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.09/0.69    inference(nnf_transformation,[],[f27])).
% 2.09/0.69  fof(f27,plain,(
% 2.09/0.69    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.09/0.69    inference(flattening,[],[f26])).
% 2.09/0.69  fof(f26,plain,(
% 2.09/0.69    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.09/0.69    inference(ennf_transformation,[],[f1])).
% 2.09/0.69  fof(f1,axiom,(
% 2.09/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.09/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.09/0.69  fof(f392,plain,(
% 2.09/0.69    ( ! [X0] : (r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_42),
% 2.09/0.69    inference(avatar_component_clause,[],[f391])).
% 2.09/0.69  fof(f454,plain,(
% 2.09/0.69    spl6_48 | ~spl6_11 | ~spl6_38 | ~spl6_43),
% 2.09/0.69    inference(avatar_split_clause,[],[f406,f395,f364,f128,f451])).
% 2.09/0.69  fof(f427,plain,(
% 2.09/0.69    spl6_46 | ~spl6_10 | ~spl6_29 | ~spl6_37 | ~spl6_43),
% 2.09/0.69    inference(avatar_split_clause,[],[f414,f395,f351,f278,f123,f424])).
% 2.09/0.69  fof(f278,plain,(
% 2.09/0.69    spl6_29 <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 2.09/0.69  fof(f351,plain,(
% 2.09/0.69    spl6_37 <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 2.09/0.69  fof(f414,plain,(
% 2.09/0.69    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | (~spl6_10 | ~spl6_29 | ~spl6_37 | ~spl6_43)),
% 2.09/0.69    inference(backward_demodulation,[],[f280,f405])).
% 2.09/0.69  fof(f405,plain,(
% 2.09/0.69    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | (~spl6_10 | ~spl6_37 | ~spl6_43)),
% 2.09/0.69    inference(forward_demodulation,[],[f401,f353])).
% 2.09/0.69  fof(f353,plain,(
% 2.09/0.69    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~spl6_37),
% 2.09/0.69    inference(avatar_component_clause,[],[f351])).
% 2.09/0.69  fof(f401,plain,(
% 2.09/0.69    k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl6_10 | ~spl6_43)),
% 2.09/0.69    inference(resolution,[],[f396,f125])).
% 2.09/0.69  fof(f280,plain,(
% 2.09/0.69    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~spl6_29),
% 2.09/0.69    inference(avatar_component_clause,[],[f278])).
% 2.09/0.69  fof(f419,plain,(
% 2.09/0.69    spl6_45 | ~spl6_10 | ~spl6_37 | ~spl6_43),
% 2.09/0.69    inference(avatar_split_clause,[],[f405,f395,f351,f123,f416])).
% 2.09/0.69  fof(f397,plain,(
% 2.09/0.69    spl6_43 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_39),
% 2.09/0.69    inference(avatar_split_clause,[],[f381,f369,f176,f88,f83,f78,f395])).
% 2.09/0.69  fof(f369,plain,(
% 2.09/0.69    spl6_39 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 2.09/0.69  fof(f381,plain,(
% 2.09/0.69    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_39)),
% 2.09/0.69    inference(subsumption_resolution,[],[f380,f80])).
% 2.09/0.69  fof(f380,plain,(
% 2.09/0.69    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_39)),
% 2.09/0.69    inference(subsumption_resolution,[],[f379,f85])).
% 2.09/0.69  fof(f379,plain,(
% 2.09/0.69    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_17 | ~spl6_39)),
% 2.09/0.69    inference(subsumption_resolution,[],[f378,f90])).
% 2.09/0.69  fof(f378,plain,(
% 2.09/0.69    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_17 | ~spl6_39)),
% 2.09/0.69    inference(duplicate_literal_removal,[],[f377])).
% 2.09/0.69  fof(f377,plain,(
% 2.09/0.69    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_17 | ~spl6_39)),
% 2.09/0.69    inference(resolution,[],[f370,f178])).
% 2.09/0.69  fof(f370,plain,(
% 2.09/0.69    ( ! [X0,X1] : (~m1_pre_topc(sK0,X1) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl6_39),
% 2.09/0.69    inference(avatar_component_clause,[],[f369])).
% 2.09/0.69  fof(f393,plain,(
% 2.09/0.69    spl6_42 | spl6_1 | ~spl6_2 | ~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_36),
% 2.09/0.69    inference(avatar_split_clause,[],[f362,f347,f133,f128,f123,f113,f108,f88,f83,f78,f391])).
% 2.09/0.69  fof(f133,plain,(
% 2.09/0.69    spl6_12 <=> sK0 = k1_tsep_1(sK0,sK2,sK3)),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.09/0.69  fof(f347,plain,(
% 2.09/0.69    spl6_36 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),sK4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK4))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 2.09/0.69  fof(f362,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_36)),
% 2.09/0.69    inference(subsumption_resolution,[],[f361,f80])).
% 2.09/0.69  fof(f361,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_36)),
% 2.09/0.69    inference(subsumption_resolution,[],[f360,f85])).
% 2.09/0.69  fof(f360,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_36)),
% 2.09/0.69    inference(subsumption_resolution,[],[f359,f90])).
% 2.09/0.69  fof(f359,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_36)),
% 2.09/0.69    inference(subsumption_resolution,[],[f358,f110])).
% 2.09/0.69  fof(f358,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_36)),
% 2.09/0.69    inference(subsumption_resolution,[],[f357,f125])).
% 2.09/0.69  fof(f357,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_8 | ~spl6_11 | ~spl6_12 | ~spl6_36)),
% 2.09/0.69    inference(subsumption_resolution,[],[f356,f115])).
% 2.09/0.69  fof(f356,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_11 | ~spl6_12 | ~spl6_36)),
% 2.09/0.69    inference(subsumption_resolution,[],[f355,f130])).
% 2.09/0.69  fof(f355,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_12 | ~spl6_36)),
% 2.09/0.69    inference(superposition,[],[f348,f135])).
% 2.09/0.69  fof(f135,plain,(
% 2.09/0.69    sK0 = k1_tsep_1(sK0,sK2,sK3) | ~spl6_12),
% 2.09/0.69    inference(avatar_component_clause,[],[f133])).
% 2.09/0.69  fof(f348,plain,(
% 2.09/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),sK4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK4))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_36),
% 2.09/0.69    inference(avatar_component_clause,[],[f347])).
% 2.09/0.69  fof(f371,plain,(
% 2.09/0.69    spl6_39 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_28),
% 2.09/0.69    inference(avatar_split_clause,[],[f295,f274,f143,f138,f103,f98,f93,f369])).
% 2.09/0.69  fof(f274,plain,(
% 2.09/0.69    spl6_28 <=> ! [X1,X3,X0,X2] : (~m1_pre_topc(X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.09/0.69  fof(f295,plain,(
% 2.09/0.69    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_28)),
% 2.09/0.69    inference(subsumption_resolution,[],[f294,f95])).
% 2.09/0.69  fof(f294,plain,(
% 2.09/0.69    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK0,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_28)),
% 2.09/0.69    inference(subsumption_resolution,[],[f293,f100])).
% 2.09/0.69  fof(f293,plain,(
% 2.09/0.69    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK0,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_28)),
% 2.09/0.69    inference(subsumption_resolution,[],[f292,f105])).
% 2.09/0.69  fof(f292,plain,(
% 2.09/0.69    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl6_13 | ~spl6_14 | ~spl6_28)),
% 2.09/0.69    inference(subsumption_resolution,[],[f291,f140])).
% 2.09/0.69  fof(f291,plain,(
% 2.09/0.69    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl6_14 | ~spl6_28)),
% 2.09/0.69    inference(resolution,[],[f275,f145])).
% 2.09/0.69  fof(f275,plain,(
% 2.09/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl6_28),
% 2.09/0.69    inference(avatar_component_clause,[],[f274])).
% 2.09/0.69  fof(f367,plain,(
% 2.09/0.69    spl6_38 | ~spl6_11 | ~spl6_35),
% 2.09/0.69    inference(avatar_split_clause,[],[f341,f331,f128,f364])).
% 2.09/0.69  fof(f331,plain,(
% 2.09/0.69    spl6_35 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 2.09/0.69  fof(f341,plain,(
% 2.09/0.69    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | (~spl6_11 | ~spl6_35)),
% 2.09/0.69    inference(resolution,[],[f332,f130])).
% 2.09/0.69  fof(f332,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl6_35),
% 2.09/0.69    inference(avatar_component_clause,[],[f331])).
% 2.09/0.69  fof(f354,plain,(
% 2.09/0.69    spl6_37 | ~spl6_10 | ~spl6_35),
% 2.09/0.69    inference(avatar_split_clause,[],[f340,f331,f123,f351])).
% 2.09/0.69  fof(f340,plain,(
% 2.09/0.69    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl6_10 | ~spl6_35)),
% 2.09/0.69    inference(resolution,[],[f332,f125])).
% 2.09/0.69  fof(f349,plain,(
% 2.09/0.69    spl6_36 | ~spl6_9),
% 2.09/0.69    inference(avatar_split_clause,[],[f246,f118,f347])).
% 2.09/0.69  fof(f246,plain,(
% 2.09/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),sK4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK4))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_9),
% 2.09/0.69    inference(resolution,[],[f59,f120])).
% 2.09/0.69  fof(f59,plain,(
% 2.09/0.69    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f21])).
% 2.09/0.69  fof(f21,plain,(
% 2.09/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.69    inference(flattening,[],[f20])).
% 2.09/0.69  fof(f20,plain,(
% 2.09/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.69    inference(ennf_transformation,[],[f10])).
% 2.09/0.69  fof(f10,axiom,(
% 2.09/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))))))))),
% 2.09/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_tmap_1)).
% 2.09/0.69  fof(f333,plain,(
% 2.09/0.69    spl6_35 | spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_26),
% 2.09/0.69    inference(avatar_split_clause,[],[f266,f252,f143,f138,f103,f98,f93,f88,f83,f78,f331])).
% 2.09/0.69  fof(f252,plain,(
% 2.09/0.69    spl6_26 <=> ! [X1,X0,X2] : (~m1_pre_topc(X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.09/0.69  fof(f266,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_26)),
% 2.09/0.69    inference(subsumption_resolution,[],[f265,f80])).
% 2.09/0.69  fof(f265,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_26)),
% 2.09/0.69    inference(subsumption_resolution,[],[f264,f85])).
% 2.09/0.69  fof(f264,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_26)),
% 2.09/0.69    inference(subsumption_resolution,[],[f263,f90])).
% 2.09/0.69  fof(f263,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_26)),
% 2.09/0.69    inference(subsumption_resolution,[],[f262,f95])).
% 2.09/0.69  fof(f262,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_26)),
% 2.09/0.69    inference(subsumption_resolution,[],[f261,f100])).
% 2.09/0.69  fof(f261,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_26)),
% 2.09/0.69    inference(subsumption_resolution,[],[f260,f105])).
% 2.09/0.69  fof(f260,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_13 | ~spl6_14 | ~spl6_26)),
% 2.09/0.69    inference(subsumption_resolution,[],[f259,f140])).
% 2.09/0.69  fof(f259,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_14 | ~spl6_26)),
% 2.09/0.69    inference(resolution,[],[f253,f145])).
% 2.09/0.69  fof(f253,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl6_26),
% 2.09/0.69    inference(avatar_component_clause,[],[f252])).
% 2.09/0.69  fof(f311,plain,(
% 2.09/0.69    spl6_33 | spl6_1 | ~spl6_2 | ~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12),
% 2.09/0.69    inference(avatar_split_clause,[],[f241,f133,f128,f123,f113,f108,f88,f83,f78,f309])).
% 2.09/0.69  fof(f241,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f240,f80])).
% 2.09/0.69  fof(f240,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f239,f85])).
% 2.09/0.69  fof(f239,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f238,f90])).
% 2.09/0.69  fof(f238,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f237,f110])).
% 2.09/0.69  fof(f237,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f236,f125])).
% 2.09/0.69  fof(f236,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_8 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f235,f115])).
% 2.09/0.69  fof(f235,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f234,f130])).
% 2.09/0.69  fof(f234,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_12),
% 2.09/0.69    inference(superposition,[],[f72,f135])).
% 2.09/0.69  fof(f72,plain,(
% 2.09/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f33])).
% 2.09/0.69  fof(f290,plain,(
% 2.09/0.69    spl6_31 | ~spl6_11 | ~spl6_27),
% 2.09/0.69    inference(avatar_split_clause,[],[f268,f256,f128,f287])).
% 2.09/0.69  fof(f256,plain,(
% 2.09/0.69    spl6_27 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.09/0.69  fof(f268,plain,(
% 2.09/0.69    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | (~spl6_11 | ~spl6_27)),
% 2.09/0.69    inference(resolution,[],[f257,f130])).
% 2.09/0.69  fof(f257,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))) ) | ~spl6_27),
% 2.09/0.69    inference(avatar_component_clause,[],[f256])).
% 2.09/0.69  fof(f285,plain,(
% 2.09/0.69    spl6_30 | spl6_1 | ~spl6_2 | ~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12),
% 2.09/0.69    inference(avatar_split_clause,[],[f228,f133,f128,f123,f113,f108,f88,f83,f78,f283])).
% 2.09/0.69  fof(f228,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f227,f80])).
% 2.09/0.69  fof(f227,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f226,f85])).
% 2.09/0.69  fof(f226,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f225,f90])).
% 2.09/0.69  fof(f225,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f224,f110])).
% 2.09/0.69  fof(f224,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f223,f125])).
% 2.09/0.69  fof(f223,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_8 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f222,f115])).
% 2.09/0.69  fof(f222,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f221,f130])).
% 2.09/0.69  fof(f221,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_12),
% 2.09/0.69    inference(superposition,[],[f71,f135])).
% 2.09/0.69  fof(f71,plain,(
% 2.09/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f33])).
% 2.09/0.69  fof(f281,plain,(
% 2.09/0.69    spl6_29 | ~spl6_10 | ~spl6_27),
% 2.09/0.69    inference(avatar_split_clause,[],[f267,f256,f123,f278])).
% 2.09/0.69  fof(f267,plain,(
% 2.09/0.69    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | (~spl6_10 | ~spl6_27)),
% 2.09/0.69    inference(resolution,[],[f257,f125])).
% 2.09/0.69  fof(f276,plain,(
% 2.09/0.69    spl6_28 | ~spl6_9),
% 2.09/0.69    inference(avatar_split_clause,[],[f215,f118,f274])).
% 2.09/0.69  fof(f215,plain,(
% 2.09/0.69    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl6_9),
% 2.09/0.69    inference(resolution,[],[f58,f120])).
% 2.09/0.69  fof(f58,plain,(
% 2.09/0.69    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f19])).
% 2.09/0.69  fof(f19,plain,(
% 2.09/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.69    inference(flattening,[],[f18])).
% 2.09/0.69  fof(f18,plain,(
% 2.09/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.69    inference(ennf_transformation,[],[f6])).
% 2.09/0.69  fof(f6,axiom,(
% 2.09/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 2.09/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 2.09/0.69  fof(f258,plain,(
% 2.09/0.69    spl6_27 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_25),
% 2.09/0.69    inference(avatar_split_clause,[],[f250,f243,f176,f88,f83,f78,f256])).
% 2.09/0.69  fof(f243,plain,(
% 2.09/0.69    spl6_25 <=> ! [X1,X0] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 2.09/0.69  fof(f250,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_25)),
% 2.09/0.69    inference(subsumption_resolution,[],[f249,f80])).
% 2.09/0.69  fof(f249,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_17 | ~spl6_25)),
% 2.09/0.69    inference(subsumption_resolution,[],[f248,f85])).
% 2.09/0.69  fof(f248,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_17 | ~spl6_25)),
% 2.09/0.69    inference(subsumption_resolution,[],[f247,f90])).
% 2.09/0.69  fof(f247,plain,(
% 2.09/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_17 | ~spl6_25)),
% 2.09/0.69    inference(resolution,[],[f244,f178])).
% 2.09/0.69  fof(f244,plain,(
% 2.09/0.69    ( ! [X0,X1] : (~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_25),
% 2.09/0.69    inference(avatar_component_clause,[],[f243])).
% 2.09/0.69  fof(f254,plain,(
% 2.09/0.69    spl6_26 | ~spl6_9),
% 2.09/0.69    inference(avatar_split_clause,[],[f199,f118,f252])).
% 2.09/0.69  fof(f199,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl6_9),
% 2.09/0.69    inference(resolution,[],[f60,f120])).
% 2.09/0.69  fof(f60,plain,(
% 2.09/0.69    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f23])).
% 2.09/0.69  fof(f23,plain,(
% 2.09/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.69    inference(flattening,[],[f22])).
% 2.09/0.69  fof(f22,plain,(
% 2.09/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.69    inference(ennf_transformation,[],[f5])).
% 2.09/0.69  fof(f5,axiom,(
% 2.09/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.09/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.09/0.69  fof(f245,plain,(
% 2.09/0.69    spl6_25 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_24),
% 2.09/0.69    inference(avatar_split_clause,[],[f233,f218,f143,f138,f103,f98,f93,f243])).
% 2.09/0.69  fof(f218,plain,(
% 2.09/0.69    spl6_24 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK4)) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X0,X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 2.09/0.69  fof(f233,plain,(
% 2.09/0.69    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_24)),
% 2.09/0.69    inference(subsumption_resolution,[],[f232,f95])).
% 2.09/0.69  fof(f232,plain,(
% 2.09/0.69    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_24)),
% 2.09/0.69    inference(subsumption_resolution,[],[f231,f100])).
% 2.09/0.69  fof(f231,plain,(
% 2.09/0.69    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl6_6 | ~spl6_13 | ~spl6_14 | ~spl6_24)),
% 2.09/0.69    inference(subsumption_resolution,[],[f230,f105])).
% 2.09/0.69  fof(f230,plain,(
% 2.09/0.69    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl6_13 | ~spl6_14 | ~spl6_24)),
% 2.09/0.69    inference(subsumption_resolution,[],[f229,f140])).
% 2.09/0.69  fof(f229,plain,(
% 2.09/0.69    ( ! [X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl6_14 | ~spl6_24)),
% 2.09/0.69    inference(resolution,[],[f219,f145])).
% 2.09/0.69  fof(f219,plain,(
% 2.09/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK4)) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X0,X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl6_24),
% 2.09/0.69    inference(avatar_component_clause,[],[f218])).
% 2.09/0.69  fof(f220,plain,(
% 2.09/0.69    spl6_24 | ~spl6_9),
% 2.09/0.69    inference(avatar_split_clause,[],[f196,f118,f218])).
% 2.09/0.69  fof(f196,plain,(
% 2.09/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK4)) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X0,X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl6_9),
% 2.09/0.69    inference(resolution,[],[f66,f120])).
% 2.09/0.69  fof(f66,plain,(
% 2.09/0.69    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f29])).
% 2.09/0.69  fof(f214,plain,(
% 2.09/0.69    spl6_22 | spl6_23 | ~spl6_19),
% 2.09/0.69    inference(avatar_split_clause,[],[f191,f187,f212,f208])).
% 2.09/0.69  fof(f187,plain,(
% 2.09/0.69    spl6_19 <=> sP5(u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 2.09/0.69  fof(f191,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(X2) | r1_funct_2(X1,X2,u1_struct_0(sK0),u1_struct_0(sK1),X0,X0)) ) | ~spl6_19),
% 2.09/0.69    inference(resolution,[],[f189,f75])).
% 2.09/0.69  fof(f75,plain,(
% 2.09/0.69    ( ! [X4,X2,X0,X3,X1] : (~sP5(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1) | r1_funct_2(X0,X1,X2,X3,X4,X4)) )),
% 2.09/0.69    inference(general_splitting,[],[f69,f74_D])).
% 2.09/0.69  fof(f74,plain,(
% 2.09/0.69    ( ! [X2,X5,X3] : (~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | sP5(X3,X2)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f74_D])).
% 2.09/0.69  fof(f74_D,plain,(
% 2.09/0.69    ( ! [X2,X3] : (( ! [X5] : (~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) <=> ~sP5(X3,X2)) )),
% 2.09/0.69    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 2.09/0.69  fof(f69,plain,(
% 2.09/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f31])).
% 2.09/0.69  fof(f31,plain,(
% 2.09/0.69    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.09/0.69    inference(flattening,[],[f30])).
% 2.09/0.69  fof(f30,plain,(
% 2.09/0.69    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.09/0.69    inference(ennf_transformation,[],[f4])).
% 2.09/0.69  fof(f4,axiom,(
% 2.09/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 2.09/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).
% 2.09/0.69  fof(f189,plain,(
% 2.09/0.69    sP5(u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl6_19),
% 2.09/0.69    inference(avatar_component_clause,[],[f187])).
% 2.09/0.69  fof(f190,plain,(
% 2.09/0.69    spl6_19 | ~spl6_13 | ~spl6_14 | ~spl6_15),
% 2.09/0.69    inference(avatar_split_clause,[],[f155,f150,f143,f138,f187])).
% 2.09/0.69  fof(f150,plain,(
% 2.09/0.69    spl6_15 <=> ! [X1,X0] : (~v1_funct_2(sK4,X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP5(X1,X0))),
% 2.09/0.69    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.09/0.69  fof(f155,plain,(
% 2.09/0.69    sP5(u1_struct_0(sK1),u1_struct_0(sK0)) | (~spl6_13 | ~spl6_14 | ~spl6_15)),
% 2.09/0.69    inference(subsumption_resolution,[],[f154,f140])).
% 2.09/0.69  fof(f154,plain,(
% 2.09/0.69    ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | sP5(u1_struct_0(sK1),u1_struct_0(sK0)) | (~spl6_14 | ~spl6_15)),
% 2.09/0.69    inference(resolution,[],[f151,f145])).
% 2.09/0.69  fof(f151,plain,(
% 2.09/0.69    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1) | sP5(X1,X0)) ) | ~spl6_15),
% 2.09/0.69    inference(avatar_component_clause,[],[f150])).
% 2.09/0.69  fof(f185,plain,(
% 2.09/0.69    ~spl6_18 | ~spl6_12),
% 2.09/0.69    inference(avatar_split_clause,[],[f180,f133,f182])).
% 2.09/0.69  fof(f180,plain,(
% 2.09/0.69    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) | ~spl6_12),
% 2.09/0.69    inference(forward_demodulation,[],[f55,f135])).
% 2.09/0.69  fof(f55,plain,(
% 2.09/0.69    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f39,plain,(
% 2.09/0.69    ((((~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & sK0 = k1_tsep_1(sK0,sK2,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.09/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f38,f37,f36,f35,f34])).
% 2.09/0.69  fof(f34,plain,(
% 2.09/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.09/0.69    introduced(choice_axiom,[])).
% 2.09/0.69  fof(f35,plain,(
% 2.09/0.69    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,X2,X3,k2_tmap_1(sK0,sK1,X4,X2),k2_tmap_1(sK0,sK1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.09/0.69    introduced(choice_axiom,[])).
% 2.09/0.69  fof(f36,plain,(
% 2.09/0.69    ? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,X2,X3,k2_tmap_1(sK0,sK1,X4,X2),k2_tmap_1(sK0,sK1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,X3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,sK2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 2.09/0.69    introduced(choice_axiom,[])).
% 2.09/0.69  fof(f37,plain,(
% 2.09/0.69    ? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,X3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,sK2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,sK3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,sK2,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 2.09/0.69    introduced(choice_axiom,[])).
% 2.09/0.69  fof(f38,plain,(
% 2.09/0.69    ? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,sK3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) => (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 2.09/0.69    introduced(choice_axiom,[])).
% 2.09/0.69  fof(f14,plain,(
% 2.09/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.69    inference(flattening,[],[f13])).
% 2.09/0.69  fof(f13,plain,(
% 2.09/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.09/0.69    inference(ennf_transformation,[],[f12])).
% 2.09/0.69  fof(f12,negated_conjecture,(
% 2.09/0.69    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 2.09/0.69    inference(negated_conjecture,[],[f11])).
% 2.09/0.69  fof(f11,conjecture,(
% 2.09/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 2.09/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_tmap_1)).
% 2.09/0.69  fof(f179,plain,(
% 2.09/0.69    spl6_17 | spl6_1 | ~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12),
% 2.09/0.69    inference(avatar_split_clause,[],[f174,f133,f128,f123,f113,f108,f88,f78,f176])).
% 2.09/0.69  fof(f174,plain,(
% 2.09/0.69    m1_pre_topc(sK0,sK0) | (spl6_1 | ~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f173,f80])).
% 2.09/0.69  fof(f173,plain,(
% 2.09/0.69    m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f172,f90])).
% 2.09/0.69  fof(f172,plain,(
% 2.09/0.69    m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f171,f110])).
% 2.09/0.69  fof(f171,plain,(
% 2.09/0.69    m1_pre_topc(sK0,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f170,f125])).
% 2.09/0.69  fof(f170,plain,(
% 2.09/0.69    m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_8 | ~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f169,f115])).
% 2.09/0.69  fof(f169,plain,(
% 2.09/0.69    m1_pre_topc(sK0,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_11 | ~spl6_12)),
% 2.09/0.69    inference(subsumption_resolution,[],[f168,f130])).
% 2.09/0.69  fof(f168,plain,(
% 2.09/0.69    m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_12),
% 2.09/0.69    inference(superposition,[],[f63,f135])).
% 2.09/0.69  fof(f63,plain,(
% 2.09/0.69    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.69    inference(cnf_transformation,[],[f25])).
% 2.09/0.69  fof(f25,plain,(
% 2.09/0.69    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.69    inference(flattening,[],[f24])).
% 2.09/0.69  fof(f24,plain,(
% 2.09/0.69    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.69    inference(ennf_transformation,[],[f8])).
% 2.09/0.69  fof(f8,axiom,(
% 2.09/0.69    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.09/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 2.09/0.69  fof(f152,plain,(
% 2.09/0.69    spl6_15 | ~spl6_9),
% 2.09/0.69    inference(avatar_split_clause,[],[f147,f118,f150])).
% 2.09/0.69  fof(f147,plain,(
% 2.09/0.69    ( ! [X0,X1] : (~v1_funct_2(sK4,X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP5(X1,X0)) ) | ~spl6_9),
% 2.09/0.69    inference(resolution,[],[f74,f120])).
% 2.09/0.69  fof(f146,plain,(
% 2.09/0.69    spl6_14),
% 2.09/0.69    inference(avatar_split_clause,[],[f54,f143])).
% 2.09/0.69  fof(f54,plain,(
% 2.09/0.69    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f141,plain,(
% 2.09/0.69    spl6_13),
% 2.09/0.69    inference(avatar_split_clause,[],[f53,f138])).
% 2.09/0.69  fof(f53,plain,(
% 2.09/0.69    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f136,plain,(
% 2.09/0.69    spl6_12),
% 2.09/0.69    inference(avatar_split_clause,[],[f51,f133])).
% 2.09/0.69  fof(f51,plain,(
% 2.09/0.69    sK0 = k1_tsep_1(sK0,sK2,sK3)),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f131,plain,(
% 2.09/0.69    spl6_11),
% 2.09/0.69    inference(avatar_split_clause,[],[f50,f128])).
% 2.09/0.69  fof(f50,plain,(
% 2.09/0.69    m1_pre_topc(sK3,sK0)),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f126,plain,(
% 2.09/0.69    spl6_10),
% 2.09/0.69    inference(avatar_split_clause,[],[f48,f123])).
% 2.09/0.69  fof(f48,plain,(
% 2.09/0.69    m1_pre_topc(sK2,sK0)),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f121,plain,(
% 2.09/0.69    spl6_9),
% 2.09/0.69    inference(avatar_split_clause,[],[f52,f118])).
% 2.09/0.69  fof(f52,plain,(
% 2.09/0.69    v1_funct_1(sK4)),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f116,plain,(
% 2.09/0.69    ~spl6_8),
% 2.09/0.69    inference(avatar_split_clause,[],[f49,f113])).
% 2.09/0.69  fof(f49,plain,(
% 2.09/0.69    ~v2_struct_0(sK3)),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f111,plain,(
% 2.09/0.69    ~spl6_7),
% 2.09/0.69    inference(avatar_split_clause,[],[f47,f108])).
% 2.09/0.69  fof(f47,plain,(
% 2.09/0.69    ~v2_struct_0(sK2)),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f106,plain,(
% 2.09/0.69    spl6_6),
% 2.09/0.69    inference(avatar_split_clause,[],[f46,f103])).
% 2.09/0.69  fof(f46,plain,(
% 2.09/0.69    l1_pre_topc(sK1)),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f101,plain,(
% 2.09/0.69    spl6_5),
% 2.09/0.69    inference(avatar_split_clause,[],[f45,f98])).
% 2.09/0.69  fof(f45,plain,(
% 2.09/0.69    v2_pre_topc(sK1)),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f96,plain,(
% 2.09/0.69    ~spl6_4),
% 2.09/0.69    inference(avatar_split_clause,[],[f44,f93])).
% 2.09/0.69  fof(f44,plain,(
% 2.09/0.69    ~v2_struct_0(sK1)),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f91,plain,(
% 2.09/0.69    spl6_3),
% 2.09/0.69    inference(avatar_split_clause,[],[f43,f88])).
% 2.09/0.69  fof(f43,plain,(
% 2.09/0.69    l1_pre_topc(sK0)),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f86,plain,(
% 2.09/0.69    spl6_2),
% 2.09/0.69    inference(avatar_split_clause,[],[f42,f83])).
% 2.09/0.69  fof(f42,plain,(
% 2.09/0.69    v2_pre_topc(sK0)),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  fof(f81,plain,(
% 2.09/0.69    ~spl6_1),
% 2.09/0.69    inference(avatar_split_clause,[],[f41,f78])).
% 2.09/0.69  fof(f41,plain,(
% 2.09/0.69    ~v2_struct_0(sK0)),
% 2.09/0.69    inference(cnf_transformation,[],[f39])).
% 2.09/0.69  % SZS output end Proof for theBenchmark
% 2.09/0.69  % (28883)------------------------------
% 2.09/0.69  % (28883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.69  % (28883)Termination reason: Refutation
% 2.09/0.69  
% 2.09/0.69  % (28883)Memory used [KB]: 8827
% 2.09/0.69  % (28883)Time elapsed: 0.290 s
% 2.09/0.69  % (28883)------------------------------
% 2.09/0.69  % (28883)------------------------------
% 2.09/0.69  % (28880)Success in time 0.338 s
%------------------------------------------------------------------------------

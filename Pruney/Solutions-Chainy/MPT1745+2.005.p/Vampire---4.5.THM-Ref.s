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
% DateTime   : Thu Dec  3 13:18:12 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 490 expanded)
%              Number of leaves         :   44 ( 251 expanded)
%              Depth                    :   26
%              Number of atoms          : 1246 (5649 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f442,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f224,f232,f255,f265,f278,f362,f372,f391,f440])).

fof(f440,plain,
    ( spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f438,f149])).

fof(f149,plain,
    ( ~ v2_struct_0(sK3)
    | spl10_16 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl10_16
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f438,plain,
    ( v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f437,f144])).

fof(f144,plain,
    ( v2_pre_topc(sK3)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl10_15
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f437,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f436,f139])).

fof(f139,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl10_14
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f436,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f435,f134])).

fof(f134,plain,
    ( ~ v2_struct_0(sK4)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl10_13
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f435,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f434,f129])).

fof(f129,plain,
    ( v2_pre_topc(sK4)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl10_12
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f434,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f433,f124])).

fof(f124,plain,
    ( l1_pre_topc(sK4)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl10_11
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f433,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f432,f164])).

fof(f164,plain,
    ( ~ v2_struct_0(sK2)
    | spl10_19 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl10_19
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f432,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f431,f159])).

fof(f159,plain,
    ( v2_pre_topc(sK2)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl10_18
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f431,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_17
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f430,f154])).

fof(f154,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl10_17
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f430,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f429,f119])).

fof(f119,plain,
    ( v1_funct_1(sK5)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl10_10
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f429,plain,
    ( ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f428,f114])).

fof(f114,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl10_9
  <=> v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f428,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f427,f109])).

fof(f109,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl10_8
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f427,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f426,f104])).

fof(f104,plain,
    ( v1_funct_1(sK6)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl10_7
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f426,plain,
    ( ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f425,f99])).

fof(f99,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl10_6
  <=> v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f425,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f424,f94])).

fof(f94,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl10_5
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f424,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f423,f89])).

fof(f89,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl10_4
  <=> m1_subset_1(sK7,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f423,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_35
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f422,f277])).

fof(f277,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl10_35
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f422,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f421,f84])).

fof(f84,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl10_3
  <=> r1_tmap_1(sK4,sK2,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f421,plain,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f416,f390])).

fof(f390,plain,
    ( r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl10_49
  <=> r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f416,plain,
    ( ~ r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ r1_tmap_1(sK4,sK2,sK5,sK7)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1 ),
    inference(resolution,[],[f68,f74])).

fof(f74,plain,
    ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl10_1
  <=> r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
      | ~ r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5))
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
      | ~ r1_tmap_1(X2,X0,X4,X6)
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
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
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
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
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_tmap_1(X2,X0,X4,X6)
                                  & r1_tmap_1(X1,X2,X3,X5)
                                  & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6 )
                               => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tmap_1)).

fof(f391,plain,
    ( spl10_49
    | ~ spl10_35
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f385,f367,f275,f388])).

fof(f367,plain,
    ( spl10_46
  <=> sP0(sK6,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f385,plain,
    ( r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))
    | ~ spl10_35
    | ~ spl10_46 ),
    inference(unit_resulting_resolution,[],[f277,f369,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_tmap_1(X2,X1,X0,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_tmap_1(X2,X1,X0,sK8(X0,X1,X2))
          & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)) ) )
      & ( ! [X4] :
            ( r1_tmap_1(X2,X1,X0,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X2,X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,X1,X0,sK8(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_tmap_1(X2,X1,X0,X3)
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      & ( ! [X4] :
            ( r1_tmap_1(X2,X1,X0,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_tmap_1(X1,X0,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( r1_tmap_1(X1,X0,X2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( r1_tmap_1(X1,X0,X2,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f369,plain,
    ( sP0(sK6,sK3,sK2)
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f367])).

fof(f372,plain,
    ( spl10_46
    | ~ spl10_2
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f371,f336,f77,f367])).

fof(f77,plain,
    ( spl10_2
  <=> v5_pre_topc(sK6,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f336,plain,
    ( spl10_44
  <=> sP1(sK2,sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f371,plain,
    ( sP0(sK6,sK3,sK2)
    | ~ spl10_2
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f365,f79])).

fof(f79,plain,
    ( v5_pre_topc(sK6,sK2,sK3)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f365,plain,
    ( ~ v5_pre_topc(sK6,sK2,sK3)
    | sP0(sK6,sK3,sK2)
    | ~ spl10_44 ),
    inference(resolution,[],[f338,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v5_pre_topc(X2,X0,X1)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X2,X0,X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v5_pre_topc(X2,X0,X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( ( v5_pre_topc(X2,X1,X0)
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | ~ v5_pre_topc(X2,X1,X0) ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( ( v5_pre_topc(X2,X1,X0)
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f338,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f336])).

fof(f362,plain,
    ( spl10_44
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19 ),
    inference(avatar_split_clause,[],[f361,f162,f157,f152,f147,f142,f137,f102,f97,f92,f336])).

fof(f361,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19 ),
    inference(subsumption_resolution,[],[f360,f149])).

fof(f360,plain,
    ( sP1(sK2,sK3,sK6)
    | v2_struct_0(sK3)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19 ),
    inference(subsumption_resolution,[],[f359,f144])).

fof(f359,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19 ),
    inference(subsumption_resolution,[],[f358,f139])).

fof(f358,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19 ),
    inference(subsumption_resolution,[],[f357,f164])).

fof(f357,plain,
    ( sP1(sK2,sK3,sK6)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_17
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f356,f159])).

fof(f356,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f355,f154])).

fof(f355,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f354,f104])).

fof(f354,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f334,f99])).

fof(f334,plain,
    ( sP1(sK2,sK3,sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_5 ),
    inference(resolution,[],[f64,f94])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | sP1(X1,X0,X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f23,f22])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
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
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f278,plain,
    ( spl10_35
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | spl10_33 ),
    inference(avatar_split_clause,[],[f267,f260,f117,f112,f107,f87,f275])).

fof(f260,plain,
    ( spl10_33
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f267,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | spl10_33 ),
    inference(unit_resulting_resolution,[],[f119,f89,f114,f109,f262,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f262,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl10_33 ),
    inference(avatar_component_clause,[],[f260])).

fof(f265,plain,
    ( ~ spl10_33
    | spl10_29
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f264,f252,f228,f260])).

fof(f228,plain,
    ( spl10_29
  <=> sP9(k1_connsp_2(sK4,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f252,plain,
    ( spl10_32
  <=> m1_subset_1(k1_connsp_2(sK4,sK7),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f264,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl10_29
    | ~ spl10_32 ),
    inference(subsumption_resolution,[],[f258,f230])).

fof(f230,plain,
    ( ~ sP9(k1_connsp_2(sK4,sK7))
    | spl10_29 ),
    inference(avatar_component_clause,[],[f228])).

fof(f258,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | sP9(k1_connsp_2(sK4,sK7))
    | ~ spl10_32 ),
    inference(resolution,[],[f254,f69])).

fof(f69,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f69_D])).

fof(f69_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f254,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f252])).

fof(f255,plain,
    ( spl10_32
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13 ),
    inference(avatar_split_clause,[],[f243,f132,f127,f122,f87,f252])).

fof(f243,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13 ),
    inference(unit_resulting_resolution,[],[f134,f129,f124,f89,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f232,plain,
    ( ~ spl10_29
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f226,f221,f228])).

fof(f221,plain,
    ( spl10_28
  <=> r2_hidden(sK7,k1_connsp_2(sK4,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f226,plain,
    ( ~ sP9(k1_connsp_2(sK4,sK7))
    | ~ spl10_28 ),
    inference(resolution,[],[f223,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP9(X1) ) ),
    inference(general_splitting,[],[f66,f69_D])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f223,plain,
    ( r2_hidden(sK7,k1_connsp_2(sK4,sK7))
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f221])).

fof(f224,plain,
    ( spl10_28
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13 ),
    inference(avatar_split_clause,[],[f212,f132,f127,f122,f87,f221])).

fof(f212,plain,
    ( r2_hidden(sK7,k1_connsp_2(sK4,sK7))
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_12
    | spl10_13 ),
    inference(unit_resulting_resolution,[],[f134,f129,f124,f89,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

fof(f165,plain,(
    ~ spl10_19 ),
    inference(avatar_split_clause,[],[f38,f162])).

fof(f38,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)
    & v5_pre_topc(sK6,sK2,sK3)
    & r1_tmap_1(sK4,sK2,sK5,sK7)
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f30,f29,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                            & v5_pre_topc(X4,X0,X1)
                            & r1_tmap_1(X2,X0,X3,X5)
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & l1_pre_topc(X2)
                & v2_pre_topc(X2)
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
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,sK2,X1)
                          & r1_tmap_1(X2,sK2,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(X1),X3,X4),X5)
                        & v5_pre_topc(X4,sK2,X1)
                        & r1_tmap_1(X2,sK2,X3,X5)
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2))
                & v1_funct_1(X3) )
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5)
                      & v5_pre_topc(X4,sK2,sK3)
                      & r1_tmap_1(X2,sK2,X3,X5)
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
              & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2))
              & v1_funct_1(X3) )
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5)
                    & v5_pre_topc(X4,sK2,sK3)
                    & r1_tmap_1(X2,sK2,X3,X5)
                    & m1_subset_1(X5,u1_struct_0(X2)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
            & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2))
            & v1_funct_1(X3) )
        & l1_pre_topc(X2)
        & v2_pre_topc(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5)
                  & v5_pre_topc(X4,sK2,sK3)
                  & r1_tmap_1(sK4,sK2,X3,X5)
                  & m1_subset_1(X5,u1_struct_0(sK4)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
          & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK2))
          & v1_funct_1(X3) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5)
                & v5_pre_topc(X4,sK2,sK3)
                & r1_tmap_1(sK4,sK2,X3,X5)
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK2))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,X4),X5)
              & v5_pre_topc(X4,sK2,sK3)
              & r1_tmap_1(sK4,sK2,sK5,X5)
              & m1_subset_1(X5,u1_struct_0(sK4)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
      & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,X4),X5)
            & v5_pre_topc(X4,sK2,sK3)
            & r1_tmap_1(sK4,sK2,sK5,X5)
            & m1_subset_1(X5,u1_struct_0(sK4)) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),X5)
          & v5_pre_topc(sK6,sK2,sK3)
          & r1_tmap_1(sK4,sK2,sK5,X5)
          & m1_subset_1(X5,u1_struct_0(sK4)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X5] :
        ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),X5)
        & v5_pre_topc(sK6,sK2,sK3)
        & r1_tmap_1(sK4,sK2,sK5,X5)
        & m1_subset_1(X5,u1_struct_0(sK4)) )
   => ( ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)
      & v5_pre_topc(sK6,sK2,sK3)
      & r1_tmap_1(sK4,sK2,sK5,sK7)
      & m1_subset_1(sK7,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,X0,X1)
                          & r1_tmap_1(X2,X0,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5)
                          & v5_pre_topc(X4,X0,X1)
                          & r1_tmap_1(X2,X0,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (838)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ( ( v5_pre_topc(X4,X0,X1)
                                & r1_tmap_1(X2,X0,X3,X5) )
                             => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( v5_pre_topc(X4,X0,X1)
                              & r1_tmap_1(X2,X0,X3,X5) )
                           => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tmap_1)).

fof(f160,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f39,f157])).

fof(f39,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f155,plain,(
    spl10_17 ),
    inference(avatar_split_clause,[],[f40,f152])).

fof(f40,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f150,plain,(
    ~ spl10_16 ),
    inference(avatar_split_clause,[],[f41,f147])).

fof(f41,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f145,plain,(
    spl10_15 ),
    inference(avatar_split_clause,[],[f42,f142])).

fof(f42,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f140,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f43,f137])).

fof(f43,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f135,plain,(
    ~ spl10_13 ),
    inference(avatar_split_clause,[],[f44,f132])).

fof(f44,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f130,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f45,f127])).

fof(f45,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f125,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f46,f122])).

fof(f46,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f120,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f47,f117])).

fof(f47,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f115,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f48,f112])).

fof(f48,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f110,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f49,f107])).

fof(f49,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f105,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f50,f102])).

fof(f50,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f100,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f51,f97])).

fof(f51,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f52,f92])).

fof(f52,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f53,f87])).

fof(f53,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f54,f82])).

fof(f54,plain,(
    r1_tmap_1(sK4,sK2,sK5,sK7) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f55,f77])).

fof(f55,plain,(
    v5_pre_topc(sK6,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f56,f72])).

fof(f56,plain,(
    ~ r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:33:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  ipcrm: permission denied for id (807108610)
% 0.12/0.36  ipcrm: permission denied for id (807141379)
% 0.12/0.36  ipcrm: permission denied for id (806715396)
% 0.12/0.37  ipcrm: permission denied for id (807206918)
% 0.12/0.37  ipcrm: permission denied for id (807239687)
% 0.12/0.37  ipcrm: permission denied for id (807305225)
% 0.12/0.37  ipcrm: permission denied for id (807337994)
% 0.12/0.37  ipcrm: permission denied for id (807370763)
% 0.12/0.37  ipcrm: permission denied for id (807403532)
% 0.12/0.38  ipcrm: permission denied for id (807534607)
% 0.12/0.38  ipcrm: permission denied for id (807567376)
% 0.12/0.38  ipcrm: permission denied for id (806813713)
% 0.12/0.38  ipcrm: permission denied for id (807600146)
% 0.12/0.38  ipcrm: permission denied for id (807632915)
% 0.12/0.38  ipcrm: permission denied for id (807698453)
% 0.12/0.39  ipcrm: permission denied for id (807763991)
% 0.12/0.39  ipcrm: permission denied for id (807796760)
% 0.12/0.40  ipcrm: permission denied for id (808026143)
% 0.12/0.40  ipcrm: permission denied for id (808091681)
% 0.12/0.40  ipcrm: permission denied for id (808124450)
% 0.12/0.40  ipcrm: permission denied for id (808157219)
% 0.12/0.40  ipcrm: permission denied for id (808189988)
% 0.12/0.41  ipcrm: permission denied for id (808288295)
% 0.20/0.41  ipcrm: permission denied for id (808353833)
% 0.20/0.41  ipcrm: permission denied for id (808386602)
% 0.20/0.42  ipcrm: permission denied for id (808419371)
% 0.20/0.42  ipcrm: permission denied for id (808484909)
% 0.20/0.42  ipcrm: permission denied for id (808550447)
% 0.20/0.43  ipcrm: permission denied for id (808615985)
% 0.20/0.43  ipcrm: permission denied for id (808648754)
% 0.20/0.43  ipcrm: permission denied for id (808714292)
% 0.20/0.43  ipcrm: permission denied for id (808779830)
% 0.20/0.44  ipcrm: permission denied for id (808812599)
% 0.20/0.44  ipcrm: permission denied for id (808845368)
% 0.20/0.44  ipcrm: permission denied for id (808878137)
% 0.20/0.44  ipcrm: permission denied for id (808910906)
% 0.20/0.44  ipcrm: permission denied for id (809009212)
% 0.20/0.45  ipcrm: permission denied for id (809041981)
% 0.20/0.45  ipcrm: permission denied for id (809074750)
% 0.20/0.45  ipcrm: permission denied for id (809107519)
% 0.20/0.45  ipcrm: permission denied for id (809140288)
% 0.20/0.45  ipcrm: permission denied for id (809173057)
% 0.20/0.45  ipcrm: permission denied for id (809205826)
% 0.20/0.46  ipcrm: permission denied for id (809238595)
% 0.20/0.46  ipcrm: permission denied for id (809271364)
% 0.20/0.46  ipcrm: permission denied for id (809435209)
% 0.20/0.47  ipcrm: permission denied for id (809467978)
% 0.20/0.47  ipcrm: permission denied for id (806912075)
% 0.20/0.47  ipcrm: permission denied for id (809566285)
% 0.20/0.47  ipcrm: permission denied for id (809631823)
% 0.20/0.48  ipcrm: permission denied for id (806944848)
% 0.20/0.48  ipcrm: permission denied for id (809697362)
% 0.20/0.48  ipcrm: permission denied for id (809762899)
% 0.20/0.48  ipcrm: permission denied for id (809795668)
% 0.20/0.48  ipcrm: permission denied for id (809828437)
% 0.20/0.48  ipcrm: permission denied for id (809861206)
% 0.20/0.48  ipcrm: permission denied for id (809893975)
% 0.20/0.48  ipcrm: permission denied for id (809926744)
% 0.20/0.49  ipcrm: permission denied for id (809992282)
% 0.20/0.49  ipcrm: permission denied for id (810025051)
% 0.20/0.49  ipcrm: permission denied for id (810057820)
% 0.20/0.49  ipcrm: permission denied for id (810090589)
% 0.20/0.49  ipcrm: permission denied for id (810156127)
% 0.20/0.49  ipcrm: permission denied for id (810221665)
% 0.20/0.50  ipcrm: permission denied for id (806977640)
% 0.20/0.50  ipcrm: permission denied for id (810516587)
% 0.20/0.50  ipcrm: permission denied for id (810549356)
% 0.20/0.50  ipcrm: permission denied for id (810582125)
% 0.20/0.51  ipcrm: permission denied for id (810647663)
% 0.20/0.51  ipcrm: permission denied for id (810745970)
% 0.20/0.51  ipcrm: permission denied for id (810778739)
% 0.20/0.51  ipcrm: permission denied for id (810811508)
% 0.20/0.51  ipcrm: permission denied for id (810844277)
% 0.20/0.51  ipcrm: permission denied for id (807010422)
% 0.20/0.51  ipcrm: permission denied for id (810909816)
% 0.20/0.51  ipcrm: permission denied for id (810942585)
% 0.20/0.51  ipcrm: permission denied for id (810975354)
% 0.20/0.52  ipcrm: permission denied for id (811106430)
% 0.20/0.52  ipcrm: permission denied for id (811171967)
% 0.63/0.62  % (827)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.63/0.62  % (835)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.99/0.62  % (834)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.99/0.62  % (821)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.99/0.62  % (835)Refutation found. Thanks to Tanya!
% 0.99/0.62  % SZS status Theorem for theBenchmark
% 0.99/0.63  % (837)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.99/0.63  % (826)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.99/0.63  % (828)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.99/0.63  % (830)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.99/0.63  % (836)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.99/0.63  % SZS output start Proof for theBenchmark
% 0.99/0.63  fof(f442,plain,(
% 0.99/0.63    $false),
% 0.99/0.63    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f224,f232,f255,f265,f278,f362,f372,f391,f440])).
% 0.99/0.63  fof(f440,plain,(
% 0.99/0.63    spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_35 | ~spl10_49),
% 0.99/0.63    inference(avatar_contradiction_clause,[],[f439])).
% 0.99/0.63  fof(f439,plain,(
% 0.99/0.63    $false | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f438,f149])).
% 0.99/0.63  fof(f149,plain,(
% 0.99/0.63    ~v2_struct_0(sK3) | spl10_16),
% 0.99/0.63    inference(avatar_component_clause,[],[f147])).
% 0.99/0.63  fof(f147,plain,(
% 0.99/0.63    spl10_16 <=> v2_struct_0(sK3)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.99/0.63  fof(f438,plain,(
% 0.99/0.63    v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f437,f144])).
% 0.99/0.63  fof(f144,plain,(
% 0.99/0.63    v2_pre_topc(sK3) | ~spl10_15),
% 0.99/0.63    inference(avatar_component_clause,[],[f142])).
% 0.99/0.63  fof(f142,plain,(
% 0.99/0.63    spl10_15 <=> v2_pre_topc(sK3)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.99/0.63  fof(f437,plain,(
% 0.99/0.63    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f436,f139])).
% 0.99/0.63  fof(f139,plain,(
% 0.99/0.63    l1_pre_topc(sK3) | ~spl10_14),
% 0.99/0.63    inference(avatar_component_clause,[],[f137])).
% 0.99/0.63  fof(f137,plain,(
% 0.99/0.63    spl10_14 <=> l1_pre_topc(sK3)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.99/0.63  fof(f436,plain,(
% 0.99/0.63    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | spl10_13 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f435,f134])).
% 0.99/0.63  fof(f134,plain,(
% 0.99/0.63    ~v2_struct_0(sK4) | spl10_13),
% 0.99/0.63    inference(avatar_component_clause,[],[f132])).
% 0.99/0.63  fof(f132,plain,(
% 0.99/0.63    spl10_13 <=> v2_struct_0(sK4)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.99/0.63  fof(f435,plain,(
% 0.99/0.63    v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f434,f129])).
% 0.99/0.63  fof(f129,plain,(
% 0.99/0.63    v2_pre_topc(sK4) | ~spl10_12),
% 0.99/0.63    inference(avatar_component_clause,[],[f127])).
% 0.99/0.63  fof(f127,plain,(
% 0.99/0.63    spl10_12 <=> v2_pre_topc(sK4)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.99/0.63  fof(f434,plain,(
% 0.99/0.63    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f433,f124])).
% 0.99/0.63  fof(f124,plain,(
% 0.99/0.63    l1_pre_topc(sK4) | ~spl10_11),
% 0.99/0.63    inference(avatar_component_clause,[],[f122])).
% 0.99/0.63  fof(f122,plain,(
% 0.99/0.63    spl10_11 <=> l1_pre_topc(sK4)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.99/0.63  fof(f433,plain,(
% 0.99/0.63    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f432,f164])).
% 0.99/0.63  fof(f164,plain,(
% 0.99/0.63    ~v2_struct_0(sK2) | spl10_19),
% 0.99/0.63    inference(avatar_component_clause,[],[f162])).
% 0.99/0.63  fof(f162,plain,(
% 0.99/0.63    spl10_19 <=> v2_struct_0(sK2)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.99/0.63  fof(f432,plain,(
% 0.99/0.63    v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_17 | ~spl10_18 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f431,f159])).
% 0.99/0.63  fof(f159,plain,(
% 0.99/0.63    v2_pre_topc(sK2) | ~spl10_18),
% 0.99/0.63    inference(avatar_component_clause,[],[f157])).
% 0.99/0.63  fof(f157,plain,(
% 0.99/0.63    spl10_18 <=> v2_pre_topc(sK2)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.99/0.63  fof(f431,plain,(
% 0.99/0.63    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_17 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f430,f154])).
% 0.99/0.63  fof(f154,plain,(
% 0.99/0.63    l1_pre_topc(sK2) | ~spl10_17),
% 0.99/0.63    inference(avatar_component_clause,[],[f152])).
% 0.99/0.63  fof(f152,plain,(
% 0.99/0.63    spl10_17 <=> l1_pre_topc(sK2)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.99/0.63  fof(f430,plain,(
% 0.99/0.63    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f429,f119])).
% 0.99/0.63  fof(f119,plain,(
% 0.99/0.63    v1_funct_1(sK5) | ~spl10_10),
% 0.99/0.63    inference(avatar_component_clause,[],[f117])).
% 0.99/0.63  fof(f117,plain,(
% 0.99/0.63    spl10_10 <=> v1_funct_1(sK5)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.99/0.63  fof(f429,plain,(
% 0.99/0.63    ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f428,f114])).
% 0.99/0.63  fof(f114,plain,(
% 0.99/0.63    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~spl10_9),
% 0.99/0.63    inference(avatar_component_clause,[],[f112])).
% 0.99/0.63  fof(f112,plain,(
% 0.99/0.63    spl10_9 <=> v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.99/0.63  fof(f428,plain,(
% 0.99/0.63    ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f427,f109])).
% 0.99/0.63  fof(f109,plain,(
% 0.99/0.63    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~spl10_8),
% 0.99/0.63    inference(avatar_component_clause,[],[f107])).
% 0.99/0.63  fof(f107,plain,(
% 0.99/0.63    spl10_8 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.99/0.63  fof(f427,plain,(
% 0.99/0.63    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f426,f104])).
% 0.99/0.63  fof(f104,plain,(
% 0.99/0.63    v1_funct_1(sK6) | ~spl10_7),
% 0.99/0.63    inference(avatar_component_clause,[],[f102])).
% 0.99/0.63  fof(f102,plain,(
% 0.99/0.63    spl10_7 <=> v1_funct_1(sK6)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.99/0.63  fof(f426,plain,(
% 0.99/0.63    ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f425,f99])).
% 0.99/0.63  fof(f99,plain,(
% 0.99/0.63    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl10_6),
% 0.99/0.63    inference(avatar_component_clause,[],[f97])).
% 0.99/0.63  fof(f97,plain,(
% 0.99/0.63    spl10_6 <=> v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.99/0.63  fof(f425,plain,(
% 0.99/0.63    ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f424,f94])).
% 0.99/0.63  fof(f94,plain,(
% 0.99/0.63    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~spl10_5),
% 0.99/0.63    inference(avatar_component_clause,[],[f92])).
% 0.99/0.63  fof(f92,plain,(
% 0.99/0.63    spl10_5 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.99/0.63  fof(f424,plain,(
% 0.99/0.63    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f423,f89])).
% 0.99/0.63  fof(f89,plain,(
% 0.99/0.63    m1_subset_1(sK7,u1_struct_0(sK4)) | ~spl10_4),
% 0.99/0.63    inference(avatar_component_clause,[],[f87])).
% 0.99/0.63  fof(f87,plain,(
% 0.99/0.63    spl10_4 <=> m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.99/0.63  fof(f423,plain,(
% 0.99/0.63    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_35 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f422,f277])).
% 0.99/0.63  fof(f277,plain,(
% 0.99/0.63    m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) | ~spl10_35),
% 0.99/0.63    inference(avatar_component_clause,[],[f275])).
% 0.99/0.63  fof(f275,plain,(
% 0.99/0.63    spl10_35 <=> m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2))),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).
% 0.99/0.63  fof(f422,plain,(
% 0.99/0.63    ~m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_3 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f421,f84])).
% 0.99/0.63  fof(f84,plain,(
% 0.99/0.63    r1_tmap_1(sK4,sK2,sK5,sK7) | ~spl10_3),
% 0.99/0.63    inference(avatar_component_clause,[],[f82])).
% 0.99/0.63  fof(f82,plain,(
% 0.99/0.63    spl10_3 <=> r1_tmap_1(sK4,sK2,sK5,sK7)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.99/0.63  fof(f421,plain,(
% 0.99/0.63    ~r1_tmap_1(sK4,sK2,sK5,sK7) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_49)),
% 0.99/0.63    inference(subsumption_resolution,[],[f416,f390])).
% 0.99/0.63  fof(f390,plain,(
% 0.99/0.63    r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~spl10_49),
% 0.99/0.63    inference(avatar_component_clause,[],[f388])).
% 0.99/0.63  fof(f388,plain,(
% 0.99/0.63    spl10_49 <=> r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7))),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).
% 0.99/0.63  fof(f416,plain,(
% 0.99/0.63    ~r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | ~r1_tmap_1(sK4,sK2,sK5,sK7) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl10_1),
% 0.99/0.63    inference(resolution,[],[f68,f74])).
% 0.99/0.63  fof(f74,plain,(
% 0.99/0.63    ~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) | spl10_1),
% 0.99/0.63    inference(avatar_component_clause,[],[f72])).
% 0.99/0.63  fof(f72,plain,(
% 0.99/0.63    spl10_1 <=> r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.99/0.63  fof(f68,plain,(
% 0.99/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | ~r1_tmap_1(X1,X2,X3,X5) | ~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/0.63    inference(equality_resolution,[],[f58])).
% 0.99/0.63  fof(f58,plain,(
% 0.99/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/0.63    inference(cnf_transformation,[],[f14])).
% 0.99/0.63  fof(f14,plain,(
% 0.99/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/0.63    inference(flattening,[],[f13])).
% 0.99/0.63  fof(f13,plain,(
% 0.99/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | (~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.99/0.63    inference(ennf_transformation,[],[f6])).
% 0.99/0.63  fof(f6,axiom,(
% 0.99/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X0,X4,X6) & r1_tmap_1(X1,X2,X3,X5) & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6) => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)))))))))),
% 0.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tmap_1)).
% 0.99/0.63  fof(f391,plain,(
% 0.99/0.63    spl10_49 | ~spl10_35 | ~spl10_46),
% 0.99/0.63    inference(avatar_split_clause,[],[f385,f367,f275,f388])).
% 0.99/0.63  fof(f367,plain,(
% 0.99/0.63    spl10_46 <=> sP0(sK6,sK3,sK2)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).
% 0.99/0.63  fof(f385,plain,(
% 0.99/0.63    r1_tmap_1(sK2,sK3,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)) | (~spl10_35 | ~spl10_46)),
% 0.99/0.63    inference(unit_resulting_resolution,[],[f277,f369,f61])).
% 0.99/0.63  fof(f61,plain,(
% 0.99/0.63    ( ! [X4,X2,X0,X1] : (r1_tmap_1(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 0.99/0.63    inference(cnf_transformation,[],[f37])).
% 0.99/0.63  fof(f37,plain,(
% 0.99/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r1_tmap_1(X2,X1,X0,sK8(X0,X1,X2)) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)))) & (! [X4] : (r1_tmap_1(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 0.99/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f35,f36])).
% 0.99/0.63  fof(f36,plain,(
% 0.99/0.63    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X2))) => (~r1_tmap_1(X2,X1,X0,sK8(X0,X1,X2)) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2))))),
% 0.99/0.63    introduced(choice_axiom,[])).
% 0.99/0.63  fof(f35,plain,(
% 0.99/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r1_tmap_1(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X2)))) & (! [X4] : (r1_tmap_1(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 0.99/0.63    inference(rectify,[],[f34])).
% 0.99/0.63  fof(f34,plain,(
% 0.99/0.63    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X2,X0,X1)))),
% 0.99/0.63    inference(nnf_transformation,[],[f22])).
% 0.99/0.63  fof(f22,plain,(
% 0.99/0.63    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))))),
% 0.99/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.99/0.63  fof(f369,plain,(
% 0.99/0.63    sP0(sK6,sK3,sK2) | ~spl10_46),
% 0.99/0.63    inference(avatar_component_clause,[],[f367])).
% 0.99/0.63  fof(f372,plain,(
% 0.99/0.63    spl10_46 | ~spl10_2 | ~spl10_44),
% 0.99/0.63    inference(avatar_split_clause,[],[f371,f336,f77,f367])).
% 0.99/0.63  fof(f77,plain,(
% 0.99/0.63    spl10_2 <=> v5_pre_topc(sK6,sK2,sK3)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.99/0.63  fof(f336,plain,(
% 0.99/0.63    spl10_44 <=> sP1(sK2,sK3,sK6)),
% 0.99/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 0.99/0.63  fof(f371,plain,(
% 0.99/0.63    sP0(sK6,sK3,sK2) | (~spl10_2 | ~spl10_44)),
% 0.99/0.63    inference(subsumption_resolution,[],[f365,f79])).
% 0.99/0.63  fof(f79,plain,(
% 0.99/0.63    v5_pre_topc(sK6,sK2,sK3) | ~spl10_2),
% 0.99/0.63    inference(avatar_component_clause,[],[f77])).
% 0.99/0.63  fof(f365,plain,(
% 0.99/0.63    ~v5_pre_topc(sK6,sK2,sK3) | sP0(sK6,sK3,sK2) | ~spl10_44),
% 0.99/0.63    inference(resolution,[],[f338,f59])).
% 0.99/0.63  fof(f59,plain,(
% 0.99/0.63    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v5_pre_topc(X2,X0,X1) | sP0(X2,X1,X0)) )),
% 0.99/0.63    inference(cnf_transformation,[],[f33])).
% 0.99/0.63  fof(f33,plain,(
% 0.99/0.63    ! [X0,X1,X2] : (((v5_pre_topc(X2,X0,X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v5_pre_topc(X2,X0,X1))) | ~sP1(X0,X1,X2))),
% 0.99/0.63    inference(rectify,[],[f32])).
% 0.99/0.63  fof(f32,plain,(
% 0.99/0.63    ! [X1,X0,X2] : (((v5_pre_topc(X2,X1,X0) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~v5_pre_topc(X2,X1,X0))) | ~sP1(X1,X0,X2))),
% 0.99/0.63    inference(nnf_transformation,[],[f23])).
% 0.99/0.63  fof(f23,plain,(
% 0.99/0.63    ! [X1,X0,X2] : ((v5_pre_topc(X2,X1,X0) <=> sP0(X2,X0,X1)) | ~sP1(X1,X0,X2))),
% 0.99/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.99/0.64  fof(f338,plain,(
% 0.99/0.64    sP1(sK2,sK3,sK6) | ~spl10_44),
% 0.99/0.64    inference(avatar_component_clause,[],[f336])).
% 0.99/0.64  fof(f362,plain,(
% 0.99/0.64    spl10_44 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19),
% 0.99/0.64    inference(avatar_split_clause,[],[f361,f162,f157,f152,f147,f142,f137,f102,f97,f92,f336])).
% 0.99/0.64  fof(f361,plain,(
% 0.99/0.64    sP1(sK2,sK3,sK6) | (~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19)),
% 0.99/0.64    inference(subsumption_resolution,[],[f360,f149])).
% 0.99/0.64  fof(f360,plain,(
% 0.99/0.64    sP1(sK2,sK3,sK6) | v2_struct_0(sK3) | (~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_14 | ~spl10_15 | ~spl10_17 | ~spl10_18 | spl10_19)),
% 0.99/0.64    inference(subsumption_resolution,[],[f359,f144])).
% 0.99/0.64  fof(f359,plain,(
% 0.99/0.64    sP1(sK2,sK3,sK6) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_14 | ~spl10_17 | ~spl10_18 | spl10_19)),
% 0.99/0.64    inference(subsumption_resolution,[],[f358,f139])).
% 0.99/0.64  fof(f358,plain,(
% 0.99/0.64    sP1(sK2,sK3,sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_17 | ~spl10_18 | spl10_19)),
% 0.99/0.64    inference(subsumption_resolution,[],[f357,f164])).
% 0.99/0.64  fof(f357,plain,(
% 0.99/0.64    sP1(sK2,sK3,sK6) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_17 | ~spl10_18)),
% 0.99/0.64    inference(subsumption_resolution,[],[f356,f159])).
% 0.99/0.64  fof(f356,plain,(
% 0.99/0.64    sP1(sK2,sK3,sK6) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_17)),
% 0.99/0.64    inference(subsumption_resolution,[],[f355,f154])).
% 0.99/0.64  fof(f355,plain,(
% 0.99/0.64    sP1(sK2,sK3,sK6) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl10_5 | ~spl10_6 | ~spl10_7)),
% 0.99/0.64    inference(subsumption_resolution,[],[f354,f104])).
% 0.99/0.64  fof(f354,plain,(
% 0.99/0.64    sP1(sK2,sK3,sK6) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl10_5 | ~spl10_6)),
% 0.99/0.64    inference(subsumption_resolution,[],[f334,f99])).
% 0.99/0.64  fof(f334,plain,(
% 0.99/0.64    sP1(sK2,sK3,sK6) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl10_5),
% 0.99/0.64    inference(resolution,[],[f64,f94])).
% 0.99/0.64  fof(f64,plain,(
% 0.99/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | sP1(X1,X0,X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/0.64    inference(cnf_transformation,[],[f24])).
% 0.99/0.64  fof(f24,plain,(
% 0.99/0.64    ! [X0] : (! [X1] : (! [X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/0.64    inference(definition_folding,[],[f16,f23,f22])).
% 0.99/0.64  fof(f16,plain,(
% 0.99/0.64    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/0.64    inference(flattening,[],[f15])).
% 0.99/0.64  fof(f15,plain,(
% 0.99/0.64    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.99/0.64    inference(ennf_transformation,[],[f5])).
% 0.99/0.64  fof(f5,axiom,(
% 0.99/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.99/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).
% 0.99/0.64  fof(f278,plain,(
% 0.99/0.64    spl10_35 | ~spl10_4 | ~spl10_8 | ~spl10_9 | ~spl10_10 | spl10_33),
% 0.99/0.64    inference(avatar_split_clause,[],[f267,f260,f117,f112,f107,f87,f275])).
% 0.99/0.64  fof(f260,plain,(
% 0.99/0.64    spl10_33 <=> v1_xboole_0(u1_struct_0(sK4))),
% 0.99/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 0.99/0.64  fof(f267,plain,(
% 0.99/0.64    m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7),u1_struct_0(sK2)) | (~spl10_4 | ~spl10_8 | ~spl10_9 | ~spl10_10 | spl10_33)),
% 0.99/0.64    inference(unit_resulting_resolution,[],[f119,f89,f114,f109,f262,f67])).
% 0.99/0.64  fof(f67,plain,(
% 0.99/0.64    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.99/0.64    inference(cnf_transformation,[],[f21])).
% 0.99/0.64  fof(f21,plain,(
% 0.99/0.64    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.99/0.64    inference(flattening,[],[f20])).
% 0.99/0.64  fof(f20,plain,(
% 0.99/0.64    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.99/0.64    inference(ennf_transformation,[],[f2])).
% 0.99/0.64  fof(f2,axiom,(
% 0.99/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.99/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.99/0.64  fof(f262,plain,(
% 0.99/0.64    ~v1_xboole_0(u1_struct_0(sK4)) | spl10_33),
% 0.99/0.64    inference(avatar_component_clause,[],[f260])).
% 0.99/0.64  fof(f265,plain,(
% 0.99/0.64    ~spl10_33 | spl10_29 | ~spl10_32),
% 0.99/0.64    inference(avatar_split_clause,[],[f264,f252,f228,f260])).
% 0.99/0.64  fof(f228,plain,(
% 0.99/0.64    spl10_29 <=> sP9(k1_connsp_2(sK4,sK7))),
% 0.99/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 0.99/0.64  fof(f252,plain,(
% 0.99/0.64    spl10_32 <=> m1_subset_1(k1_connsp_2(sK4,sK7),k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.99/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).
% 0.99/0.64  fof(f264,plain,(
% 0.99/0.64    ~v1_xboole_0(u1_struct_0(sK4)) | (spl10_29 | ~spl10_32)),
% 0.99/0.64    inference(subsumption_resolution,[],[f258,f230])).
% 0.99/0.64  fof(f230,plain,(
% 0.99/0.64    ~sP9(k1_connsp_2(sK4,sK7)) | spl10_29),
% 0.99/0.64    inference(avatar_component_clause,[],[f228])).
% 0.99/0.64  fof(f258,plain,(
% 0.99/0.64    ~v1_xboole_0(u1_struct_0(sK4)) | sP9(k1_connsp_2(sK4,sK7)) | ~spl10_32),
% 0.99/0.64    inference(resolution,[],[f254,f69])).
% 0.99/0.64  fof(f69,plain,(
% 0.99/0.64    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP9(X1)) )),
% 0.99/0.64    inference(cnf_transformation,[],[f69_D])).
% 0.99/0.64  fof(f69_D,plain,(
% 0.99/0.64    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP9(X1)) )),
% 0.99/0.64    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.99/0.64  fof(f254,plain,(
% 0.99/0.64    m1_subset_1(k1_connsp_2(sK4,sK7),k1_zfmisc_1(u1_struct_0(sK4))) | ~spl10_32),
% 0.99/0.64    inference(avatar_component_clause,[],[f252])).
% 0.99/0.64  fof(f255,plain,(
% 0.99/0.64    spl10_32 | ~spl10_4 | ~spl10_11 | ~spl10_12 | spl10_13),
% 0.99/0.64    inference(avatar_split_clause,[],[f243,f132,f127,f122,f87,f252])).
% 0.99/0.64  fof(f243,plain,(
% 0.99/0.64    m1_subset_1(k1_connsp_2(sK4,sK7),k1_zfmisc_1(u1_struct_0(sK4))) | (~spl10_4 | ~spl10_11 | ~spl10_12 | spl10_13)),
% 0.99/0.64    inference(unit_resulting_resolution,[],[f134,f129,f124,f89,f65])).
% 0.99/0.64  fof(f65,plain,(
% 0.99/0.64    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/0.64    inference(cnf_transformation,[],[f18])).
% 0.99/0.64  fof(f18,plain,(
% 0.99/0.64    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/0.64    inference(flattening,[],[f17])).
% 0.99/0.64  fof(f17,plain,(
% 0.99/0.64    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.99/0.64    inference(ennf_transformation,[],[f3])).
% 0.99/0.64  fof(f3,axiom,(
% 0.99/0.64    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.99/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 0.99/0.64  fof(f232,plain,(
% 0.99/0.64    ~spl10_29 | ~spl10_28),
% 0.99/0.64    inference(avatar_split_clause,[],[f226,f221,f228])).
% 0.99/0.64  fof(f221,plain,(
% 0.99/0.64    spl10_28 <=> r2_hidden(sK7,k1_connsp_2(sK4,sK7))),
% 0.99/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 0.99/0.64  fof(f226,plain,(
% 0.99/0.64    ~sP9(k1_connsp_2(sK4,sK7)) | ~spl10_28),
% 0.99/0.64    inference(resolution,[],[f223,f70])).
% 0.99/0.64  fof(f70,plain,(
% 0.99/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP9(X1)) )),
% 0.99/0.64    inference(general_splitting,[],[f66,f69_D])).
% 0.99/0.64  fof(f66,plain,(
% 0.99/0.64    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.99/0.64    inference(cnf_transformation,[],[f19])).
% 0.99/0.64  fof(f19,plain,(
% 0.99/0.64    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.99/0.64    inference(ennf_transformation,[],[f1])).
% 0.99/0.64  fof(f1,axiom,(
% 0.99/0.64    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.99/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.99/0.64  fof(f223,plain,(
% 0.99/0.64    r2_hidden(sK7,k1_connsp_2(sK4,sK7)) | ~spl10_28),
% 0.99/0.64    inference(avatar_component_clause,[],[f221])).
% 0.99/0.64  fof(f224,plain,(
% 0.99/0.64    spl10_28 | ~spl10_4 | ~spl10_11 | ~spl10_12 | spl10_13),
% 0.99/0.64    inference(avatar_split_clause,[],[f212,f132,f127,f122,f87,f221])).
% 0.99/0.64  fof(f212,plain,(
% 0.99/0.64    r2_hidden(sK7,k1_connsp_2(sK4,sK7)) | (~spl10_4 | ~spl10_11 | ~spl10_12 | spl10_13)),
% 0.99/0.64    inference(unit_resulting_resolution,[],[f134,f129,f124,f89,f57])).
% 0.99/0.64  fof(f57,plain,(
% 0.99/0.64    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.99/0.64    inference(cnf_transformation,[],[f12])).
% 0.99/0.64  fof(f12,plain,(
% 0.99/0.64    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.99/0.64    inference(flattening,[],[f11])).
% 0.99/0.64  fof(f11,plain,(
% 0.99/0.64    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.99/0.64    inference(ennf_transformation,[],[f4])).
% 0.99/0.64  fof(f4,axiom,(
% 0.99/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 0.99/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).
% 0.99/0.64  fof(f165,plain,(
% 0.99/0.64    ~spl10_19),
% 0.99/0.64    inference(avatar_split_clause,[],[f38,f162])).
% 0.99/0.64  fof(f38,plain,(
% 0.99/0.64    ~v2_struct_0(sK2)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f31,plain,(
% 0.99/0.64    (((((~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) & v5_pre_topc(sK6,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,sK7) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.99/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f30,f29,f28,f27,f26,f25])).
% 0.99/0.64  fof(f25,plain,(
% 0.99/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,sK2,X1) & r1_tmap_1(X2,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.99/0.64    introduced(choice_axiom,[])).
% 0.99/0.64  fof(f26,plain,(
% 0.99/0.64    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,sK2,X1) & r1_tmap_1(X2,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5) & v5_pre_topc(X4,sK2,sK3) & r1_tmap_1(X2,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.99/0.64    introduced(choice_axiom,[])).
% 0.99/0.64  fof(f27,plain,(
% 0.99/0.64    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5) & v5_pre_topc(X4,sK2,sK3) & r1_tmap_1(X2,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5) & v5_pre_topc(X4,sK2,sK3) & r1_tmap_1(sK4,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(X3)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.99/0.64    introduced(choice_axiom,[])).
% 0.99/0.64  fof(f28,plain,(
% 0.99/0.64    ? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),X3,X4),X5) & v5_pre_topc(X4,sK2,sK3) & r1_tmap_1(sK4,sK2,X3,X5) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,X4),X5) & v5_pre_topc(X4,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,X5) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5))),
% 0.99/0.64    introduced(choice_axiom,[])).
% 0.99/0.64  fof(f29,plain,(
% 0.99/0.64    ? [X4] : (? [X5] : (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,X4),X5) & v5_pre_topc(X4,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,X5) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) => (? [X5] : (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),X5) & v5_pre_topc(sK6,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,X5) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 0.99/0.64    introduced(choice_axiom,[])).
% 0.99/0.64  fof(f30,plain,(
% 0.99/0.64    ? [X5] : (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),X5) & v5_pre_topc(sK6,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,X5) & m1_subset_1(X5,u1_struct_0(sK4))) => (~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7) & v5_pre_topc(sK6,sK2,sK3) & r1_tmap_1(sK4,sK2,sK5,sK7) & m1_subset_1(sK7,u1_struct_0(sK4)))),
% 0.99/0.64    introduced(choice_axiom,[])).
% 0.99/0.64  fof(f10,plain,(
% 0.99/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.99/0.64    inference(flattening,[],[f9])).
% 0.99/0.64  fof(f9,plain,(
% 0.99/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5) & (v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5))) & m1_subset_1(X5,u1_struct_0(X2))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.99/0.64    inference(ennf_transformation,[],[f8])).
% 0.99/0.64  % (838)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.99/0.64  fof(f8,negated_conjecture,(
% 0.99/0.64    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5)) => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5))))))))),
% 0.99/0.64    inference(negated_conjecture,[],[f7])).
% 0.99/0.64  fof(f7,conjecture,(
% 0.99/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((v5_pre_topc(X4,X0,X1) & r1_tmap_1(X2,X0,X3,X5)) => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),X3,X4),X5))))))))),
% 0.99/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tmap_1)).
% 0.99/0.64  fof(f160,plain,(
% 0.99/0.64    spl10_18),
% 0.99/0.64    inference(avatar_split_clause,[],[f39,f157])).
% 0.99/0.64  fof(f39,plain,(
% 0.99/0.64    v2_pre_topc(sK2)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f155,plain,(
% 0.99/0.64    spl10_17),
% 0.99/0.64    inference(avatar_split_clause,[],[f40,f152])).
% 0.99/0.64  fof(f40,plain,(
% 0.99/0.64    l1_pre_topc(sK2)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f150,plain,(
% 0.99/0.64    ~spl10_16),
% 0.99/0.64    inference(avatar_split_clause,[],[f41,f147])).
% 0.99/0.64  fof(f41,plain,(
% 0.99/0.64    ~v2_struct_0(sK3)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f145,plain,(
% 0.99/0.64    spl10_15),
% 0.99/0.64    inference(avatar_split_clause,[],[f42,f142])).
% 0.99/0.64  fof(f42,plain,(
% 0.99/0.64    v2_pre_topc(sK3)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f140,plain,(
% 0.99/0.64    spl10_14),
% 0.99/0.64    inference(avatar_split_clause,[],[f43,f137])).
% 0.99/0.64  fof(f43,plain,(
% 0.99/0.64    l1_pre_topc(sK3)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f135,plain,(
% 0.99/0.64    ~spl10_13),
% 0.99/0.64    inference(avatar_split_clause,[],[f44,f132])).
% 0.99/0.64  fof(f44,plain,(
% 0.99/0.64    ~v2_struct_0(sK4)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f130,plain,(
% 0.99/0.64    spl10_12),
% 0.99/0.64    inference(avatar_split_clause,[],[f45,f127])).
% 0.99/0.64  fof(f45,plain,(
% 0.99/0.64    v2_pre_topc(sK4)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f125,plain,(
% 0.99/0.64    spl10_11),
% 0.99/0.64    inference(avatar_split_clause,[],[f46,f122])).
% 0.99/0.64  fof(f46,plain,(
% 0.99/0.64    l1_pre_topc(sK4)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f120,plain,(
% 0.99/0.64    spl10_10),
% 0.99/0.64    inference(avatar_split_clause,[],[f47,f117])).
% 0.99/0.64  fof(f47,plain,(
% 0.99/0.64    v1_funct_1(sK5)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f115,plain,(
% 0.99/0.64    spl10_9),
% 0.99/0.64    inference(avatar_split_clause,[],[f48,f112])).
% 0.99/0.64  fof(f48,plain,(
% 0.99/0.64    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f110,plain,(
% 0.99/0.64    spl10_8),
% 0.99/0.64    inference(avatar_split_clause,[],[f49,f107])).
% 0.99/0.64  fof(f49,plain,(
% 0.99/0.64    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f105,plain,(
% 0.99/0.64    spl10_7),
% 0.99/0.64    inference(avatar_split_clause,[],[f50,f102])).
% 0.99/0.64  fof(f50,plain,(
% 0.99/0.64    v1_funct_1(sK6)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f100,plain,(
% 0.99/0.64    spl10_6),
% 0.99/0.64    inference(avatar_split_clause,[],[f51,f97])).
% 0.99/0.64  fof(f51,plain,(
% 0.99/0.64    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f95,plain,(
% 0.99/0.64    spl10_5),
% 0.99/0.64    inference(avatar_split_clause,[],[f52,f92])).
% 0.99/0.64  fof(f52,plain,(
% 0.99/0.64    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f90,plain,(
% 0.99/0.64    spl10_4),
% 0.99/0.64    inference(avatar_split_clause,[],[f53,f87])).
% 0.99/0.64  fof(f53,plain,(
% 0.99/0.64    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f85,plain,(
% 0.99/0.64    spl10_3),
% 0.99/0.64    inference(avatar_split_clause,[],[f54,f82])).
% 0.99/0.64  fof(f54,plain,(
% 0.99/0.64    r1_tmap_1(sK4,sK2,sK5,sK7)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f80,plain,(
% 0.99/0.64    spl10_2),
% 0.99/0.64    inference(avatar_split_clause,[],[f55,f77])).
% 0.99/0.64  fof(f55,plain,(
% 0.99/0.64    v5_pre_topc(sK6,sK2,sK3)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  fof(f75,plain,(
% 0.99/0.64    ~spl10_1),
% 0.99/0.64    inference(avatar_split_clause,[],[f56,f72])).
% 0.99/0.64  fof(f56,plain,(
% 0.99/0.64    ~r1_tmap_1(sK4,sK3,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6),sK7)),
% 0.99/0.64    inference(cnf_transformation,[],[f31])).
% 0.99/0.64  % SZS output end Proof for theBenchmark
% 0.99/0.64  % (835)------------------------------
% 0.99/0.64  % (835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.99/0.64  % (835)Termination reason: Refutation
% 0.99/0.64  
% 0.99/0.64  % (835)Memory used [KB]: 11129
% 0.99/0.64  % (835)Time elapsed: 0.069 s
% 0.99/0.64  % (835)------------------------------
% 0.99/0.64  % (835)------------------------------
% 0.99/0.64  % (598)Success in time 0.286 s
%------------------------------------------------------------------------------

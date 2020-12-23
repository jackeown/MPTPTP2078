%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  313 ( 753 expanded)
%              Number of leaves         :   75 ( 377 expanded)
%              Depth                    :   32
%              Number of atoms          : 1681 (6618 expanded)
%              Number of equality atoms :   76 ( 751 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1656,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f171,f176,f181,f186,f191,f196,f201,f206,f213,f219,f231,f257,f283,f288,f297,f302,f307,f329,f337,f376,f377,f380,f383,f391,f399,f409,f460,f467,f672,f851,f923,f955,f978,f1047,f1245,f1428,f1499,f1655])).

fof(f1655,plain,
    ( spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_38
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(avatar_contradiction_clause,[],[f1654])).

fof(f1654,plain,
    ( $false
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_38
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1653,f319])).

fof(f319,plain,
    ( v1_funct_2(sK7,k2_struct_0(sK6),k2_struct_0(sK4))
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl10_38
  <=> v1_funct_2(sK7,k2_struct_0(sK6),k2_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f1653,plain,
    ( ~ v1_funct_2(sK7,k2_struct_0(sK6),k2_struct_0(sK4))
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(forward_demodulation,[],[f1652,f398])).

fof(f398,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6)
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl10_42
  <=> u1_struct_0(sK6) = k2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f1652,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK6),k2_struct_0(sK4))
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(forward_demodulation,[],[f1651,f256])).

fof(f256,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl10_26
  <=> u1_struct_0(sK4) = k2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f1651,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_36
    | ~ spl10_37
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1650,f314])).

fof(f314,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK4))))
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl10_37
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f1650,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_36
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(forward_demodulation,[],[f1649,f398])).

fof(f1649,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_21
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_36
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(forward_demodulation,[],[f1648,f256])).

fof(f1648,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_21
    | ~ spl10_32
    | ~ spl10_36
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1647,f306])).

fof(f306,plain,
    ( m1_subset_1(sK8,k2_struct_0(sK6))
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl10_36
  <=> m1_subset_1(sK8,k2_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f1647,plain,
    ( ~ m1_subset_1(sK8,k2_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_21
    | ~ spl10_32
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(forward_demodulation,[],[f1646,f398])).

fof(f1646,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_21
    | ~ spl10_32
    | ~ spl10_41
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1645,f287])).

fof(f287,plain,
    ( m1_subset_1(sK8,k2_struct_0(sK5))
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl10_32
  <=> m1_subset_1(sK8,k2_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f1645,plain,
    ( ~ m1_subset_1(sK8,k2_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_21
    | ~ spl10_41
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(forward_demodulation,[],[f1644,f390])).

fof(f390,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl10_41
  <=> u1_struct_0(sK5) = k2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f1644,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | spl10_19
    | ~ spl10_21
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1643,f205])).

fof(f205,plain,
    ( ~ v2_struct_0(sK3)
    | spl10_19 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl10_19
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f1643,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_18
    | ~ spl10_21
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1642,f200])).

fof(f200,plain,
    ( v2_pre_topc(sK3)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl10_18
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f1642,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_17
    | ~ spl10_21
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1641,f195])).

fof(f195,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl10_17
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f1641,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | spl10_16
    | ~ spl10_21
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1640,f190])).

fof(f190,plain,
    ( ~ v2_struct_0(sK4)
    | spl10_16 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl10_16
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f1640,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_21
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1639,f185])).

fof(f185,plain,
    ( v2_pre_topc(sK4)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl10_15
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f1639,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_14
    | ~ spl10_21
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1638,f180])).

fof(f180,plain,
    ( l1_pre_topc(sK4)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl10_14
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f1638,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | spl10_13
    | ~ spl10_21
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1637,f175])).

fof(f175,plain,
    ( ~ v2_struct_0(sK5)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl10_13
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f1637,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_21
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1636,f170])).

fof(f170,plain,
    ( m1_pre_topc(sK5,sK3)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl10_12
  <=> m1_pre_topc(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f1636,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_21
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1635,f165])).

fof(f165,plain,
    ( ~ v2_struct_0(sK6)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl10_11
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f1635,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_21
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1634,f160])).

fof(f160,plain,
    ( m1_pre_topc(sK6,sK3)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl10_10
  <=> m1_pre_topc(sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f1634,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | ~ m1_pre_topc(sK6,sK3)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_9
    | ~ spl10_21
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1633,f155])).

fof(f155,plain,
    ( v1_funct_1(sK7)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl10_9
  <=> v1_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f1633,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | ~ v1_funct_1(sK7)
    | ~ m1_pre_topc(sK6,sK3)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_21
    | ~ spl10_84
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1632,f998])).

fof(f998,plain,
    ( v1_tsep_1(sK5,sK6)
    | ~ spl10_99 ),
    inference(avatar_component_clause,[],[f997])).

fof(f997,plain,
    ( spl10_99
  <=> v1_tsep_1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).

fof(f1632,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ v1_tsep_1(sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | ~ v1_funct_1(sK7)
    | ~ m1_pre_topc(sK6,sK3)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_21
    | ~ spl10_84 ),
    inference(subsumption_resolution,[],[f1631,f850])).

fof(f850,plain,
    ( m1_pre_topc(sK5,sK6)
    | ~ spl10_84 ),
    inference(avatar_component_clause,[],[f848])).

fof(f848,plain,
    ( spl10_84
  <=> m1_pre_topc(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f1631,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_pre_topc(sK5,sK6)
    | ~ v1_tsep_1(sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | ~ v1_funct_1(sK7)
    | ~ m1_pre_topc(sK6,sK3)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl10_1
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f1630,f115])).

fof(f115,plain,
    ( ~ r1_tmap_1(sK6,sK4,sK7,sK8)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl10_1
  <=> r1_tmap_1(sK6,sK4,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f1630,plain,
    ( r1_tmap_1(sK6,sK4,sK7,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_pre_topc(sK5,sK6)
    | ~ v1_tsep_1(sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | ~ v1_funct_1(sK7)
    | ~ m1_pre_topc(sK6,sK3)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_21 ),
    inference(resolution,[],[f109,f218])).

fof(f218,plain,
    ( r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK8)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl10_21
  <=> r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f1499,plain,
    ( spl10_11
    | spl10_13
    | ~ spl10_39
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_43
    | ~ spl10_47
    | ~ spl10_89
    | ~ spl10_96
    | spl10_99
    | ~ spl10_162 ),
    inference(avatar_contradiction_clause,[],[f1498])).

fof(f1498,plain,
    ( $false
    | spl10_11
    | spl10_13
    | ~ spl10_39
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_43
    | ~ spl10_47
    | ~ spl10_89
    | ~ spl10_96
    | spl10_99
    | ~ spl10_162 ),
    inference(subsumption_resolution,[],[f1497,f897])).

fof(f897,plain,
    ( r1_tarski(k2_struct_0(sK5),k2_struct_0(sK6))
    | ~ spl10_89 ),
    inference(avatar_component_clause,[],[f895])).

fof(f895,plain,
    ( spl10_89
  <=> r1_tarski(k2_struct_0(sK5),k2_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).

fof(f1497,plain,
    ( ~ r1_tarski(k2_struct_0(sK5),k2_struct_0(sK6))
    | spl10_11
    | spl10_13
    | ~ spl10_39
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_43
    | ~ spl10_47
    | ~ spl10_96
    | spl10_99
    | ~ spl10_162 ),
    inference(forward_demodulation,[],[f1496,f390])).

fof(f1496,plain,
    ( ~ r1_tarski(u1_struct_0(sK5),k2_struct_0(sK6))
    | spl10_11
    | spl10_13
    | ~ spl10_39
    | ~ spl10_42
    | ~ spl10_43
    | ~ spl10_47
    | ~ spl10_96
    | spl10_99
    | ~ spl10_162 ),
    inference(forward_demodulation,[],[f1453,f398])).

fof(f1453,plain,
    ( ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK6))
    | spl10_11
    | spl10_13
    | ~ spl10_39
    | ~ spl10_43
    | ~ spl10_47
    | ~ spl10_96
    | spl10_99
    | ~ spl10_162 ),
    inference(unit_resulting_resolution,[],[f175,f448,f326,f165,f976,f408,f999,f1427,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | v1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f1427,plain,
    ( m1_pre_topc(sK6,sK5)
    | ~ spl10_162 ),
    inference(avatar_component_clause,[],[f1425])).

fof(f1425,plain,
    ( spl10_162
  <=> m1_pre_topc(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_162])])).

fof(f999,plain,
    ( ~ v1_tsep_1(sK5,sK6)
    | spl10_99 ),
    inference(avatar_component_clause,[],[f997])).

fof(f408,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl10_43
  <=> m1_pre_topc(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f976,plain,
    ( v1_tsep_1(sK5,sK5)
    | ~ spl10_96 ),
    inference(avatar_component_clause,[],[f974])).

fof(f974,plain,
    ( spl10_96
  <=> v1_tsep_1(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f326,plain,
    ( l1_pre_topc(sK5)
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl10_39
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f448,plain,
    ( v2_pre_topc(sK5)
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl10_47
  <=> v2_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f1428,plain,
    ( spl10_162
    | ~ spl10_105
    | ~ spl10_136 ),
    inference(avatar_split_clause,[],[f1423,f1242,f1044,f1425])).

fof(f1044,plain,
    ( spl10_105
  <=> sP2(sK5,sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_105])])).

fof(f1242,plain,
    ( spl10_136
  <=> sK6 = k1_tsep_1(sK5,sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_136])])).

fof(f1423,plain,
    ( m1_pre_topc(sK6,sK5)
    | ~ spl10_105
    | ~ spl10_136 ),
    inference(forward_demodulation,[],[f1418,f1244])).

fof(f1244,plain,
    ( sK6 = k1_tsep_1(sK5,sK5,sK5)
    | ~ spl10_136 ),
    inference(avatar_component_clause,[],[f1242])).

fof(f1418,plain,
    ( m1_pre_topc(k1_tsep_1(sK5,sK5,sK5),sK5)
    | ~ spl10_105 ),
    inference(unit_resulting_resolution,[],[f1046,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1046,plain,
    ( sP2(sK5,sK5,sK5)
    | ~ spl10_105 ),
    inference(avatar_component_clause,[],[f1044])).

fof(f1245,plain,
    ( spl10_136
    | spl10_13
    | ~ spl10_31
    | ~ spl10_39
    | ~ spl10_41
    | ~ spl10_43
    | ~ spl10_47 ),
    inference(avatar_split_clause,[],[f1240,f446,f406,f388,f325,f280,f173,f1242])).

fof(f280,plain,
    ( spl10_31
  <=> sK6 = g1_pre_topc(k2_struct_0(sK5),u1_pre_topc(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f1240,plain,
    ( sK6 = k1_tsep_1(sK5,sK5,sK5)
    | spl10_13
    | ~ spl10_31
    | ~ spl10_39
    | ~ spl10_41
    | ~ spl10_43
    | ~ spl10_47 ),
    inference(forward_demodulation,[],[f1239,f282])).

fof(f282,plain,
    ( sK6 = g1_pre_topc(k2_struct_0(sK5),u1_pre_topc(sK5))
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f280])).

fof(f1239,plain,
    ( g1_pre_topc(k2_struct_0(sK5),u1_pre_topc(sK5)) = k1_tsep_1(sK5,sK5,sK5)
    | spl10_13
    | ~ spl10_39
    | ~ spl10_41
    | ~ spl10_43
    | ~ spl10_47 ),
    inference(forward_demodulation,[],[f1211,f390])).

fof(f1211,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k1_tsep_1(sK5,sK5,sK5)
    | spl10_13
    | ~ spl10_39
    | ~ spl10_43
    | ~ spl10_47 ),
    inference(unit_resulting_resolution,[],[f175,f448,f326,f175,f408,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f1047,plain,
    ( spl10_105
    | spl10_13
    | ~ spl10_39
    | ~ spl10_43 ),
    inference(avatar_split_clause,[],[f1018,f406,f325,f173,f1044])).

fof(f1018,plain,
    ( sP2(sK5,sK5,sK5)
    | spl10_13
    | ~ spl10_39
    | ~ spl10_43 ),
    inference(unit_resulting_resolution,[],[f175,f326,f175,f408,f175,f408,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f42,f46])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f978,plain,
    ( spl10_96
    | ~ spl10_95 ),
    inference(avatar_split_clause,[],[f972,f950,f974])).

fof(f950,plain,
    ( spl10_95
  <=> sP0(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_95])])).

fof(f972,plain,
    ( v1_tsep_1(sK5,sK5)
    | ~ spl10_95 ),
    inference(resolution,[],[f952,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_pre_topc(X1,X0)
        & v1_tsep_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f952,plain,
    ( sP0(sK5,sK5)
    | ~ spl10_95 ),
    inference(avatar_component_clause,[],[f950])).

fof(f955,plain,
    ( spl10_95
    | ~ spl10_49
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f954,f669,f464,f950])).

fof(f464,plain,
    ( spl10_49
  <=> v3_pre_topc(k2_struct_0(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f669,plain,
    ( spl10_64
  <=> sP1(sK5,k2_struct_0(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f954,plain,
    ( sP0(sK5,sK5)
    | ~ spl10_49
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f947,f466])).

fof(f466,plain,
    ( v3_pre_topc(k2_struct_0(sK5),sK5)
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f464])).

fof(f947,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK5),sK5)
    | sP0(sK5,sK5)
    | ~ spl10_64 ),
    inference(resolution,[],[f671,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | sP0(X0,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP0(X0,X2)
          | ~ v3_pre_topc(X1,X0) )
        & ( v3_pre_topc(X1,X0)
          | ~ sP0(X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X2,X1] :
      ( ( ( sP0(X0,X1)
          | ~ v3_pre_topc(X2,X0) )
        & ( v3_pre_topc(X2,X0)
          | ~ sP0(X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X1)
      <=> v3_pre_topc(X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f671,plain,
    ( sP1(sK5,k2_struct_0(sK5),sK5)
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f669])).

fof(f923,plain,
    ( spl10_89
    | ~ spl10_40
    | ~ spl10_41
    | ~ spl10_84 ),
    inference(avatar_split_clause,[],[f879,f848,f388,f333,f895])).

fof(f333,plain,
    ( spl10_40
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f879,plain,
    ( r1_tarski(k2_struct_0(sK5),k2_struct_0(sK6))
    | ~ spl10_40
    | ~ spl10_41
    | ~ spl10_84 ),
    inference(unit_resulting_resolution,[],[f334,f850,f557])).

fof(f557,plain,
    ( ! [X0] :
        ( r1_tarski(k2_struct_0(sK5),k2_struct_0(X0))
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f550,f84])).

fof(f84,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f550,plain,
    ( ! [X0] :
        ( r1_tarski(k2_struct_0(sK5),k2_struct_0(X0))
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ l1_struct_0(X0) )
    | ~ spl10_41 ),
    inference(superposition,[],[f486,f83])).

fof(f83,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f486,plain,
    ( ! [X4] :
        ( r1_tarski(k2_struct_0(sK5),u1_struct_0(X4))
        | ~ m1_pre_topc(sK5,X4)
        | ~ l1_pre_topc(X4) )
    | ~ spl10_41 ),
    inference(superposition,[],[f89,f390])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f334,plain,
    ( l1_pre_topc(sK6)
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f333])).

fof(f851,plain,
    ( spl10_84
    | ~ spl10_31
    | ~ spl10_39
    | ~ spl10_41
    | ~ spl10_43 ),
    inference(avatar_split_clause,[],[f846,f406,f388,f325,f280,f848])).

fof(f846,plain,
    ( m1_pre_topc(sK5,sK6)
    | ~ spl10_31
    | ~ spl10_39
    | ~ spl10_41
    | ~ spl10_43 ),
    inference(forward_demodulation,[],[f845,f282])).

fof(f845,plain,
    ( m1_pre_topc(sK5,g1_pre_topc(k2_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl10_39
    | ~ spl10_41
    | ~ spl10_43 ),
    inference(forward_demodulation,[],[f830,f390])).

fof(f830,plain,
    ( m1_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ spl10_39
    | ~ spl10_43 ),
    inference(unit_resulting_resolution,[],[f326,f326,f408,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f672,plain,
    ( spl10_64
    | ~ spl10_39
    | ~ spl10_41
    | ~ spl10_43
    | ~ spl10_47 ),
    inference(avatar_split_clause,[],[f667,f446,f406,f388,f325,f669])).

fof(f667,plain,
    ( sP1(sK5,k2_struct_0(sK5),sK5)
    | ~ spl10_39
    | ~ spl10_41
    | ~ spl10_43
    | ~ spl10_47 ),
    inference(forward_demodulation,[],[f652,f390])).

fof(f652,plain,
    ( sP1(sK5,u1_struct_0(sK5),sK5)
    | ~ spl10_39
    | ~ spl10_43
    | ~ spl10_47 ),
    inference(unit_resulting_resolution,[],[f448,f326,f408,f207])).

fof(f207,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f111,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f111,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f40,f44,f43])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f467,plain,
    ( spl10_49
    | ~ spl10_39
    | ~ spl10_47 ),
    inference(avatar_split_clause,[],[f462,f446,f325,f464])).

fof(f462,plain,
    ( v3_pre_topc(k2_struct_0(sK5),sK5)
    | ~ spl10_39
    | ~ spl10_47 ),
    inference(unit_resulting_resolution,[],[f326,f448,f96])).

fof(f96,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f460,plain,
    ( spl10_47
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f459,f198,f193,f168,f446])).

fof(f459,plain,
    ( v2_pre_topc(sK5)
    | ~ spl10_12
    | ~ spl10_17
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f458,f200])).

fof(f458,plain,
    ( v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_12
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f439,f195])).

fof(f439,plain,
    ( v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_12 ),
    inference(resolution,[],[f97,f170])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f409,plain,
    ( spl10_43
    | ~ spl10_39 ),
    inference(avatar_split_clause,[],[f403,f325,f406])).

fof(f403,plain,
    ( m1_pre_topc(sK5,sK5)
    | ~ spl10_39 ),
    inference(unit_resulting_resolution,[],[f326,f85])).

fof(f85,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f399,plain,
    ( spl10_42
    | ~ spl10_33 ),
    inference(avatar_split_clause,[],[f394,f290,f396])).

fof(f290,plain,
    ( spl10_33
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f394,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6)
    | ~ spl10_33 ),
    inference(unit_resulting_resolution,[],[f291,f83])).

fof(f291,plain,
    ( l1_struct_0(sK6)
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f290])).

fof(f391,plain,
    ( spl10_41
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f386,f276,f388])).

fof(f276,plain,
    ( spl10_30
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f386,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f277,f83])).

fof(f277,plain,
    ( l1_struct_0(sK5)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f276])).

fof(f383,plain,
    ( spl10_40
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f342,f193,f158,f333])).

fof(f342,plain,
    ( l1_pre_topc(sK6)
    | ~ spl10_10
    | ~ spl10_17 ),
    inference(unit_resulting_resolution,[],[f195,f160,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f380,plain,
    ( spl10_39
    | ~ spl10_12
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f345,f193,f168,f325])).

fof(f345,plain,
    ( l1_pre_topc(sK5)
    | ~ spl10_12
    | ~ spl10_17 ),
    inference(unit_resulting_resolution,[],[f195,f170,f88])).

fof(f377,plain,
    ( u1_struct_0(sK4) != k2_struct_0(sK4)
    | v1_funct_2(sK7,k2_struct_0(sK6),k2_struct_0(sK4))
    | ~ v1_funct_2(sK7,k2_struct_0(sK6),u1_struct_0(sK4)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f376,plain,
    ( u1_struct_0(sK4) != k2_struct_0(sK4)
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK4))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),u1_struct_0(sK4)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f337,plain,
    ( ~ spl10_40
    | spl10_33 ),
    inference(avatar_split_clause,[],[f331,f290,f333])).

fof(f331,plain,
    ( ~ l1_pre_topc(sK6)
    | spl10_33 ),
    inference(resolution,[],[f292,f84])).

fof(f292,plain,
    ( ~ l1_struct_0(sK6)
    | spl10_33 ),
    inference(avatar_component_clause,[],[f290])).

fof(f329,plain,
    ( ~ spl10_39
    | spl10_30 ),
    inference(avatar_split_clause,[],[f323,f276,f325])).

fof(f323,plain,
    ( ~ l1_pre_topc(sK5)
    | spl10_30 ),
    inference(resolution,[],[f278,f84])).

fof(f278,plain,
    ( ~ l1_struct_0(sK5)
    | spl10_30 ),
    inference(avatar_component_clause,[],[f276])).

fof(f307,plain,
    ( ~ spl10_33
    | spl10_36
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f252,f133,f304,f290])).

fof(f133,plain,
    ( spl10_5
  <=> m1_subset_1(sK8,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f252,plain,
    ( m1_subset_1(sK8,k2_struct_0(sK6))
    | ~ l1_struct_0(sK6)
    | ~ spl10_5 ),
    inference(superposition,[],[f135,f83])).

fof(f135,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f302,plain,
    ( ~ spl10_33
    | spl10_35
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f251,f148,f299,f290])).

fof(f299,plain,
    ( spl10_35
  <=> v1_funct_2(sK7,k2_struct_0(sK6),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f148,plain,
    ( spl10_8
  <=> v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f251,plain,
    ( v1_funct_2(sK7,k2_struct_0(sK6),u1_struct_0(sK4))
    | ~ l1_struct_0(sK6)
    | ~ spl10_8 ),
    inference(superposition,[],[f150,f83])).

fof(f150,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f297,plain,
    ( ~ spl10_33
    | spl10_34
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f250,f143,f294,f290])).

fof(f294,plain,
    ( spl10_34
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f143,plain,
    ( spl10_7
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f250,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),u1_struct_0(sK4))))
    | ~ l1_struct_0(sK6)
    | ~ spl10_7 ),
    inference(superposition,[],[f145,f83])).

fof(f145,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f288,plain,
    ( ~ spl10_30
    | spl10_32
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f249,f210,f285,f276])).

fof(f210,plain,
    ( spl10_20
  <=> m1_subset_1(sK8,u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f249,plain,
    ( m1_subset_1(sK8,k2_struct_0(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl10_20 ),
    inference(superposition,[],[f212,f83])).

fof(f212,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f283,plain,
    ( ~ spl10_30
    | spl10_31
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f248,f138,f280,f276])).

fof(f138,plain,
    ( spl10_6
  <=> g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f248,plain,
    ( sK6 = g1_pre_topc(k2_struct_0(sK5),u1_pre_topc(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl10_6 ),
    inference(superposition,[],[f140,f83])).

fof(f140,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f257,plain,
    ( spl10_26
    | ~ spl10_23 ),
    inference(avatar_split_clause,[],[f245,f228,f254])).

fof(f228,plain,
    ( spl10_23
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f245,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl10_23 ),
    inference(unit_resulting_resolution,[],[f230,f83])).

fof(f230,plain,
    ( l1_struct_0(sK4)
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f228])).

fof(f231,plain,
    ( spl10_23
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f220,f178,f228])).

fof(f220,plain,
    ( l1_struct_0(sK4)
    | ~ spl10_14 ),
    inference(unit_resulting_resolution,[],[f180,f84])).

fof(f219,plain,
    ( spl10_21
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f214,f123,f118,f216])).

fof(f118,plain,
    ( spl10_2
  <=> r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f123,plain,
    ( spl10_3
  <=> sK8 = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f214,plain,
    ( r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK8)
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f120,f125])).

fof(f125,plain,
    ( sK8 = sK9
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f120,plain,
    ( r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f213,plain,
    ( spl10_20
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f208,f128,f123,f210])).

fof(f128,plain,
    ( spl10_4
  <=> m1_subset_1(sK9,u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f208,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(backward_demodulation,[],[f130,f125])).

fof(f130,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f206,plain,(
    ~ spl10_19 ),
    inference(avatar_split_clause,[],[f64,f203])).

fof(f64,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ~ r1_tmap_1(sK6,sK4,sK7,sK8)
    & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9)
    & sK8 = sK9
    & m1_subset_1(sK9,u1_struct_0(sK5))
    & m1_subset_1(sK8,u1_struct_0(sK6))
    & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    & v1_funct_1(sK7)
    & m1_pre_topc(sK6,sK3)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f19,f54,f53,f52,f51,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,X4,X5)
                                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
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
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK3,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK3)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK3)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,X1,X4,X5)
                            & r1_tmap_1(X2,X1,k3_tmap_1(sK3,X1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK3)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK3)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,sK4,X4,X5)
                          & r1_tmap_1(X2,sK4,k3_tmap_1(sK3,sK4,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK3)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK3)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,sK4,X4,X5)
                        & r1_tmap_1(X2,sK4,k3_tmap_1(sK3,sK4,X3,X2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK3)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK3)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,sK4,X4,X5)
                      & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,X3,sK5,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK5)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK3)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK5,sK3)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X3,sK4,X4,X5)
                    & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,X3,sK5,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK5)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK3)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK6,sK4,X4,X5)
                  & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK5)) )
              & m1_subset_1(X5,u1_struct_0(sK6)) )
          & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
          & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK4))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK6,sK3)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK6,sK4,X4,X5)
                & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,X4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK5)) )
            & m1_subset_1(X5,u1_struct_0(sK6)) )
        & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
        & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK4))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK6,sK4,sK7,X5)
              & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK5)) )
          & m1_subset_1(X5,u1_struct_0(sK6)) )
      & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
      & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK6,sK4,sK7,X5)
            & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK5)) )
        & m1_subset_1(X5,u1_struct_0(sK6)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK6,sK4,sK7,sK8)
          & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6)
          & sK8 = X6
          & m1_subset_1(X6,u1_struct_0(sK5)) )
      & m1_subset_1(sK8,u1_struct_0(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK6,sK4,sK7,sK8)
        & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6)
        & sK8 = X6
        & m1_subset_1(X6,u1_struct_0(sK5)) )
   => ( ~ r1_tmap_1(sK6,sK4,sK7,sK8)
      & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9)
      & sK8 = sK9
      & m1_subset_1(sK9,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f201,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f65,f198])).

fof(f65,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f196,plain,(
    spl10_17 ),
    inference(avatar_split_clause,[],[f66,f193])).

fof(f66,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f191,plain,(
    ~ spl10_16 ),
    inference(avatar_split_clause,[],[f67,f188])).

fof(f67,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f186,plain,(
    spl10_15 ),
    inference(avatar_split_clause,[],[f68,f183])).

fof(f68,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f181,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f69,f178])).

fof(f69,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f176,plain,(
    ~ spl10_13 ),
    inference(avatar_split_clause,[],[f70,f173])).

fof(f70,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f171,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f71,f168])).

fof(f71,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f166,plain,(
    ~ spl10_11 ),
    inference(avatar_split_clause,[],[f72,f163])).

fof(f72,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f161,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f73,f158])).

fof(f73,plain,(
    m1_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f156,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f74,f153])).

fof(f74,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f151,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f75,f148])).

fof(f75,plain,(
    v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f146,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f76,f143])).

fof(f76,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f141,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f77,f138])).

fof(f77,plain,(
    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 ),
    inference(cnf_transformation,[],[f55])).

fof(f136,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f78,f133])).

fof(f78,plain,(
    m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f55])).

fof(f131,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f79,f128])).

fof(f79,plain,(
    m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f55])).

fof(f126,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f80,f123])).

fof(f80,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f55])).

fof(f121,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f81,f118])).

fof(f81,plain,(
    r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9) ),
    inference(cnf_transformation,[],[f55])).

fof(f116,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f82,f113])).

fof(f82,plain,(
    ~ r1_tmap_1(sK6,sK4,sK7,sK8) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:53:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (28209)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (28214)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (28223)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (28217)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (28215)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (28213)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (28222)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (28216)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (28210)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (28211)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (28226)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (28225)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (28212)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (28208)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (28218)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (28221)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (28220)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (28219)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (28228)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (28224)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (28227)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.56  % (28224)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f1656,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f171,f176,f181,f186,f191,f196,f201,f206,f213,f219,f231,f257,f283,f288,f297,f302,f307,f329,f337,f376,f377,f380,f383,f391,f399,f409,f460,f467,f672,f851,f923,f955,f978,f1047,f1245,f1428,f1499,f1655])).
% 0.22/0.56  fof(f1655,plain,(
% 0.22/0.56    spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_21 | ~spl10_26 | ~spl10_32 | ~spl10_36 | ~spl10_37 | ~spl10_38 | ~spl10_41 | ~spl10_42 | ~spl10_84 | ~spl10_99),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f1654])).
% 0.22/0.56  fof(f1654,plain,(
% 0.22/0.56    $false | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_21 | ~spl10_26 | ~spl10_32 | ~spl10_36 | ~spl10_37 | ~spl10_38 | ~spl10_41 | ~spl10_42 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1653,f319])).
% 0.22/0.56  fof(f319,plain,(
% 0.22/0.56    v1_funct_2(sK7,k2_struct_0(sK6),k2_struct_0(sK4)) | ~spl10_38),
% 0.22/0.56    inference(avatar_component_clause,[],[f318])).
% 0.22/0.56  fof(f318,plain,(
% 0.22/0.56    spl10_38 <=> v1_funct_2(sK7,k2_struct_0(sK6),k2_struct_0(sK4))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 0.22/0.56  fof(f1653,plain,(
% 0.22/0.56    ~v1_funct_2(sK7,k2_struct_0(sK6),k2_struct_0(sK4)) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_21 | ~spl10_26 | ~spl10_32 | ~spl10_36 | ~spl10_37 | ~spl10_41 | ~spl10_42 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(forward_demodulation,[],[f1652,f398])).
% 0.22/0.56  fof(f398,plain,(
% 0.22/0.56    u1_struct_0(sK6) = k2_struct_0(sK6) | ~spl10_42),
% 0.22/0.56    inference(avatar_component_clause,[],[f396])).
% 0.22/0.56  fof(f396,plain,(
% 0.22/0.56    spl10_42 <=> u1_struct_0(sK6) = k2_struct_0(sK6)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).
% 0.22/0.56  fof(f1652,plain,(
% 0.22/0.56    ~v1_funct_2(sK7,u1_struct_0(sK6),k2_struct_0(sK4)) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_21 | ~spl10_26 | ~spl10_32 | ~spl10_36 | ~spl10_37 | ~spl10_41 | ~spl10_42 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(forward_demodulation,[],[f1651,f256])).
% 0.22/0.56  fof(f256,plain,(
% 0.22/0.56    u1_struct_0(sK4) = k2_struct_0(sK4) | ~spl10_26),
% 0.22/0.56    inference(avatar_component_clause,[],[f254])).
% 0.22/0.56  fof(f254,plain,(
% 0.22/0.56    spl10_26 <=> u1_struct_0(sK4) = k2_struct_0(sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.22/0.56  fof(f1651,plain,(
% 0.22/0.56    ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_21 | ~spl10_26 | ~spl10_32 | ~spl10_36 | ~spl10_37 | ~spl10_41 | ~spl10_42 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1650,f314])).
% 0.22/0.56  fof(f314,plain,(
% 0.22/0.56    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK4)))) | ~spl10_37),
% 0.22/0.56    inference(avatar_component_clause,[],[f313])).
% 0.22/0.56  fof(f313,plain,(
% 0.22/0.56    spl10_37 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK4))))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).
% 0.22/0.56  fof(f1650,plain,(
% 0.22/0.56    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_21 | ~spl10_26 | ~spl10_32 | ~spl10_36 | ~spl10_41 | ~spl10_42 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(forward_demodulation,[],[f1649,f398])).
% 0.22/0.56  fof(f1649,plain,(
% 0.22/0.56    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k2_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_21 | ~spl10_26 | ~spl10_32 | ~spl10_36 | ~spl10_41 | ~spl10_42 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(forward_demodulation,[],[f1648,f256])).
% 0.22/0.56  fof(f1648,plain,(
% 0.22/0.56    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_21 | ~spl10_32 | ~spl10_36 | ~spl10_41 | ~spl10_42 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1647,f306])).
% 0.22/0.56  fof(f306,plain,(
% 0.22/0.56    m1_subset_1(sK8,k2_struct_0(sK6)) | ~spl10_36),
% 0.22/0.56    inference(avatar_component_clause,[],[f304])).
% 0.22/0.56  fof(f304,plain,(
% 0.22/0.56    spl10_36 <=> m1_subset_1(sK8,k2_struct_0(sK6))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 0.22/0.56  fof(f1647,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,k2_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_21 | ~spl10_32 | ~spl10_41 | ~spl10_42 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(forward_demodulation,[],[f1646,f398])).
% 0.22/0.56  fof(f1646,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_21 | ~spl10_32 | ~spl10_41 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1645,f287])).
% 0.22/0.56  fof(f287,plain,(
% 0.22/0.56    m1_subset_1(sK8,k2_struct_0(sK5)) | ~spl10_32),
% 0.22/0.56    inference(avatar_component_clause,[],[f285])).
% 0.22/0.56  fof(f285,plain,(
% 0.22/0.56    spl10_32 <=> m1_subset_1(sK8,k2_struct_0(sK5))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).
% 0.22/0.56  fof(f1645,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,k2_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_21 | ~spl10_41 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(forward_demodulation,[],[f1644,f390])).
% 0.22/0.56  fof(f390,plain,(
% 0.22/0.56    u1_struct_0(sK5) = k2_struct_0(sK5) | ~spl10_41),
% 0.22/0.56    inference(avatar_component_clause,[],[f388])).
% 0.22/0.56  fof(f388,plain,(
% 0.22/0.56    spl10_41 <=> u1_struct_0(sK5) = k2_struct_0(sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 0.22/0.56  fof(f1644,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | spl10_19 | ~spl10_21 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1643,f205])).
% 0.22/0.56  fof(f205,plain,(
% 0.22/0.56    ~v2_struct_0(sK3) | spl10_19),
% 0.22/0.56    inference(avatar_component_clause,[],[f203])).
% 0.22/0.56  fof(f203,plain,(
% 0.22/0.56    spl10_19 <=> v2_struct_0(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.22/0.56  fof(f1643,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | v2_struct_0(sK3) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_18 | ~spl10_21 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1642,f200])).
% 0.22/0.56  fof(f200,plain,(
% 0.22/0.56    v2_pre_topc(sK3) | ~spl10_18),
% 0.22/0.56    inference(avatar_component_clause,[],[f198])).
% 0.22/0.56  fof(f198,plain,(
% 0.22/0.56    spl10_18 <=> v2_pre_topc(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.22/0.56  fof(f1642,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_17 | ~spl10_21 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1641,f195])).
% 0.22/0.56  fof(f195,plain,(
% 0.22/0.56    l1_pre_topc(sK3) | ~spl10_17),
% 0.22/0.56    inference(avatar_component_clause,[],[f193])).
% 0.22/0.56  fof(f193,plain,(
% 0.22/0.56    spl10_17 <=> l1_pre_topc(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.22/0.56  fof(f1641,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | spl10_16 | ~spl10_21 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1640,f190])).
% 0.22/0.56  fof(f190,plain,(
% 0.22/0.56    ~v2_struct_0(sK4) | spl10_16),
% 0.22/0.56    inference(avatar_component_clause,[],[f188])).
% 0.22/0.56  fof(f188,plain,(
% 0.22/0.56    spl10_16 <=> v2_struct_0(sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.22/0.56  fof(f1640,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_21 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1639,f185])).
% 0.22/0.56  fof(f185,plain,(
% 0.22/0.56    v2_pre_topc(sK4) | ~spl10_15),
% 0.22/0.56    inference(avatar_component_clause,[],[f183])).
% 0.22/0.56  fof(f183,plain,(
% 0.22/0.56    spl10_15 <=> v2_pre_topc(sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.22/0.56  fof(f1639,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_14 | ~spl10_21 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1638,f180])).
% 0.22/0.56  fof(f180,plain,(
% 0.22/0.56    l1_pre_topc(sK4) | ~spl10_14),
% 0.22/0.56    inference(avatar_component_clause,[],[f178])).
% 0.22/0.56  fof(f178,plain,(
% 0.22/0.56    spl10_14 <=> l1_pre_topc(sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.22/0.56  fof(f1638,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | spl10_13 | ~spl10_21 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1637,f175])).
% 0.22/0.56  fof(f175,plain,(
% 0.22/0.56    ~v2_struct_0(sK5) | spl10_13),
% 0.22/0.56    inference(avatar_component_clause,[],[f173])).
% 0.22/0.56  fof(f173,plain,(
% 0.22/0.56    spl10_13 <=> v2_struct_0(sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.22/0.56  fof(f1637,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_12 | ~spl10_21 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1636,f170])).
% 0.22/0.56  fof(f170,plain,(
% 0.22/0.56    m1_pre_topc(sK5,sK3) | ~spl10_12),
% 0.22/0.56    inference(avatar_component_clause,[],[f168])).
% 0.22/0.56  fof(f168,plain,(
% 0.22/0.56    spl10_12 <=> m1_pre_topc(sK5,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.22/0.56  fof(f1636,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_9 | ~spl10_10 | spl10_11 | ~spl10_21 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1635,f165])).
% 0.22/0.56  fof(f165,plain,(
% 0.22/0.56    ~v2_struct_0(sK6) | spl10_11),
% 0.22/0.56    inference(avatar_component_clause,[],[f163])).
% 0.22/0.56  fof(f163,plain,(
% 0.22/0.56    spl10_11 <=> v2_struct_0(sK6)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.22/0.56  fof(f1635,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_9 | ~spl10_10 | ~spl10_21 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1634,f160])).
% 0.22/0.56  fof(f160,plain,(
% 0.22/0.56    m1_pre_topc(sK6,sK3) | ~spl10_10),
% 0.22/0.56    inference(avatar_component_clause,[],[f158])).
% 0.22/0.56  fof(f158,plain,(
% 0.22/0.56    spl10_10 <=> m1_pre_topc(sK6,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.22/0.56  fof(f1634,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | ~m1_pre_topc(sK6,sK3) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_9 | ~spl10_21 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1633,f155])).
% 0.22/0.56  fof(f155,plain,(
% 0.22/0.56    v1_funct_1(sK7) | ~spl10_9),
% 0.22/0.56    inference(avatar_component_clause,[],[f153])).
% 0.22/0.56  fof(f153,plain,(
% 0.22/0.56    spl10_9 <=> v1_funct_1(sK7)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.22/0.56  fof(f1633,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | ~v1_funct_1(sK7) | ~m1_pre_topc(sK6,sK3) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_21 | ~spl10_84 | ~spl10_99)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1632,f998])).
% 0.22/0.56  fof(f998,plain,(
% 0.22/0.56    v1_tsep_1(sK5,sK6) | ~spl10_99),
% 0.22/0.56    inference(avatar_component_clause,[],[f997])).
% 0.22/0.56  fof(f997,plain,(
% 0.22/0.56    spl10_99 <=> v1_tsep_1(sK5,sK6)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).
% 0.22/0.56  fof(f1632,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~v1_tsep_1(sK5,sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | ~v1_funct_1(sK7) | ~m1_pre_topc(sK6,sK3) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_21 | ~spl10_84)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1631,f850])).
% 0.22/0.56  fof(f850,plain,(
% 0.22/0.56    m1_pre_topc(sK5,sK6) | ~spl10_84),
% 0.22/0.56    inference(avatar_component_clause,[],[f848])).
% 0.22/0.56  fof(f848,plain,(
% 0.22/0.56    spl10_84 <=> m1_pre_topc(sK5,sK6)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).
% 0.22/0.56  fof(f1631,plain,(
% 0.22/0.56    ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_pre_topc(sK5,sK6) | ~v1_tsep_1(sK5,sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | ~v1_funct_1(sK7) | ~m1_pre_topc(sK6,sK3) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl10_1 | ~spl10_21)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1630,f115])).
% 0.22/0.56  fof(f115,plain,(
% 0.22/0.56    ~r1_tmap_1(sK6,sK4,sK7,sK8) | spl10_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f113])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    spl10_1 <=> r1_tmap_1(sK6,sK4,sK7,sK8)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.22/0.56  fof(f1630,plain,(
% 0.22/0.56    r1_tmap_1(sK6,sK4,sK7,sK8) | ~m1_subset_1(sK8,u1_struct_0(sK5)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_pre_topc(sK5,sK6) | ~v1_tsep_1(sK5,sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | ~v1_funct_1(sK7) | ~m1_pre_topc(sK6,sK3) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl10_21),
% 0.22/0.56    inference(resolution,[],[f109,f218])).
% 0.22/0.56  fof(f218,plain,(
% 0.22/0.56    r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK8) | ~spl10_21),
% 0.22/0.56    inference(avatar_component_clause,[],[f216])).
% 0.22/0.56  fof(f216,plain,(
% 0.22/0.56    spl10_21 <=> r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK8)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f92])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.22/0.56  fof(f1499,plain,(
% 0.22/0.56    spl10_11 | spl10_13 | ~spl10_39 | ~spl10_41 | ~spl10_42 | ~spl10_43 | ~spl10_47 | ~spl10_89 | ~spl10_96 | spl10_99 | ~spl10_162),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f1498])).
% 0.22/0.56  fof(f1498,plain,(
% 0.22/0.56    $false | (spl10_11 | spl10_13 | ~spl10_39 | ~spl10_41 | ~spl10_42 | ~spl10_43 | ~spl10_47 | ~spl10_89 | ~spl10_96 | spl10_99 | ~spl10_162)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1497,f897])).
% 0.22/0.56  fof(f897,plain,(
% 0.22/0.56    r1_tarski(k2_struct_0(sK5),k2_struct_0(sK6)) | ~spl10_89),
% 0.22/0.56    inference(avatar_component_clause,[],[f895])).
% 0.22/0.56  fof(f895,plain,(
% 0.22/0.56    spl10_89 <=> r1_tarski(k2_struct_0(sK5),k2_struct_0(sK6))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).
% 0.22/0.56  fof(f1497,plain,(
% 0.22/0.56    ~r1_tarski(k2_struct_0(sK5),k2_struct_0(sK6)) | (spl10_11 | spl10_13 | ~spl10_39 | ~spl10_41 | ~spl10_42 | ~spl10_43 | ~spl10_47 | ~spl10_96 | spl10_99 | ~spl10_162)),
% 0.22/0.56    inference(forward_demodulation,[],[f1496,f390])).
% 0.22/0.56  fof(f1496,plain,(
% 0.22/0.56    ~r1_tarski(u1_struct_0(sK5),k2_struct_0(sK6)) | (spl10_11 | spl10_13 | ~spl10_39 | ~spl10_42 | ~spl10_43 | ~spl10_47 | ~spl10_96 | spl10_99 | ~spl10_162)),
% 0.22/0.56    inference(forward_demodulation,[],[f1453,f398])).
% 0.22/0.56  fof(f1453,plain,(
% 0.22/0.56    ~r1_tarski(u1_struct_0(sK5),u1_struct_0(sK6)) | (spl10_11 | spl10_13 | ~spl10_39 | ~spl10_43 | ~spl10_47 | ~spl10_96 | spl10_99 | ~spl10_162)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f175,f448,f326,f165,f976,f408,f999,f1427,f94])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).
% 0.22/0.56  fof(f1427,plain,(
% 0.22/0.56    m1_pre_topc(sK6,sK5) | ~spl10_162),
% 0.22/0.56    inference(avatar_component_clause,[],[f1425])).
% 0.22/0.56  fof(f1425,plain,(
% 0.22/0.56    spl10_162 <=> m1_pre_topc(sK6,sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_162])])).
% 0.22/0.56  fof(f999,plain,(
% 0.22/0.56    ~v1_tsep_1(sK5,sK6) | spl10_99),
% 0.22/0.56    inference(avatar_component_clause,[],[f997])).
% 0.22/0.56  fof(f408,plain,(
% 0.22/0.56    m1_pre_topc(sK5,sK5) | ~spl10_43),
% 0.22/0.56    inference(avatar_component_clause,[],[f406])).
% 0.22/0.56  fof(f406,plain,(
% 0.22/0.56    spl10_43 <=> m1_pre_topc(sK5,sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).
% 0.22/0.56  fof(f976,plain,(
% 0.22/0.56    v1_tsep_1(sK5,sK5) | ~spl10_96),
% 0.22/0.56    inference(avatar_component_clause,[],[f974])).
% 0.22/0.56  fof(f974,plain,(
% 0.22/0.56    spl10_96 <=> v1_tsep_1(sK5,sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).
% 0.22/0.56  fof(f326,plain,(
% 0.22/0.56    l1_pre_topc(sK5) | ~spl10_39),
% 0.22/0.56    inference(avatar_component_clause,[],[f325])).
% 0.22/0.56  fof(f325,plain,(
% 0.22/0.56    spl10_39 <=> l1_pre_topc(sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).
% 0.22/0.56  fof(f448,plain,(
% 0.22/0.56    v2_pre_topc(sK5) | ~spl10_47),
% 0.22/0.56    inference(avatar_component_clause,[],[f446])).
% 0.22/0.56  fof(f446,plain,(
% 0.22/0.56    spl10_47 <=> v2_pre_topc(sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).
% 0.22/0.56  fof(f1428,plain,(
% 0.22/0.56    spl10_162 | ~spl10_105 | ~spl10_136),
% 0.22/0.56    inference(avatar_split_clause,[],[f1423,f1242,f1044,f1425])).
% 0.22/0.56  fof(f1044,plain,(
% 0.22/0.56    spl10_105 <=> sP2(sK5,sK5,sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_105])])).
% 0.22/0.56  fof(f1242,plain,(
% 0.22/0.56    spl10_136 <=> sK6 = k1_tsep_1(sK5,sK5,sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_136])])).
% 0.22/0.56  fof(f1423,plain,(
% 0.22/0.56    m1_pre_topc(sK6,sK5) | (~spl10_105 | ~spl10_136)),
% 0.22/0.56    inference(forward_demodulation,[],[f1418,f1244])).
% 0.22/0.56  fof(f1244,plain,(
% 0.22/0.56    sK6 = k1_tsep_1(sK5,sK5,sK5) | ~spl10_136),
% 0.22/0.56    inference(avatar_component_clause,[],[f1242])).
% 0.22/0.56  fof(f1418,plain,(
% 0.22/0.56    m1_pre_topc(k1_tsep_1(sK5,sK5,sK5),sK5) | ~spl10_105),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f1046,f107])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP2(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP2(X0,X1,X2))),
% 0.22/0.56    inference(rectify,[],[f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP2(X0,X2,X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP2(X0,X2,X1))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.56  fof(f1046,plain,(
% 0.22/0.56    sP2(sK5,sK5,sK5) | ~spl10_105),
% 0.22/0.56    inference(avatar_component_clause,[],[f1044])).
% 0.22/0.56  fof(f1245,plain,(
% 0.22/0.56    spl10_136 | spl10_13 | ~spl10_31 | ~spl10_39 | ~spl10_41 | ~spl10_43 | ~spl10_47),
% 0.22/0.56    inference(avatar_split_clause,[],[f1240,f446,f406,f388,f325,f280,f173,f1242])).
% 0.22/0.56  fof(f280,plain,(
% 0.22/0.56    spl10_31 <=> sK6 = g1_pre_topc(k2_struct_0(sK5),u1_pre_topc(sK5))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 0.22/0.56  fof(f1240,plain,(
% 0.22/0.56    sK6 = k1_tsep_1(sK5,sK5,sK5) | (spl10_13 | ~spl10_31 | ~spl10_39 | ~spl10_41 | ~spl10_43 | ~spl10_47)),
% 0.22/0.56    inference(forward_demodulation,[],[f1239,f282])).
% 0.22/0.56  fof(f282,plain,(
% 0.22/0.56    sK6 = g1_pre_topc(k2_struct_0(sK5),u1_pre_topc(sK5)) | ~spl10_31),
% 0.22/0.56    inference(avatar_component_clause,[],[f280])).
% 0.22/0.56  fof(f1239,plain,(
% 0.22/0.56    g1_pre_topc(k2_struct_0(sK5),u1_pre_topc(sK5)) = k1_tsep_1(sK5,sK5,sK5) | (spl10_13 | ~spl10_39 | ~spl10_41 | ~spl10_43 | ~spl10_47)),
% 0.22/0.56    inference(forward_demodulation,[],[f1211,f390])).
% 0.22/0.56  fof(f1211,plain,(
% 0.22/0.56    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = k1_tsep_1(sK5,sK5,sK5) | (spl10_13 | ~spl10_39 | ~spl10_43 | ~spl10_47)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f175,f448,f326,f175,f408,f93])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).
% 0.22/0.56  fof(f1047,plain,(
% 0.22/0.56    spl10_105 | spl10_13 | ~spl10_39 | ~spl10_43),
% 0.22/0.56    inference(avatar_split_clause,[],[f1018,f406,f325,f173,f1044])).
% 0.22/0.56  fof(f1018,plain,(
% 0.22/0.56    sP2(sK5,sK5,sK5) | (spl10_13 | ~spl10_39 | ~spl10_43)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f175,f326,f175,f408,f175,f408,f108])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (sP2(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (sP2(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(definition_folding,[],[f42,f46])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.22/0.56  fof(f978,plain,(
% 0.22/0.56    spl10_96 | ~spl10_95),
% 0.22/0.56    inference(avatar_split_clause,[],[f972,f950,f974])).
% 0.22/0.56  fof(f950,plain,(
% 0.22/0.56    spl10_95 <=> sP0(sK5,sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_95])])).
% 0.22/0.56  fof(f972,plain,(
% 0.22/0.56    v1_tsep_1(sK5,sK5) | ~spl10_95),
% 0.22/0.56    inference(resolution,[],[f952,f101])).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~sP0(X0,X1) | v1_tsep_1(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f61])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ! [X0,X1] : ((sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 0.22/0.56    inference(flattening,[],[f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ! [X0,X1] : ((sP0(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ! [X0,X1] : (sP0(X0,X1) <=> (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.56  fof(f952,plain,(
% 0.22/0.56    sP0(sK5,sK5) | ~spl10_95),
% 0.22/0.56    inference(avatar_component_clause,[],[f950])).
% 0.22/0.56  fof(f955,plain,(
% 0.22/0.56    spl10_95 | ~spl10_49 | ~spl10_64),
% 0.22/0.56    inference(avatar_split_clause,[],[f954,f669,f464,f950])).
% 0.22/0.56  fof(f464,plain,(
% 0.22/0.56    spl10_49 <=> v3_pre_topc(k2_struct_0(sK5),sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).
% 0.22/0.56  fof(f669,plain,(
% 0.22/0.56    spl10_64 <=> sP1(sK5,k2_struct_0(sK5),sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).
% 0.22/0.56  fof(f954,plain,(
% 0.22/0.56    sP0(sK5,sK5) | (~spl10_49 | ~spl10_64)),
% 0.22/0.56    inference(subsumption_resolution,[],[f947,f466])).
% 0.22/0.56  fof(f466,plain,(
% 0.22/0.56    v3_pre_topc(k2_struct_0(sK5),sK5) | ~spl10_49),
% 0.22/0.56    inference(avatar_component_clause,[],[f464])).
% 0.22/0.56  fof(f947,plain,(
% 0.22/0.56    ~v3_pre_topc(k2_struct_0(sK5),sK5) | sP0(sK5,sK5) | ~spl10_64),
% 0.22/0.56    inference(resolution,[],[f671,f100])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v3_pre_topc(X1,X0) | sP0(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((sP0(X0,X2) | ~v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) | ~sP0(X0,X2))) | ~sP1(X0,X1,X2))),
% 0.22/0.56    inference(rectify,[],[f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ! [X0,X2,X1] : (((sP0(X0,X1) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~sP0(X0,X1))) | ~sP1(X0,X2,X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ! [X0,X2,X1] : ((sP0(X0,X1) <=> v3_pre_topc(X2,X0)) | ~sP1(X0,X2,X1))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.56  fof(f671,plain,(
% 0.22/0.56    sP1(sK5,k2_struct_0(sK5),sK5) | ~spl10_64),
% 0.22/0.56    inference(avatar_component_clause,[],[f669])).
% 0.22/0.56  fof(f923,plain,(
% 0.22/0.56    spl10_89 | ~spl10_40 | ~spl10_41 | ~spl10_84),
% 0.22/0.56    inference(avatar_split_clause,[],[f879,f848,f388,f333,f895])).
% 0.22/0.56  fof(f333,plain,(
% 0.22/0.56    spl10_40 <=> l1_pre_topc(sK6)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).
% 0.22/0.56  fof(f879,plain,(
% 0.22/0.56    r1_tarski(k2_struct_0(sK5),k2_struct_0(sK6)) | (~spl10_40 | ~spl10_41 | ~spl10_84)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f334,f850,f557])).
% 0.22/0.56  fof(f557,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k2_struct_0(sK5),k2_struct_0(X0)) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0)) ) | ~spl10_41),
% 0.22/0.56    inference(subsumption_resolution,[],[f550,f84])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.56  fof(f550,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k2_struct_0(sK5),k2_struct_0(X0)) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~l1_struct_0(X0)) ) | ~spl10_41),
% 0.22/0.56    inference(superposition,[],[f486,f83])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.56  fof(f486,plain,(
% 0.22/0.56    ( ! [X4] : (r1_tarski(k2_struct_0(sK5),u1_struct_0(X4)) | ~m1_pre_topc(sK5,X4) | ~l1_pre_topc(X4)) ) | ~spl10_41),
% 0.22/0.56    inference(superposition,[],[f89,f390])).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.22/0.56  fof(f334,plain,(
% 0.22/0.56    l1_pre_topc(sK6) | ~spl10_40),
% 0.22/0.56    inference(avatar_component_clause,[],[f333])).
% 0.22/0.56  fof(f851,plain,(
% 0.22/0.56    spl10_84 | ~spl10_31 | ~spl10_39 | ~spl10_41 | ~spl10_43),
% 0.22/0.56    inference(avatar_split_clause,[],[f846,f406,f388,f325,f280,f848])).
% 0.22/0.56  fof(f846,plain,(
% 0.22/0.56    m1_pre_topc(sK5,sK6) | (~spl10_31 | ~spl10_39 | ~spl10_41 | ~spl10_43)),
% 0.22/0.56    inference(forward_demodulation,[],[f845,f282])).
% 0.22/0.56  fof(f845,plain,(
% 0.22/0.56    m1_pre_topc(sK5,g1_pre_topc(k2_struct_0(sK5),u1_pre_topc(sK5))) | (~spl10_39 | ~spl10_41 | ~spl10_43)),
% 0.22/0.56    inference(forward_demodulation,[],[f830,f390])).
% 0.22/0.56  fof(f830,plain,(
% 0.22/0.56    m1_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | (~spl10_39 | ~spl10_43)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f326,f326,f408,f86])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.56  fof(f672,plain,(
% 0.22/0.56    spl10_64 | ~spl10_39 | ~spl10_41 | ~spl10_43 | ~spl10_47),
% 0.22/0.56    inference(avatar_split_clause,[],[f667,f446,f406,f388,f325,f669])).
% 0.22/0.56  fof(f667,plain,(
% 0.22/0.56    sP1(sK5,k2_struct_0(sK5),sK5) | (~spl10_39 | ~spl10_41 | ~spl10_43 | ~spl10_47)),
% 0.22/0.56    inference(forward_demodulation,[],[f652,f390])).
% 0.22/0.56  fof(f652,plain,(
% 0.22/0.56    sP1(sK5,u1_struct_0(sK5),sK5) | (~spl10_39 | ~spl10_43 | ~spl10_47)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f448,f326,f408,f207])).
% 0.22/0.56  fof(f207,plain,(
% 0.22/0.56    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f111,f90])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f104])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(definition_folding,[],[f40,f44,f43])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.22/0.56  fof(f467,plain,(
% 0.22/0.56    spl10_49 | ~spl10_39 | ~spl10_47),
% 0.22/0.56    inference(avatar_split_clause,[],[f462,f446,f325,f464])).
% 0.22/0.56  fof(f462,plain,(
% 0.22/0.56    v3_pre_topc(k2_struct_0(sK5),sK5) | (~spl10_39 | ~spl10_47)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f326,f448,f96])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.22/0.56  fof(f460,plain,(
% 0.22/0.56    spl10_47 | ~spl10_12 | ~spl10_17 | ~spl10_18),
% 0.22/0.56    inference(avatar_split_clause,[],[f459,f198,f193,f168,f446])).
% 0.22/0.56  fof(f459,plain,(
% 0.22/0.56    v2_pre_topc(sK5) | (~spl10_12 | ~spl10_17 | ~spl10_18)),
% 0.22/0.56    inference(subsumption_resolution,[],[f458,f200])).
% 0.22/0.56  fof(f458,plain,(
% 0.22/0.56    v2_pre_topc(sK5) | ~v2_pre_topc(sK3) | (~spl10_12 | ~spl10_17)),
% 0.22/0.56    inference(subsumption_resolution,[],[f439,f195])).
% 0.22/0.56  fof(f439,plain,(
% 0.22/0.56    v2_pre_topc(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~spl10_12),
% 0.22/0.56    inference(resolution,[],[f97,f170])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.56  fof(f409,plain,(
% 0.22/0.56    spl10_43 | ~spl10_39),
% 0.22/0.56    inference(avatar_split_clause,[],[f403,f325,f406])).
% 0.22/0.56  fof(f403,plain,(
% 0.22/0.56    m1_pre_topc(sK5,sK5) | ~spl10_39),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f326,f85])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.56  fof(f399,plain,(
% 0.22/0.56    spl10_42 | ~spl10_33),
% 0.22/0.56    inference(avatar_split_clause,[],[f394,f290,f396])).
% 0.22/0.56  fof(f290,plain,(
% 0.22/0.56    spl10_33 <=> l1_struct_0(sK6)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 0.22/0.56  fof(f394,plain,(
% 0.22/0.56    u1_struct_0(sK6) = k2_struct_0(sK6) | ~spl10_33),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f291,f83])).
% 0.22/0.56  fof(f291,plain,(
% 0.22/0.56    l1_struct_0(sK6) | ~spl10_33),
% 0.22/0.56    inference(avatar_component_clause,[],[f290])).
% 0.22/0.56  fof(f391,plain,(
% 0.22/0.56    spl10_41 | ~spl10_30),
% 0.22/0.56    inference(avatar_split_clause,[],[f386,f276,f388])).
% 0.22/0.56  fof(f276,plain,(
% 0.22/0.56    spl10_30 <=> l1_struct_0(sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 0.22/0.56  fof(f386,plain,(
% 0.22/0.56    u1_struct_0(sK5) = k2_struct_0(sK5) | ~spl10_30),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f277,f83])).
% 0.22/0.56  fof(f277,plain,(
% 0.22/0.56    l1_struct_0(sK5) | ~spl10_30),
% 0.22/0.56    inference(avatar_component_clause,[],[f276])).
% 0.22/0.56  fof(f383,plain,(
% 0.22/0.56    spl10_40 | ~spl10_10 | ~spl10_17),
% 0.22/0.56    inference(avatar_split_clause,[],[f342,f193,f158,f333])).
% 0.22/0.56  fof(f342,plain,(
% 0.22/0.56    l1_pre_topc(sK6) | (~spl10_10 | ~spl10_17)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f195,f160,f88])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.56  fof(f380,plain,(
% 0.22/0.56    spl10_39 | ~spl10_12 | ~spl10_17),
% 0.22/0.56    inference(avatar_split_clause,[],[f345,f193,f168,f325])).
% 0.22/0.56  fof(f345,plain,(
% 0.22/0.56    l1_pre_topc(sK5) | (~spl10_12 | ~spl10_17)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f195,f170,f88])).
% 0.22/0.56  fof(f377,plain,(
% 0.22/0.56    u1_struct_0(sK4) != k2_struct_0(sK4) | v1_funct_2(sK7,k2_struct_0(sK6),k2_struct_0(sK4)) | ~v1_funct_2(sK7,k2_struct_0(sK6),u1_struct_0(sK4))),
% 0.22/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.56  fof(f376,plain,(
% 0.22/0.56    u1_struct_0(sK4) != k2_struct_0(sK4) | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),k2_struct_0(sK4)))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),u1_struct_0(sK4))))),
% 0.22/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.56  fof(f337,plain,(
% 0.22/0.56    ~spl10_40 | spl10_33),
% 0.22/0.56    inference(avatar_split_clause,[],[f331,f290,f333])).
% 0.22/0.56  fof(f331,plain,(
% 0.22/0.56    ~l1_pre_topc(sK6) | spl10_33),
% 0.22/0.56    inference(resolution,[],[f292,f84])).
% 0.22/0.56  fof(f292,plain,(
% 0.22/0.56    ~l1_struct_0(sK6) | spl10_33),
% 0.22/0.56    inference(avatar_component_clause,[],[f290])).
% 0.22/0.56  fof(f329,plain,(
% 0.22/0.56    ~spl10_39 | spl10_30),
% 0.22/0.56    inference(avatar_split_clause,[],[f323,f276,f325])).
% 0.22/0.56  fof(f323,plain,(
% 0.22/0.56    ~l1_pre_topc(sK5) | spl10_30),
% 0.22/0.56    inference(resolution,[],[f278,f84])).
% 0.22/0.56  fof(f278,plain,(
% 0.22/0.56    ~l1_struct_0(sK5) | spl10_30),
% 0.22/0.56    inference(avatar_component_clause,[],[f276])).
% 0.22/0.56  fof(f307,plain,(
% 0.22/0.56    ~spl10_33 | spl10_36 | ~spl10_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f252,f133,f304,f290])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    spl10_5 <=> m1_subset_1(sK8,u1_struct_0(sK6))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.22/0.56  fof(f252,plain,(
% 0.22/0.56    m1_subset_1(sK8,k2_struct_0(sK6)) | ~l1_struct_0(sK6) | ~spl10_5),
% 0.22/0.56    inference(superposition,[],[f135,f83])).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    m1_subset_1(sK8,u1_struct_0(sK6)) | ~spl10_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f133])).
% 0.22/0.56  fof(f302,plain,(
% 0.22/0.56    ~spl10_33 | spl10_35 | ~spl10_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f251,f148,f299,f290])).
% 0.22/0.56  fof(f299,plain,(
% 0.22/0.56    spl10_35 <=> v1_funct_2(sK7,k2_struct_0(sK6),u1_struct_0(sK4))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).
% 0.22/0.56  fof(f148,plain,(
% 0.22/0.56    spl10_8 <=> v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.22/0.56  fof(f251,plain,(
% 0.22/0.56    v1_funct_2(sK7,k2_struct_0(sK6),u1_struct_0(sK4)) | ~l1_struct_0(sK6) | ~spl10_8),
% 0.22/0.56    inference(superposition,[],[f150,f83])).
% 0.22/0.56  fof(f150,plain,(
% 0.22/0.56    v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) | ~spl10_8),
% 0.22/0.56    inference(avatar_component_clause,[],[f148])).
% 0.22/0.56  fof(f297,plain,(
% 0.22/0.56    ~spl10_33 | spl10_34 | ~spl10_7),
% 0.22/0.56    inference(avatar_split_clause,[],[f250,f143,f294,f290])).
% 0.22/0.56  fof(f294,plain,(
% 0.22/0.56    spl10_34 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),u1_struct_0(sK4))))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 0.22/0.56  fof(f143,plain,(
% 0.22/0.56    spl10_7 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.56  fof(f250,plain,(
% 0.22/0.56    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK6),u1_struct_0(sK4)))) | ~l1_struct_0(sK6) | ~spl10_7),
% 0.22/0.56    inference(superposition,[],[f145,f83])).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) | ~spl10_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f143])).
% 0.22/0.56  fof(f288,plain,(
% 0.22/0.56    ~spl10_30 | spl10_32 | ~spl10_20),
% 0.22/0.56    inference(avatar_split_clause,[],[f249,f210,f285,f276])).
% 0.22/0.56  fof(f210,plain,(
% 0.22/0.56    spl10_20 <=> m1_subset_1(sK8,u1_struct_0(sK5))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.22/0.56  fof(f249,plain,(
% 0.22/0.56    m1_subset_1(sK8,k2_struct_0(sK5)) | ~l1_struct_0(sK5) | ~spl10_20),
% 0.22/0.56    inference(superposition,[],[f212,f83])).
% 0.22/0.56  fof(f212,plain,(
% 0.22/0.56    m1_subset_1(sK8,u1_struct_0(sK5)) | ~spl10_20),
% 0.22/0.56    inference(avatar_component_clause,[],[f210])).
% 0.22/0.56  fof(f283,plain,(
% 0.22/0.56    ~spl10_30 | spl10_31 | ~spl10_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f248,f138,f280,f276])).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    spl10_6 <=> g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.56  fof(f248,plain,(
% 0.22/0.56    sK6 = g1_pre_topc(k2_struct_0(sK5),u1_pre_topc(sK5)) | ~l1_struct_0(sK5) | ~spl10_6),
% 0.22/0.56    inference(superposition,[],[f140,f83])).
% 0.22/0.56  fof(f140,plain,(
% 0.22/0.56    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 | ~spl10_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f138])).
% 0.22/0.56  fof(f257,plain,(
% 0.22/0.56    spl10_26 | ~spl10_23),
% 0.22/0.56    inference(avatar_split_clause,[],[f245,f228,f254])).
% 0.22/0.56  fof(f228,plain,(
% 0.22/0.56    spl10_23 <=> l1_struct_0(sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 0.22/0.56  fof(f245,plain,(
% 0.22/0.56    u1_struct_0(sK4) = k2_struct_0(sK4) | ~spl10_23),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f230,f83])).
% 0.22/0.56  fof(f230,plain,(
% 0.22/0.56    l1_struct_0(sK4) | ~spl10_23),
% 0.22/0.56    inference(avatar_component_clause,[],[f228])).
% 0.22/0.56  fof(f231,plain,(
% 0.22/0.56    spl10_23 | ~spl10_14),
% 0.22/0.56    inference(avatar_split_clause,[],[f220,f178,f228])).
% 0.22/0.56  fof(f220,plain,(
% 0.22/0.56    l1_struct_0(sK4) | ~spl10_14),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f180,f84])).
% 0.22/0.56  fof(f219,plain,(
% 0.22/0.56    spl10_21 | ~spl10_2 | ~spl10_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f214,f123,f118,f216])).
% 0.22/0.56  fof(f118,plain,(
% 0.22/0.56    spl10_2 <=> r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    spl10_3 <=> sK8 = sK9),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.56  fof(f214,plain,(
% 0.22/0.56    r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK8) | (~spl10_2 | ~spl10_3)),
% 0.22/0.56    inference(forward_demodulation,[],[f120,f125])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    sK8 = sK9 | ~spl10_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f123])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9) | ~spl10_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f118])).
% 0.22/0.56  fof(f213,plain,(
% 0.22/0.56    spl10_20 | ~spl10_3 | ~spl10_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f208,f128,f123,f210])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    spl10_4 <=> m1_subset_1(sK9,u1_struct_0(sK5))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.56  fof(f208,plain,(
% 0.22/0.56    m1_subset_1(sK8,u1_struct_0(sK5)) | (~spl10_3 | ~spl10_4)),
% 0.22/0.56    inference(backward_demodulation,[],[f130,f125])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    m1_subset_1(sK9,u1_struct_0(sK5)) | ~spl10_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f128])).
% 0.22/0.56  fof(f206,plain,(
% 0.22/0.56    ~spl10_19),
% 0.22/0.56    inference(avatar_split_clause,[],[f64,f203])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ~v2_struct_0(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ((((((~r1_tmap_1(sK6,sK4,sK7,sK8) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9) & sK8 = sK9 & m1_subset_1(sK9,u1_struct_0(sK5))) & m1_subset_1(sK8,u1_struct_0(sK6))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) & v1_funct_1(sK7)) & m1_pre_topc(sK6,sK3) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f19,f54,f53,f52,f51,f50,f49,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK3,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK3,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK4,X4,X5) & r1_tmap_1(X2,sK4,k3_tmap_1(sK3,sK4,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK4,X4,X5) & r1_tmap_1(X2,sK4,k3_tmap_1(sK3,sK4,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK4,X4,X5) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,X3,sK5,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK4,X4,X5) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,X3,sK5,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK6,sK4,X4,X5) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK6))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK4)) & v1_funct_1(X4)) & m1_pre_topc(sK6,sK3) & ~v2_struct_0(sK6))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK6,sK4,X4,X5) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK6))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK4)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK6,sK4,sK7,X5) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK6))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) & v1_funct_1(sK7))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f53,plain,(
% 0.22/0.58    ? [X5] : (? [X6] : (~r1_tmap_1(sK6,sK4,sK7,X5) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK6))) => (? [X6] : (~r1_tmap_1(sK6,sK4,sK7,sK8) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6) & sK8 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(sK8,u1_struct_0(sK6)))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ? [X6] : (~r1_tmap_1(sK6,sK4,sK7,sK8) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6) & sK8 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) => (~r1_tmap_1(sK6,sK4,sK7,sK8) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9) & sK8 = sK9 & m1_subset_1(sK9,u1_struct_0(sK5)))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f18])).
% 1.74/0.58  fof(f18,plain,(
% 1.74/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.74/0.58    inference(ennf_transformation,[],[f17])).
% 1.74/0.58  fof(f17,negated_conjecture,(
% 1.74/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.74/0.58    inference(negated_conjecture,[],[f16])).
% 1.74/0.58  fof(f16,conjecture,(
% 1.74/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.74/0.58  fof(f201,plain,(
% 1.74/0.58    spl10_18),
% 1.74/0.58    inference(avatar_split_clause,[],[f65,f198])).
% 1.74/0.58  fof(f65,plain,(
% 1.74/0.58    v2_pre_topc(sK3)),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f196,plain,(
% 1.74/0.58    spl10_17),
% 1.74/0.58    inference(avatar_split_clause,[],[f66,f193])).
% 1.74/0.58  fof(f66,plain,(
% 1.74/0.58    l1_pre_topc(sK3)),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f191,plain,(
% 1.74/0.58    ~spl10_16),
% 1.74/0.58    inference(avatar_split_clause,[],[f67,f188])).
% 1.74/0.58  fof(f67,plain,(
% 1.74/0.58    ~v2_struct_0(sK4)),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f186,plain,(
% 1.74/0.58    spl10_15),
% 1.74/0.58    inference(avatar_split_clause,[],[f68,f183])).
% 1.74/0.58  fof(f68,plain,(
% 1.74/0.58    v2_pre_topc(sK4)),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f181,plain,(
% 1.74/0.58    spl10_14),
% 1.74/0.58    inference(avatar_split_clause,[],[f69,f178])).
% 1.74/0.58  fof(f69,plain,(
% 1.74/0.58    l1_pre_topc(sK4)),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f176,plain,(
% 1.74/0.58    ~spl10_13),
% 1.74/0.58    inference(avatar_split_clause,[],[f70,f173])).
% 1.74/0.58  fof(f70,plain,(
% 1.74/0.58    ~v2_struct_0(sK5)),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f171,plain,(
% 1.74/0.58    spl10_12),
% 1.74/0.58    inference(avatar_split_clause,[],[f71,f168])).
% 1.74/0.58  fof(f71,plain,(
% 1.74/0.58    m1_pre_topc(sK5,sK3)),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f166,plain,(
% 1.74/0.58    ~spl10_11),
% 1.74/0.58    inference(avatar_split_clause,[],[f72,f163])).
% 1.74/0.58  fof(f72,plain,(
% 1.74/0.58    ~v2_struct_0(sK6)),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f161,plain,(
% 1.74/0.58    spl10_10),
% 1.74/0.58    inference(avatar_split_clause,[],[f73,f158])).
% 1.74/0.58  fof(f73,plain,(
% 1.74/0.58    m1_pre_topc(sK6,sK3)),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f156,plain,(
% 1.74/0.58    spl10_9),
% 1.74/0.58    inference(avatar_split_clause,[],[f74,f153])).
% 1.74/0.58  fof(f74,plain,(
% 1.74/0.58    v1_funct_1(sK7)),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f151,plain,(
% 1.74/0.58    spl10_8),
% 1.74/0.58    inference(avatar_split_clause,[],[f75,f148])).
% 1.74/0.58  fof(f75,plain,(
% 1.74/0.58    v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f146,plain,(
% 1.74/0.58    spl10_7),
% 1.74/0.58    inference(avatar_split_clause,[],[f76,f143])).
% 1.74/0.58  fof(f76,plain,(
% 1.74/0.58    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f141,plain,(
% 1.74/0.58    spl10_6),
% 1.74/0.58    inference(avatar_split_clause,[],[f77,f138])).
% 1.74/0.58  fof(f77,plain,(
% 1.74/0.58    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f136,plain,(
% 1.74/0.58    spl10_5),
% 1.74/0.58    inference(avatar_split_clause,[],[f78,f133])).
% 1.74/0.58  fof(f78,plain,(
% 1.74/0.58    m1_subset_1(sK8,u1_struct_0(sK6))),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f131,plain,(
% 1.74/0.58    spl10_4),
% 1.74/0.58    inference(avatar_split_clause,[],[f79,f128])).
% 1.74/0.58  fof(f79,plain,(
% 1.74/0.58    m1_subset_1(sK9,u1_struct_0(sK5))),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f126,plain,(
% 1.74/0.58    spl10_3),
% 1.74/0.58    inference(avatar_split_clause,[],[f80,f123])).
% 1.74/0.58  fof(f80,plain,(
% 1.74/0.58    sK8 = sK9),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f121,plain,(
% 1.74/0.58    spl10_2),
% 1.74/0.58    inference(avatar_split_clause,[],[f81,f118])).
% 1.74/0.58  fof(f81,plain,(
% 1.74/0.58    r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9)),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  fof(f116,plain,(
% 1.74/0.58    ~spl10_1),
% 1.74/0.58    inference(avatar_split_clause,[],[f82,f113])).
% 1.74/0.58  fof(f82,plain,(
% 1.74/0.58    ~r1_tmap_1(sK6,sK4,sK7,sK8)),
% 1.74/0.58    inference(cnf_transformation,[],[f55])).
% 1.74/0.58  % SZS output end Proof for theBenchmark
% 1.74/0.58  % (28224)------------------------------
% 1.74/0.58  % (28224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.58  % (28224)Termination reason: Refutation
% 1.74/0.58  
% 1.74/0.58  % (28224)Memory used [KB]: 11897
% 1.74/0.58  % (28224)Time elapsed: 0.150 s
% 1.74/0.58  % (28224)------------------------------
% 1.74/0.58  % (28224)------------------------------
% 1.74/0.58  % (28207)Success in time 0.218 s
%------------------------------------------------------------------------------

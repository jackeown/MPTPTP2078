%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1829+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:40 EST 2020

% Result     : Theorem 2.75s
% Output     : Refutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  396 (1128 expanded)
%              Number of leaves         :   56 ( 503 expanded)
%              Depth                    :   35
%              Number of atoms          : 4744 (13291 expanded)
%              Number of equality atoms :   44 (  69 expanded)
%              Maximal formula depth    :   30 (  12 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1697,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f178,f183,f188,f193,f198,f243,f253,f297,f481,f529,f548,f552,f556,f571,f581,f699,f720,f810,f880,f1123,f1409,f1429,f1449,f1459,f1522,f1596,f1612,f1628,f1667])).

fof(f1667,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_123
    | ~ spl6_133 ),
    inference(avatar_contradiction_clause,[],[f1666])).

fof(f1666,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_123
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1665,f142])).

fof(f142,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl6_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f1665,plain,
    ( ~ v1_funct_1(sK4)
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
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_123
    | ~ spl6_133 ),
    inference(forward_demodulation,[],[f1664,f1408])).

fof(f1408,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_123 ),
    inference(avatar_component_clause,[],[f1406])).

fof(f1406,plain,
    ( spl6_123
  <=> sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).

fof(f1664,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_123
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1663,f182])).

fof(f182,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl6_17
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f1663,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_123
    | ~ spl6_133 ),
    inference(forward_demodulation,[],[f1662,f1408])).

fof(f1662,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_123
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1661,f167])).

fof(f167,plain,
    ( v5_pre_topc(sK4,sK2,sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_14
  <=> v5_pre_topc(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f1661,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_123
    | ~ spl6_133 ),
    inference(forward_demodulation,[],[f1660,f1408])).

fof(f1660,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_123
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1659,f192])).

fof(f192,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl6_19
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f1659,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_123
    | ~ spl6_133 ),
    inference(forward_demodulation,[],[f1658,f1408])).

fof(f1658,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1657,f102])).

fof(f102,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1657,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1656,f107])).

fof(f107,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1656,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1655,f112])).

fof(f112,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1655,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1654,f117])).

fof(f117,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1654,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1653,f122])).

fof(f122,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1653,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1652,f127])).

fof(f127,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1652,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1651,f132])).

fof(f132,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1651,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1650,f152])).

fof(f152,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_11
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f1650,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1649,f137])).

fof(f137,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_8
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1649,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1648,f157])).

fof(f157,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_12
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f1648,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1647,f177])).

fof(f177,plain,
    ( r4_tsep_1(sK0,sK2,sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl6_16
  <=> r4_tsep_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f1647,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1646,f229])).

fof(f229,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl6_25
  <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f1646,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_26
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1645,f233])).

fof(f233,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl6_26
  <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f1645,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_20
    | spl6_27
    | ~ spl6_28
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1644,f241])).

fof(f241,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl6_28
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f1644,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_20
    | spl6_27
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1643,f238])).

fof(f238,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl6_27
  <=> v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1643,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1642,f187])).

fof(f187,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_18
  <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f1642,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_20
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1641,f172])).

fof(f172,plain,
    ( v5_pre_topc(sK5,sK3,sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl6_15
  <=> v5_pre_topc(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1641,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1640,f197])).

fof(f197,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_20
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f1640,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1633,f147])).

fof(f147,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_10
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f1633,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_133 ),
    inference(superposition,[],[f66,f1595])).

fof(f1595,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_133 ),
    inference(avatar_component_clause,[],[f1593])).

fof(f1593,plain,
    ( spl6_133
  <=> sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_133])])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
      | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
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
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(X4) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(X4) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).

fof(f1628,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_132 ),
    inference(avatar_contradiction_clause,[],[f1627])).

fof(f1627,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_132 ),
    inference(subsumption_resolution,[],[f1626,f102])).

fof(f1626,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_132 ),
    inference(subsumption_resolution,[],[f1625,f107])).

fof(f1625,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_132 ),
    inference(subsumption_resolution,[],[f1624,f112])).

fof(f1624,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_132 ),
    inference(subsumption_resolution,[],[f1623,f117])).

fof(f1623,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_132 ),
    inference(subsumption_resolution,[],[f1622,f122])).

fof(f1622,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_132 ),
    inference(subsumption_resolution,[],[f1621,f127])).

fof(f1621,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_132 ),
    inference(subsumption_resolution,[],[f1620,f1427])).

fof(f1427,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl6_125 ),
    inference(avatar_component_clause,[],[f1426])).

fof(f1426,plain,
    ( spl6_125
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).

fof(f1620,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_132 ),
    inference(subsumption_resolution,[],[f1619,f157])).

fof(f1619,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_132 ),
    inference(subsumption_resolution,[],[f1618,f229])).

fof(f1618,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_26
    | ~ spl6_28
    | spl6_132 ),
    inference(subsumption_resolution,[],[f1617,f233])).

fof(f1617,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28
    | spl6_132 ),
    inference(subsumption_resolution,[],[f1615,f241])).

fof(f1615,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_132 ),
    inference(resolution,[],[f1591,f81])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f1591,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl6_132 ),
    inference(avatar_component_clause,[],[f1589])).

fof(f1589,plain,
    ( spl6_132
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_132])])).

fof(f1612,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_131 ),
    inference(avatar_contradiction_clause,[],[f1611])).

fof(f1611,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_131 ),
    inference(subsumption_resolution,[],[f1610,f102])).

fof(f1610,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_131 ),
    inference(subsumption_resolution,[],[f1609,f107])).

fof(f1609,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_131 ),
    inference(subsumption_resolution,[],[f1608,f112])).

fof(f1608,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_131 ),
    inference(subsumption_resolution,[],[f1607,f117])).

fof(f1607,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_131 ),
    inference(subsumption_resolution,[],[f1606,f122])).

fof(f1606,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_131 ),
    inference(subsumption_resolution,[],[f1605,f127])).

fof(f1605,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_125
    | spl6_131 ),
    inference(subsumption_resolution,[],[f1604,f1427])).

fof(f1604,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_12
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_131 ),
    inference(subsumption_resolution,[],[f1603,f157])).

fof(f1603,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_131 ),
    inference(subsumption_resolution,[],[f1602,f229])).

fof(f1602,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_26
    | ~ spl6_28
    | spl6_131 ),
    inference(subsumption_resolution,[],[f1601,f233])).

fof(f1601,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28
    | spl6_131 ),
    inference(subsumption_resolution,[],[f1599,f241])).

fof(f1599,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_131 ),
    inference(resolution,[],[f1587,f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f1587,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl6_131 ),
    inference(avatar_component_clause,[],[f1585])).

fof(f1585,plain,
    ( spl6_131
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).

fof(f1596,plain,
    ( ~ spl6_131
    | ~ spl6_132
    | spl6_133
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_52
    | ~ spl6_94 ),
    inference(avatar_split_clause,[],[f1134,f1121,f578,f195,f190,f185,f180,f145,f140,f1593,f1589,f1585])).

fof(f578,plain,
    ( spl6_52
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f1121,plain,
    ( spl6_94
  <=> ! [X7,X6] :
        ( ~ v1_funct_1(X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)) = X6
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f1134,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_52
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f1133,f147])).

fof(f1133,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_52
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f1132,f197])).

fof(f1132,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_52
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f1131,f187])).

fof(f1131,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_52
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f1130,f142])).

fof(f1130,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_52
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f1129,f182])).

fof(f1129,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ spl6_19
    | ~ spl6_52
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f1128,f192])).

fof(f1128,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ spl6_52
    | ~ spl6_94 ),
    inference(resolution,[],[f1122,f580])).

fof(f580,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f578])).

fof(f1122,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)) = X6
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X6) )
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f1121])).

fof(f1522,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_122
    | ~ spl6_125 ),
    inference(avatar_contradiction_clause,[],[f1521])).

fof(f1521,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_122
    | ~ spl6_125 ),
    inference(subsumption_resolution,[],[f1520,f102])).

fof(f1520,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_122
    | ~ spl6_125 ),
    inference(subsumption_resolution,[],[f1519,f107])).

fof(f1519,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_122
    | ~ spl6_125 ),
    inference(subsumption_resolution,[],[f1518,f112])).

fof(f1518,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_122
    | ~ spl6_125 ),
    inference(subsumption_resolution,[],[f1517,f117])).

fof(f1517,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_122
    | ~ spl6_125 ),
    inference(subsumption_resolution,[],[f1516,f122])).

fof(f1516,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_122
    | ~ spl6_125 ),
    inference(subsumption_resolution,[],[f1515,f127])).

fof(f1515,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_122
    | ~ spl6_125 ),
    inference(subsumption_resolution,[],[f1514,f1427])).

fof(f1514,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_122 ),
    inference(subsumption_resolution,[],[f1513,f152])).

fof(f1513,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28
    | spl6_122 ),
    inference(subsumption_resolution,[],[f1512,f229])).

fof(f1512,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_26
    | ~ spl6_28
    | spl6_122 ),
    inference(subsumption_resolution,[],[f1511,f233])).

fof(f1511,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28
    | spl6_122 ),
    inference(subsumption_resolution,[],[f1508,f241])).

fof(f1508,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_122 ),
    inference(resolution,[],[f1404,f81])).

fof(f1404,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl6_122 ),
    inference(avatar_component_clause,[],[f1402])).

fof(f1402,plain,
    ( spl6_122
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).

fof(f1459,plain,
    ( spl6_1
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | spl6_125 ),
    inference(avatar_contradiction_clause,[],[f1458])).

fof(f1458,plain,
    ( $false
    | spl6_1
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | spl6_125 ),
    inference(subsumption_resolution,[],[f1457,f102])).

fof(f1457,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | spl6_125 ),
    inference(subsumption_resolution,[],[f1456,f112])).

fof(f1456,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | spl6_125 ),
    inference(subsumption_resolution,[],[f1455,f132])).

fof(f1455,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | spl6_125 ),
    inference(subsumption_resolution,[],[f1454,f152])).

fof(f1454,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_12
    | spl6_125 ),
    inference(subsumption_resolution,[],[f1453,f137])).

fof(f1453,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_12
    | spl6_125 ),
    inference(subsumption_resolution,[],[f1451,f157])).

fof(f1451,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_125 ),
    inference(resolution,[],[f1428,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f1428,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | spl6_125 ),
    inference(avatar_component_clause,[],[f1426])).

fof(f1449,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(avatar_contradiction_clause,[],[f1448])).

fof(f1448,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1447,f102])).

fof(f1447,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1446,f107])).

fof(f1446,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1445,f112])).

fof(f1445,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1444,f117])).

fof(f1444,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1443,f122])).

fof(f1443,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1442,f127])).

fof(f1442,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1441,f132])).

fof(f1441,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1440,f152])).

fof(f1440,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1439,f137])).

fof(f1439,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1438,f157])).

fof(f1438,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1437,f142])).

fof(f1437,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1436,f182])).

fof(f1436,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1435,f192])).

fof(f1435,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1434,f147])).

fof(f1434,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_18
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1433,f187])).

fof(f1433,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_20
    | spl6_28 ),
    inference(subsumption_resolution,[],[f1431,f197])).

fof(f1431,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_28 ),
    inference(resolution,[],[f242,f84])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f242,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f240])).

fof(f1429,plain,
    ( ~ spl6_125
    | ~ spl6_28
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | spl6_121 ),
    inference(avatar_split_clause,[],[f1420,f1398,f232,f228,f150,f125,f120,f115,f110,f105,f100,f240,f1426])).

fof(f1398,plain,
    ( spl6_121
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f1420,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | spl6_121 ),
    inference(subsumption_resolution,[],[f1419,f102])).

fof(f1419,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | spl6_121 ),
    inference(subsumption_resolution,[],[f1418,f107])).

fof(f1418,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | spl6_121 ),
    inference(subsumption_resolution,[],[f1417,f112])).

fof(f1417,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | spl6_121 ),
    inference(subsumption_resolution,[],[f1416,f117])).

fof(f1416,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | spl6_121 ),
    inference(subsumption_resolution,[],[f1415,f122])).

fof(f1415,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | spl6_121 ),
    inference(subsumption_resolution,[],[f1414,f127])).

fof(f1414,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_11
    | ~ spl6_25
    | ~ spl6_26
    | spl6_121 ),
    inference(subsumption_resolution,[],[f1413,f152])).

fof(f1413,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_25
    | ~ spl6_26
    | spl6_121 ),
    inference(subsumption_resolution,[],[f1412,f229])).

fof(f1412,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_26
    | spl6_121 ),
    inference(subsumption_resolution,[],[f1410,f233])).

fof(f1410,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_121 ),
    inference(resolution,[],[f1400,f80])).

fof(f1400,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_121 ),
    inference(avatar_component_clause,[],[f1398])).

fof(f1409,plain,
    ( ~ spl6_121
    | ~ spl6_122
    | spl6_123
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_51
    | ~ spl6_73 ),
    inference(avatar_split_clause,[],[f894,f878,f568,f195,f190,f185,f180,f145,f140,f125,f120,f115,f1406,f1402,f1398])).

fof(f568,plain,
    ( spl6_51
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f878,plain,
    ( spl6_73
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)) = X2
        | ~ m1_subset_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f894,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_51
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f893,f187])).

fof(f893,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_51
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f892,f117])).

fof(f892,plain,
    ( v2_struct_0(sK1)
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_51
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f891,f122])).

fof(f891,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_51
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f890,f127])).

fof(f890,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_51
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f889,f197])).

fof(f889,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_51
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f888,f142])).

fof(f888,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_51
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f887,f182])).

fof(f887,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_51
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f886,f192])).

fof(f886,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_10
    | ~ spl6_51
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f885,f147])).

fof(f885,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_51
    | ~ spl6_73 ),
    inference(resolution,[],[f879,f570])).

fof(f570,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f568])).

fof(f879,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)) = X2
        | ~ m1_subset_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) )
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f878])).

fof(f1123,plain,
    ( spl6_94
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f850,f808,f1121])).

fof(f808,plain,
    ( spl6_71
  <=> ! [X3,X2] :
        ( ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X3,X2)),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f850,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_1(X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)) = X6
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6))) )
    | ~ spl6_71 ),
    inference(duplicate_literal_removal,[],[f849])).

fof(f849,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_1(X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)) = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6)),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X7,X6))) )
    | ~ spl6_71 ),
    inference(resolution,[],[f809,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f809,plain,
    ( ! [X2,X3] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X3,X2)),X2)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) )
    | ~ spl6_71 ),
    inference(avatar_component_clause,[],[f808])).

fof(f880,plain,
    ( spl6_73
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f736,f718,f878])).

fof(f718,plain,
    ( spl6_63
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f736,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)) = X2
        | ~ m1_subset_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0))) )
    | ~ spl6_63 ),
    inference(duplicate_literal_removal,[],[f735])).

fof(f735,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0))) )
    | ~ spl6_63 ),
    inference(resolution,[],[f719,f77])).

fof(f719,plain,
    ( ! [X2,X0,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f718])).

fof(f810,plain,
    ( spl6_71
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f731,f697,f125,f120,f115,f808])).

fof(f697,plain,
    ( spl6_62
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f731,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X3,X2)),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f730,f117])).

fof(f730,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X3,X2)),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f727,f122])).

fof(f727,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X3,X2)),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl6_6
    | ~ spl6_62 ),
    inference(resolution,[],[f698,f127])).

fof(f698,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f697])).

fof(f720,plain,
    ( spl6_63
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f576,f554,f155,f150,f110,f105,f100,f718])).

fof(f554,plain,
    ( spl6_50
  <=> ! [X1,X3,X0,X2] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK2,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f576,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f575,f102])).

fof(f575,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f574,f107])).

fof(f574,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f573,f112])).

fof(f573,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f572,f152])).

fof(f572,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_50 ),
    inference(resolution,[],[f555,f157])).

fof(f555,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK2,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X2)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f554])).

fof(f699,plain,
    ( spl6_62
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f566,f546,f155,f150,f110,f105,f100,f697])).

fof(f546,plain,
    ( spl6_48
  <=> ! [X1,X3,X0,X2] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK3,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f566,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f565,f102])).

fof(f565,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f564,f107])).

fof(f564,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f563,f112])).

fof(f563,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f562,f152])).

fof(f562,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)),X0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_48 ),
    inference(resolution,[],[f547,f157])).

fof(f547,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK3,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f546])).

fof(f581,plain,
    ( spl6_52
    | ~ spl6_12
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f558,f550,f155,f578])).

fof(f550,plain,
    ( spl6_49
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f558,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_12
    | ~ spl6_49 ),
    inference(resolution,[],[f551,f157])).

fof(f551,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f550])).

fof(f571,plain,
    ( spl6_51
    | ~ spl6_11
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f557,f550,f150,f568])).

fof(f557,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_11
    | ~ spl6_49 ),
    inference(resolution,[],[f551,f152])).

fof(f556,plain,
    ( spl6_50
    | spl6_7
    | spl6_8
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f355,f160,f135,f130,f554])).

fof(f160,plain,
    ( spl6_13
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f355,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK2,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_7
    | spl6_8
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f354,f132])).

fof(f354,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK2,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_8
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f353,f137])).

fof(f353,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK2,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_13 ),
    inference(resolution,[],[f348,f162])).

fof(f162,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f348,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
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
    inference(subsumption_resolution,[],[f347,f83])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f347,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ r1_tsep_1(X2,X3)
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
    inference(subsumption_resolution,[],[f346,f84])).

fof(f346,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ r1_tsep_1(X2,X3)
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
    inference(subsumption_resolution,[],[f88,f82])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ r1_tsep_1(X2,X3)
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
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | ~ r1_tsep_1(X2,X3)
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

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | r1_tsep_1(X2,X3) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_tmap_1)).

fof(f552,plain,
    ( spl6_49
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f544,f527,f155,f150,f135,f130,f110,f105,f100,f550])).

fof(f527,plain,
    ( spl6_47
  <=> ! [X1,X0] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f544,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f543,f132])).

fof(f543,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | v2_struct_0(sK2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f542,f152])).

fof(f542,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_8
    | ~ spl6_12
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f541,f137])).

fof(f541,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f540,f157])).

fof(f540,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f539,f102])).

fof(f539,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f538,f107])).

fof(f538,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl6_3
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f537,f112])).

fof(f537,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2) )
    | ~ spl6_47 ),
    inference(duplicate_literal_removal,[],[f536])).

fof(f536,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_47 ),
    inference(resolution,[],[f528,f76])).

fof(f528,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ m1_pre_topc(X1,X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f527])).

fof(f548,plain,
    ( spl6_48
    | spl6_7
    | spl6_8
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f341,f160,f135,f130,f546])).

fof(f341,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK3,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_7
    | spl6_8
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f340,f132])).

fof(f340,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK3,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl6_8
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f339,f137])).

fof(f339,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK2,sK3),sK3,k10_tmap_1(X1,X0,sK2,sK3,X2,X3)),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_13 ),
    inference(resolution,[],[f334,f162])).

fof(f334,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
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
    inference(subsumption_resolution,[],[f333,f83])).

fof(f333,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ r1_tsep_1(X2,X3)
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
    inference(subsumption_resolution,[],[f332,f84])).

fof(f332,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ r1_tsep_1(X2,X3)
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
    inference(subsumption_resolution,[],[f86,f82])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ r1_tsep_1(X2,X3)
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
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | ~ r1_tsep_1(X2,X3)
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

fof(f529,plain,
    ( spl6_47
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f502,f479,f232,f195,f190,f185,f180,f155,f150,f145,f140,f135,f130,f125,f120,f115,f110,f105,f100,f527])).

fof(f479,plain,
    ( spl6_42
  <=> ! [X5,X7,X8,X6] :
        ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(X5),u1_struct_0(X6))
        | v1_funct_1(k3_tmap_1(X7,X6,X5,X8,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X8,X7)
        | ~ m1_pre_topc(X5,X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f502,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f501,f102])).

fof(f501,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f500,f107])).

fof(f500,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f499,f112])).

fof(f499,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f498,f132])).

fof(f498,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f497,f152])).

fof(f497,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f496,f137])).

fof(f496,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f495,f157])).

fof(f495,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f494,f142])).

fof(f494,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f493,f182])).

fof(f493,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f492,f192])).

fof(f492,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f491,f147])).

fof(f491,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f490,f187])).

fof(f490,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f489,f197])).

fof(f489,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f488,f117])).

fof(f488,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f487,f122])).

fof(f487,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_6
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f486,f127])).

fof(f486,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_26
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f485,f233])).

fof(f485,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_42 ),
    inference(duplicate_literal_removal,[],[f484])).

fof(f484,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(sK0,sK2,sK3),X1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_42 ),
    inference(resolution,[],[f480,f84])).

fof(f480,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(X5),u1_struct_0(X6))
        | v1_funct_1(k3_tmap_1(X7,X6,X5,X8,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X8,X7)
        | ~ m1_pre_topc(X5,X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f479])).

fof(f481,plain,
    ( spl6_42
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f255,f228,f479])).

fof(f255,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(X5),u1_struct_0(X6))
        | v1_funct_1(k3_tmap_1(X7,X6,X5,X8,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(X8,X7)
        | ~ m1_pre_topc(X5,X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) )
    | ~ spl6_25 ),
    inference(resolution,[],[f229,f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f297,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f295,f102])).

fof(f295,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f294,f107])).

fof(f294,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f293,f112])).

fof(f293,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f292,f117])).

fof(f292,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f291,f122])).

fof(f291,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f290,f127])).

fof(f290,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f289,f132])).

fof(f289,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f288,f152])).

fof(f288,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f287,f137])).

fof(f287,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f286,f157])).

fof(f286,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f285,f142])).

fof(f285,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f284,f182])).

fof(f284,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f283,f192])).

fof(f283,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f282,f147])).

fof(f282,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_18
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f281,f187])).

fof(f281,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_20
    | spl6_26 ),
    inference(subsumption_resolution,[],[f279,f197])).

fof(f279,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_26 ),
    inference(resolution,[],[f83,f234])).

fof(f234,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f232])).

fof(f253,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_25 ),
    inference(unit_resulting_resolution,[],[f102,f107,f112,f117,f122,f127,f132,f142,f137,f147,f152,f157,f182,f230,f192,f187,f197,f82])).

fof(f230,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f228])).

fof(f243,plain,
    ( ~ spl6_25
    | ~ spl6_26
    | ~ spl6_27
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f55,f240,f236,f232,f228])).

fof(f55,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    & r4_tsep_1(sK0,sK2,sK3)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v5_pre_topc(sK5,sK3,sK1)
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(sK4,sK2,sK1)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & r1_tsep_1(sK2,sK3)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f28,f27,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                            & r4_tsep_1(X0,X2,X3)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & r1_tsep_1(X2,X3)
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(sK0,X2,X3)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r1_tsep_1(X2,X3)
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

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),X1)
                          | ~ v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5)) )
                        & r4_tsep_1(sK0,X2,X3)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & r1_tsep_1(X2,X3)
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
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1))))
                        | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),sK1)
                        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1))
                        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5)) )
                      & r4_tsep_1(sK0,X2,X3)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v5_pre_topc(X5,X3,sK1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                  & v5_pre_topc(X4,X2,sK1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & r1_tsep_1(X2,X3)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1))))
                      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),sK1)
                      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1))
                      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5)) )
                    & r4_tsep_1(sK0,X2,X3)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v5_pre_topc(X5,X3,sK1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                & v5_pre_topc(X4,X2,sK1)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & r1_tsep_1(X2,X3)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_tsep_1(sK0,sK2,X3),sK1)
                    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1))
                    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)) )
                  & r4_tsep_1(sK0,sK2,X3)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v5_pre_topc(X5,X3,sK1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v5_pre_topc(X4,sK2,sK1)
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & r1_tsep_1(sK2,X3)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_tsep_1(sK0,sK2,X3),sK1)
                  | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1))
                  | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)) )
                & r4_tsep_1(sK0,sK2,X3)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v5_pre_topc(X5,X3,sK1)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v5_pre_topc(X4,sK2,sK1)
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & r1_tsep_1(sK2,X3)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_tsep_1(sK0,sK2,sK3),sK1)
                | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
                | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)) )
              & r4_tsep_1(sK0,sK2,sK3)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v5_pre_topc(X5,sK3,sK1)
              & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v5_pre_topc(X4,sK2,sK1)
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & r1_tsep_1(sK2,sK3)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_tsep_1(sK0,sK2,sK3),sK1)
              | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
              | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)) )
            & r4_tsep_1(sK0,sK2,sK3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            & v5_pre_topc(X5,sK3,sK1)
            & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v5_pre_topc(X4,sK2,sK1)
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
            | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_tsep_1(sK0,sK2,sK3),sK1)
            | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
            | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)) )
          & r4_tsep_1(sK0,sK2,sK3)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v5_pre_topc(X5,sK3,sK1)
          & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v5_pre_topc(sK4,sK2,sK1)
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_tsep_1(sK0,sK2,sK3),sK1)
          | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
          | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)) )
        & r4_tsep_1(sK0,sK2,sK3)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v5_pre_topc(X5,sK3,sK1)
        & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
      & r4_tsep_1(sK0,sK2,sK3)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v5_pre_topc(sK5,sK3,sK1)
      & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r1_tsep_1(X2,X3)
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f8])).

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
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( r1_tsep_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(X4,X2,X1)
                            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v5_pre_topc(X5,X3,X1)
                                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( r4_tsep_1(X0,X2,X3)
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( r4_tsep_1(X0,X2,X3)
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_tmap_1)).

fof(f198,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f53,f195])).

fof(f53,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f193,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f49,f190])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f188,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f51,f185])).

fof(f51,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f183,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f47,f180])).

fof(f47,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f178,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f54,f175])).

fof(f54,plain,(
    r4_tsep_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f173,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f52,f170])).

fof(f52,plain,(
    v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f168,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f48,f165])).

fof(f48,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f163,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f45,f160])).

fof(f45,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f158,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f44,f155])).

fof(f44,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f153,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f42,f150])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f148,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f50,f145])).

fof(f50,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f143,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f46,f140])).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f138,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f43,f135])).

fof(f43,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f133,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f41,f130])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f128,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f40,f125])).

fof(f40,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f123,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f39,f120])).

fof(f39,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f118,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f38,f115])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f113,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f37,f110])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f36,f105])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f35,f100])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------

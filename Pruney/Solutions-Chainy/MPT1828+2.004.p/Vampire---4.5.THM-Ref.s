%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:49 EST 2020

% Result     : Theorem 2.30s
% Output     : Refutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  391 (1127 expanded)
%              Number of leaves         :   57 ( 516 expanded)
%              Depth                    :   33
%              Number of atoms          : 4460 (13114 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :   29 (  12 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1020,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f167,f172,f177,f182,f187,f192,f197,f216,f270,f274,f315,f321,f362,f396,f404,f429,f569,f648,f665,f719,f791,f809,f841,f843,f895,f920,f929,f955,f1001,f1019])).

fof(f1019,plain,
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
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_79
    | ~ spl6_83 ),
    inference(avatar_contradiction_clause,[],[f1018])).

fof(f1018,plain,
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
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_79
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f1017,f166])).

fof(f166,plain,
    ( v5_pre_topc(sK4,sK2,sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl6_14
  <=> v5_pre_topc(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f1017,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_79
    | ~ spl6_83 ),
    inference(forward_demodulation,[],[f1016,f647])).

fof(f647,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f645])).

fof(f645,plain,
    ( spl6_79
  <=> sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f1016,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_79
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f1015,f191])).

fof(f191,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl6_19
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f1015,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_79
    | ~ spl6_83 ),
    inference(forward_demodulation,[],[f984,f647])).

fof(f984,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f983,f101])).

fof(f101,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f983,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f982,f106])).

fof(f106,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f982,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f981,f111])).

fof(f111,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f981,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f980,f116])).

fof(f116,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f980,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f979,f121])).

fof(f121,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f979,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f978,f126])).

fof(f126,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f978,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f977,f131])).

fof(f131,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f977,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f976,f151])).

fof(f151,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_11
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f976,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f975,f136])).

fof(f136,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_8
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f975,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f974,f156])).

fof(f156,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_12
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f974,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f973,f176])).

fof(f176,plain,
    ( r4_tsep_1(sK0,sK2,sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl6_16
  <=> r4_tsep_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f973,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_28
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f972,f256])).

fof(f256,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl6_28
  <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f972,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | ~ spl6_29
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f971,f260])).

fof(f260,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl6_29
  <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f971,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | spl6_30
    | ~ spl6_31
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f970,f268])).

fof(f268,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl6_31
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f970,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | spl6_30
    | ~ spl6_76
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f969,f634])).

fof(f634,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f633])).

fof(f633,plain,
    ( spl6_76
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f969,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
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
    | spl6_30
    | ~ spl6_77
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f968,f638])).

fof(f638,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f637])).

fof(f637,plain,
    ( spl6_77
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f968,plain,
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
    | spl6_30
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f967,f265])).

fof(f265,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl6_30
  <=> v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f967,plain,
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
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f966,f186])).

fof(f186,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl6_18
  <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f966,plain,
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
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f965,f171])).

fof(f171,plain,
    ( v5_pre_topc(sK5,sK3,sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl6_15
  <=> v5_pre_topc(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f965,plain,
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
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f964,f196])).

fof(f196,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl6_20
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f964,plain,
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
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f959,f146])).

fof(f146,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_10
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f959,plain,
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
    | ~ spl6_83 ),
    inference(superposition,[],[f76,f664])).

fof(f664,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f662])).

fof(f662,plain,
    ( spl6_83
  <=> sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).

fof(f1001,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_78
    | ~ spl6_94 ),
    inference(avatar_contradiction_clause,[],[f1000])).

fof(f1000,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_78
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f999,f101])).

fof(f999,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_78
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f998,f106])).

fof(f998,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_78
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f997,f111])).

fof(f997,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_78
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f996,f116])).

fof(f996,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_78
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f995,f121])).

fof(f995,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_78
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f994,f126])).

fof(f994,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_78
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f993,f786])).

fof(f786,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f785])).

fof(f785,plain,
    ( spl6_94
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f993,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_78 ),
    inference(subsumption_resolution,[],[f992,f151])).

fof(f992,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_78 ),
    inference(subsumption_resolution,[],[f991,f256])).

fof(f991,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_29
    | ~ spl6_31
    | spl6_78 ),
    inference(subsumption_resolution,[],[f990,f260])).

fof(f990,plain,
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
    | ~ spl6_31
    | spl6_78 ),
    inference(subsumption_resolution,[],[f987,f268])).

fof(f987,plain,
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
    | spl6_78 ),
    inference(resolution,[],[f643,f84])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f643,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl6_78 ),
    inference(avatar_component_clause,[],[f641])).

fof(f641,plain,
    ( spl6_78
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f955,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_81
    | ~ spl6_94 ),
    inference(avatar_contradiction_clause,[],[f954])).

fof(f954,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_81
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f953,f101])).

fof(f953,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_81
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f952,f106])).

fof(f952,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_81
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f951,f111])).

fof(f951,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_81
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f950,f116])).

fof(f950,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_81
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f949,f121])).

fof(f949,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_81
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f948,f126])).

fof(f948,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_81
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f947,f786])).

fof(f947,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_81 ),
    inference(subsumption_resolution,[],[f946,f156])).

fof(f946,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_81 ),
    inference(subsumption_resolution,[],[f945,f256])).

fof(f945,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_29
    | ~ spl6_31
    | spl6_81 ),
    inference(subsumption_resolution,[],[f944,f260])).

fof(f944,plain,
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
    | ~ spl6_31
    | spl6_81 ),
    inference(subsumption_resolution,[],[f942,f268])).

fof(f942,plain,
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
    | spl6_81 ),
    inference(resolution,[],[f656,f83])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f656,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl6_81 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl6_81
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f929,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_82
    | ~ spl6_94 ),
    inference(avatar_contradiction_clause,[],[f926])).

fof(f926,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | spl6_82
    | ~ spl6_94 ),
    inference(unit_resulting_resolution,[],[f101,f106,f111,f116,f121,f126,f156,f786,f256,f260,f660,f268,f84])).

fof(f660,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl6_82 ),
    inference(avatar_component_clause,[],[f658])).

fof(f658,plain,
    ( spl6_82
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f920,plain,
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
    | spl6_31 ),
    inference(avatar_contradiction_clause,[],[f919])).

fof(f919,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f918,f101])).

fof(f918,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f917,f106])).

fof(f917,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f916,f111])).

fof(f916,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f915,f116])).

fof(f915,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f914,f121])).

fof(f914,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f913,f126])).

fof(f913,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f912,f131])).

fof(f912,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f911,f151])).

fof(f911,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f910,f136])).

fof(f910,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f909,f156])).

fof(f909,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f908,f141])).

fof(f141,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl6_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f908,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f907,f181])).

fof(f181,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl6_17
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f907,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f906,f191])).

fof(f906,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f905,f146])).

fof(f905,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f904,f186])).

fof(f904,plain,
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
    | spl6_31 ),
    inference(subsumption_resolution,[],[f902,f196])).

fof(f902,plain,
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
    | spl6_31 ),
    inference(resolution,[],[f269,f87])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f269,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | spl6_31 ),
    inference(avatar_component_clause,[],[f267])).

fof(f895,plain,
    ( ~ spl6_31
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | spl6_77
    | ~ spl6_94 ),
    inference(avatar_split_clause,[],[f882,f785,f637,f259,f255,f149,f124,f119,f114,f109,f104,f99,f267])).

fof(f882,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | spl6_77
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f881,f101])).

fof(f881,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | spl6_77
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f880,f106])).

fof(f880,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | spl6_77
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f879,f111])).

fof(f879,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | spl6_77
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f878,f116])).

fof(f878,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | spl6_77
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f877,f121])).

fof(f877,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | spl6_77
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f876,f126])).

fof(f876,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | spl6_77
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f875,f786])).

fof(f875,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | spl6_77 ),
    inference(subsumption_resolution,[],[f874,f151])).

fof(f874,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28
    | ~ spl6_29
    | spl6_77 ),
    inference(subsumption_resolution,[],[f873,f256])).

fof(f873,plain,
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
    | ~ spl6_29
    | spl6_77 ),
    inference(subsumption_resolution,[],[f871,f260])).

fof(f871,plain,
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
    | spl6_77 ),
    inference(resolution,[],[f639,f83])).

fof(f639,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_77 ),
    inference(avatar_component_clause,[],[f637])).

fof(f843,plain,
    ( ~ spl6_12
    | spl6_80
    | ~ spl6_95 ),
    inference(avatar_contradiction_clause,[],[f842])).

fof(f842,plain,
    ( $false
    | ~ spl6_12
    | spl6_80
    | ~ spl6_95 ),
    inference(subsumption_resolution,[],[f832,f652])).

fof(f652,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | spl6_80 ),
    inference(avatar_component_clause,[],[f650])).

fof(f650,plain,
    ( spl6_80
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f832,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_12
    | ~ spl6_95 ),
    inference(resolution,[],[f790,f156])).

fof(f790,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | ~ spl6_95 ),
    inference(avatar_component_clause,[],[f789])).

fof(f789,plain,
    ( spl6_95
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f841,plain,
    ( ~ spl6_11
    | spl6_76
    | ~ spl6_95 ),
    inference(avatar_contradiction_clause,[],[f840])).

fof(f840,plain,
    ( $false
    | ~ spl6_11
    | spl6_76
    | ~ spl6_95 ),
    inference(subsumption_resolution,[],[f831,f635])).

fof(f635,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | spl6_76 ),
    inference(avatar_component_clause,[],[f633])).

fof(f831,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_11
    | ~ spl6_95 ),
    inference(resolution,[],[f790,f151])).

fof(f809,plain,
    ( spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_38
    | spl6_94 ),
    inference(avatar_contradiction_clause,[],[f808])).

fof(f808,plain,
    ( $false
    | spl6_7
    | spl6_8
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_38
    | spl6_94 ),
    inference(subsumption_resolution,[],[f807,f151])).

fof(f807,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl6_7
    | spl6_8
    | ~ spl6_12
    | ~ spl6_38
    | spl6_94 ),
    inference(subsumption_resolution,[],[f806,f131])).

fof(f806,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | spl6_8
    | ~ spl6_12
    | ~ spl6_38
    | spl6_94 ),
    inference(subsumption_resolution,[],[f805,f156])).

fof(f805,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | spl6_8
    | ~ spl6_38
    | spl6_94 ),
    inference(subsumption_resolution,[],[f799,f136])).

fof(f799,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl6_38
    | spl6_94 ),
    inference(resolution,[],[f787,f361])).

fof(f361,plain,
    ( ! [X4,X5] :
        ( m1_pre_topc(k1_tsep_1(sK0,X4,X5),sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0) )
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl6_38
  <=> ! [X5,X4] :
        ( ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X4)
        | m1_pre_topc(k1_tsep_1(sK0,X4,X5),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f787,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | spl6_94 ),
    inference(avatar_component_clause,[],[f785])).

fof(f791,plain,
    ( ~ spl6_94
    | spl6_95
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
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f745,f717,f259,f194,f189,f184,f179,f154,f149,f144,f139,f134,f129,f124,f119,f114,f109,f104,f99,f789,f785])).

fof(f717,plain,
    ( spl6_90
  <=> ! [X5,X4] :
        ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(X4),u1_struct_0(sK1))
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f745,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
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
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f744,f101])).

fof(f744,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f743,f106])).

fof(f743,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f742,f111])).

fof(f742,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f741,f116])).

fof(f741,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
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
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f740,f121])).

fof(f740,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
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
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f739,f126])).

fof(f739,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
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
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f738,f131])).

fof(f738,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f737,f151])).

fof(f737,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f736,f136])).

fof(f736,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f735,f156])).

fof(f735,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f734,f141])).

fof(f734,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f733,f181])).

fof(f733,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f732,f191])).

fof(f732,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f731,f146])).

fof(f731,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f730,f186])).

fof(f730,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_20
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f729,f196])).

fof(f729,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_29
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f728,f260])).

fof(f728,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
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
    | ~ spl6_90 ),
    inference(resolution,[],[f718,f87])).

fof(f718,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(X4),u1_struct_0(sK1))
        | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f717])).

fof(f719,plain,
    ( spl6_90
    | ~ spl6_28
    | ~ spl6_65 ),
    inference(avatar_split_clause,[],[f580,f567,f255,f717])).

fof(f567,plain,
    ( spl6_65
  <=> ! [X3,X5,X4] :
        ( ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f580,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(X4),u1_struct_0(sK1))
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | ~ spl6_28
    | ~ spl6_65 ),
    inference(resolution,[],[f568,f256])).

fof(f568,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3)) )
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f567])).

fof(f665,plain,
    ( ~ spl6_80
    | ~ spl6_81
    | ~ spl6_82
    | spl6_83
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f420,f401,f194,f184,f144,f662,f658,f654,f650])).

fof(f401,plain,
    ( spl6_41
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f420,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f419,f146])).

fof(f419,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f418,f186])).

fof(f418,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_20
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f417,f196])).

fof(f417,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_41 ),
    inference(resolution,[],[f403,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f403,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f401])).

fof(f648,plain,
    ( ~ spl6_76
    | ~ spl6_77
    | ~ spl6_78
    | spl6_79
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f412,f393,f189,f179,f139,f645,f641,f637,f633])).

fof(f393,plain,
    ( spl6_40
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f412,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f411,f141])).

fof(f411,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f410,f181])).

fof(f410,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_19
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f409,f191])).

fof(f409,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_40 ),
    inference(resolution,[],[f395,f80])).

fof(f395,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f393])).

fof(f569,plain,
    ( spl6_65
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f447,f427,f124,f119,f114,f567])).

fof(f427,plain,
    ( spl6_44
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f447,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3)) )
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f446,f116])).

fof(f446,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | v2_struct_0(sK1)
        | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3)) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f443,f121])).

fof(f443,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3)) )
    | ~ spl6_6
    | ~ spl6_44 ),
    inference(resolution,[],[f428,f126])).

fof(f428,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(X2)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0)) )
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f427])).

fof(f429,plain,
    ( spl6_44
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f242,f109,f104,f99,f427])).

fof(f242,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f241,f101])).

fof(f241,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f239,f106])).

fof(f239,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f82,f111])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f404,plain,
    ( spl6_41
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f380,f213,f194,f189,f184,f179,f159,f154,f149,f144,f139,f134,f129,f124,f119,f114,f109,f104,f99,f401])).

fof(f159,plain,
    ( spl6_13
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f213,plain,
    ( spl6_23
  <=> r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f380,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f379,f101])).

fof(f379,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | v2_struct_0(sK0)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f378,f106])).

fof(f378,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ v2_pre_topc(sK0)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f377,f111])).

fof(f377,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ l1_pre_topc(sK0)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f376,f116])).

fof(f376,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | v2_struct_0(sK1)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f375,f121])).

fof(f375,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ v2_pre_topc(sK1)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f374,f126])).

fof(f374,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ l1_pre_topc(sK1)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f373,f131])).

fof(f373,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
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
    | ~ spl6_11
    | ~ spl6_12
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f372,f151])).

fof(f372,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ m1_pre_topc(sK2,sK0)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f371,f136])).

fof(f371,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
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
    | ~ spl6_12
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f370,f156])).

fof(f370,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
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
    | ~ spl6_9
    | ~ spl6_10
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f369,f161])).

fof(f161,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f369,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f368,f141])).

fof(f368,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f367,f181])).

fof(f367,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f366,f191])).

fof(f366,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f365,f146])).

fof(f365,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f364,f186])).

fof(f364,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f363,f196])).

fof(f363,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_23 ),
    inference(resolution,[],[f65,f215])).

fof(f215,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f213])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | r1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                              | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                            & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                              | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                            & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
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
                 => ( ~ r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                            <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_tmap_1)).

fof(f396,plain,
    ( spl6_40
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f358,f213,f194,f189,f184,f179,f159,f154,f149,f144,f139,f134,f129,f124,f119,f114,f109,f104,f99,f393])).

fof(f358,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f357,f101])).

fof(f357,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | v2_struct_0(sK0)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f356,f106])).

fof(f356,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ v2_pre_topc(sK0)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f355,f111])).

fof(f355,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ l1_pre_topc(sK0)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f354,f116])).

fof(f354,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | v2_struct_0(sK1)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f353,f121])).

fof(f353,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ v2_pre_topc(sK1)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f352,f126])).

fof(f352,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ l1_pre_topc(sK1)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f351,f131])).

fof(f351,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
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
    | ~ spl6_11
    | ~ spl6_12
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f350,f151])).

fof(f350,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ m1_pre_topc(sK2,sK0)
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
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f349,f136])).

fof(f349,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
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
    | ~ spl6_12
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f348,f156])).

fof(f348,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
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
    | ~ spl6_9
    | ~ spl6_10
    | spl6_13
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f347,f161])).

fof(f347,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f346,f141])).

fof(f346,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f345,f181])).

fof(f345,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f344,f191])).

fof(f344,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f343,f146])).

fof(f343,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f342,f186])).

fof(f342,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f341,f196])).

fof(f341,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r1_tsep_1(sK2,sK3)
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
    | ~ spl6_23 ),
    inference(resolution,[],[f64,f215])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | r1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f36])).

fof(f362,plain,
    ( spl6_38
    | spl6_1
    | ~ spl6_3
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f332,f319,f109,f99,f360])).

fof(f319,plain,
    ( spl6_34
  <=> ! [X1,X0,X2] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X2)
        | m1_pre_topc(k1_tsep_1(sK0,X2,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f332,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X4)
        | m1_pre_topc(k1_tsep_1(sK0,X4,X5),sK0) )
    | spl6_1
    | ~ spl6_3
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f331,f111])).

fof(f331,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X4)
        | m1_pre_topc(k1_tsep_1(sK0,X4,X5),sK0)
        | ~ l1_pre_topc(sK0) )
    | spl6_1
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f328,f101])).

fof(f328,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X4)
        | m1_pre_topc(k1_tsep_1(sK0,X4,X5),sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_34 ),
    inference(resolution,[],[f320,f62])).

fof(f62,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f320,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X1)
        | v2_struct_0(X2)
        | m1_pre_topc(k1_tsep_1(sK0,X2,X0),X1) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f319])).

fof(f321,plain,
    ( spl6_34
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f235,f109,f104,f99,f319])).

fof(f235,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X2)
        | m1_pre_topc(k1_tsep_1(sK0,X2,X0),X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f234,f101])).

fof(f234,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X2)
        | m1_pre_topc(k1_tsep_1(sK0,X2,X0),X1)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f232,f106])).

fof(f232,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X2,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X2)
        | m1_pre_topc(k1_tsep_1(sK0,X2,X0),X1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f230,f111])).

fof(f230,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | v2_struct_0(X1)
      | m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f229,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f229,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f78,f79])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
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
                  ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  | ~ m1_pre_topc(X3,X2)
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
                  ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  | ~ m1_pre_topc(X3,X2)
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f315,plain,
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
    | spl6_29 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f313,f101])).

fof(f313,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f312,f106])).

fof(f312,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f311,f111])).

fof(f311,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f310,f116])).

fof(f310,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f309,f121])).

fof(f309,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f308,f126])).

fof(f308,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f307,f131])).

fof(f307,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f306,f151])).

fof(f306,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f305,f136])).

fof(f305,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f304,f156])).

fof(f304,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f303,f141])).

fof(f303,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f302,f181])).

fof(f302,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f301,f191])).

fof(f301,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f300,f146])).

fof(f300,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f299,f186])).

fof(f299,plain,
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
    | spl6_29 ),
    inference(subsumption_resolution,[],[f297,f196])).

fof(f297,plain,
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
    | spl6_29 ),
    inference(resolution,[],[f86,f261])).

fof(f261,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f259])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f274,plain,
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
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
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
    inference(unit_resulting_resolution,[],[f101,f106,f146,f116,f121,f126,f131,f141,f136,f111,f151,f156,f181,f257,f191,f186,f196,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_pre_topc(X0)
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
      | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f257,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f255])).

fof(f270,plain,
    ( ~ spl6_28
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f61,f267,f263,f259,f255])).

fof(f61,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    & r4_tsep_1(sK0,sK2,sK3)
    & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v5_pre_topc(sK5,sK3,sK1)
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(sK4,sK2,sK1)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & ~ r1_tsep_1(sK2,sK3)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f33,f32,f31,f30,f29,f28])).

fof(f28,plain,
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
                            & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & ~ r1_tsep_1(X2,X3)
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
                          & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK0,X1,X2,k2_tsep_1(sK0,X2,X3),X4),k3_tmap_1(sK0,X1,X3,k2_tsep_1(sK0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
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

fof(f29,plain,
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
                        & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK0,X1,X2,k2_tsep_1(sK0,X2,X3),X4),k3_tmap_1(sK0,X1,X3,k2_tsep_1(sK0,X2,X3),X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & ~ r1_tsep_1(X2,X3)
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
                      & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,X2,X3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X2,k2_tsep_1(sK0,X2,X3),X4),k3_tmap_1(sK0,sK1,X3,k2_tsep_1(sK0,X2,X3),X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v5_pre_topc(X5,X3,sK1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                  & v5_pre_topc(X4,X2,sK1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & ~ r1_tsep_1(X2,X3)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1))))
                      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),sK1)
                      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1))
                      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5)) )
                    & r4_tsep_1(sK0,X2,X3)
                    & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,X2,X3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X2,k2_tsep_1(sK0,X2,X3),X4),k3_tmap_1(sK0,sK1,X3,k2_tsep_1(sK0,X2,X3),X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v5_pre_topc(X5,X3,sK1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                & v5_pre_topc(X4,X2,sK1)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & ~ r1_tsep_1(X2,X3)
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
                  & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,X3),X4),k3_tmap_1(sK0,sK1,X3,k2_tsep_1(sK0,sK2,X3),X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v5_pre_topc(X5,X3,sK1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v5_pre_topc(X4,sK2,sK1)
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & ~ r1_tsep_1(sK2,X3)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_tsep_1(sK0,sK2,X3),sK1)
                  | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1))
                  | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)) )
                & r4_tsep_1(sK0,sK2,X3)
                & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,X3),X4),k3_tmap_1(sK0,sK1,X3,k2_tsep_1(sK0,sK2,X3),X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v5_pre_topc(X5,X3,sK1)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v5_pre_topc(X4,sK2,sK1)
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & ~ r1_tsep_1(sK2,X3)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_tsep_1(sK0,sK2,sK3),sK1)
                | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
                | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)) )
              & r4_tsep_1(sK0,sK2,sK3)
              & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),X4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v5_pre_topc(X5,sK3,sK1)
              & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v5_pre_topc(X4,sK2,sK1)
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & ~ r1_tsep_1(sK2,sK3)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_tsep_1(sK0,sK2,sK3),sK1)
              | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
              | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)) )
            & r4_tsep_1(sK0,sK2,sK3)
            & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),X4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X5))
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
          & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v5_pre_topc(X5,sK3,sK1)
          & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v5_pre_topc(sK4,sK2,sK1)
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_tsep_1(sK0,sK2,sK3),sK1)
          | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
          | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)) )
        & r4_tsep_1(sK0,sK2,sK3)
        & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X5))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v5_pre_topc(X5,sK3,sK1)
        & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
      & r4_tsep_1(sK0,sK2,sK3)
      & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v5_pre_topc(sK5,sK3,sK1)
      & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
                   => ( ~ r1_tsep_1(X2,X3)
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
                             => ( ( r4_tsep_1(X0,X2,X3)
                                  & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
                 => ( ~ r1_tsep_1(X2,X3)
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
                           => ( ( r4_tsep_1(X0,X2,X3)
                                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_tmap_1)).

fof(f216,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f59,f213])).

fof(f59,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f197,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f58,f194])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f192,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f54,f189])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f187,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f56,f184])).

fof(f56,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f182,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f52,f179])).

fof(f52,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f177,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f60,f174])).

fof(f60,plain,(
    r4_tsep_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f172,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f57,f169])).

fof(f57,plain,(
    v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f167,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f53,f164])).

fof(f53,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f162,plain,(
    ~ spl6_13 ),
    inference(avatar_split_clause,[],[f50,f159])).

fof(f50,plain,(
    ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f157,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f49,f154])).

fof(f49,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f152,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f47,f149])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f147,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f55,f144])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f142,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f51,f139])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f137,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f48,f134])).

fof(f48,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f132,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f46,f129])).

fof(f46,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f127,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f45,f124])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f122,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f44,f119])).

fof(f44,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f117,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f43,f114])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f112,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f42,f109])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f41,f104])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f102,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f40,f99])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (19325)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  % (19317)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (19308)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (19309)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (19315)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (19318)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (19326)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (19306)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (19320)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (19327)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (19322)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (19319)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (19307)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (19311)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (19328)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (19324)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (19305)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (19310)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (19313)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (19314)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (19316)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (19311)Refutation not found, incomplete strategy% (19311)------------------------------
% 0.21/0.54  % (19311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19311)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19311)Memory used [KB]: 10874
% 0.21/0.55  % (19311)Time elapsed: 0.079 s
% 0.21/0.55  % (19311)------------------------------
% 0.21/0.55  % (19311)------------------------------
% 1.56/0.56  % (19323)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.56/0.56  % (19330)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.56/0.57  % (19321)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.70/0.58  % (19329)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.70/0.58  % (19312)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 2.30/0.66  % (19307)Refutation found. Thanks to Tanya!
% 2.30/0.66  % SZS status Theorem for theBenchmark
% 2.30/0.66  % SZS output start Proof for theBenchmark
% 2.30/0.67  fof(f1020,plain,(
% 2.30/0.67    $false),
% 2.30/0.67    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f167,f172,f177,f182,f187,f192,f197,f216,f270,f274,f315,f321,f362,f396,f404,f429,f569,f648,f665,f719,f791,f809,f841,f843,f895,f920,f929,f955,f1001,f1019])).
% 2.30/0.67  fof(f1019,plain,(
% 2.30/0.67    spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_79 | ~spl6_83),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f1018])).
% 2.30/0.67  fof(f1018,plain,(
% 2.30/0.67    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_79 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f1017,f166])).
% 2.30/0.67  fof(f166,plain,(
% 2.30/0.67    v5_pre_topc(sK4,sK2,sK1) | ~spl6_14),
% 2.30/0.67    inference(avatar_component_clause,[],[f164])).
% 2.30/0.67  fof(f164,plain,(
% 2.30/0.67    spl6_14 <=> v5_pre_topc(sK4,sK2,sK1)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.30/0.67  fof(f1017,plain,(
% 2.30/0.67    ~v5_pre_topc(sK4,sK2,sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_79 | ~spl6_83)),
% 2.30/0.67    inference(forward_demodulation,[],[f1016,f647])).
% 2.30/0.67  fof(f647,plain,(
% 2.30/0.67    sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl6_79),
% 2.30/0.67    inference(avatar_component_clause,[],[f645])).
% 2.30/0.67  fof(f645,plain,(
% 2.30/0.67    spl6_79 <=> sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 2.30/0.67  fof(f1016,plain,(
% 2.30/0.67    ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_79 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f1015,f191])).
% 2.30/0.67  fof(f191,plain,(
% 2.30/0.67    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~spl6_19),
% 2.30/0.67    inference(avatar_component_clause,[],[f189])).
% 2.30/0.67  fof(f189,plain,(
% 2.30/0.67    spl6_19 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 2.30/0.67  fof(f1015,plain,(
% 2.30/0.67    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_79 | ~spl6_83)),
% 2.30/0.67    inference(forward_demodulation,[],[f984,f647])).
% 2.30/0.67  fof(f984,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f983,f101])).
% 2.30/0.67  fof(f101,plain,(
% 2.30/0.67    ~v2_struct_0(sK0) | spl6_1),
% 2.30/0.67    inference(avatar_component_clause,[],[f99])).
% 2.30/0.67  fof(f99,plain,(
% 2.30/0.67    spl6_1 <=> v2_struct_0(sK0)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.30/0.67  fof(f983,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f982,f106])).
% 2.30/0.67  fof(f106,plain,(
% 2.30/0.67    v2_pre_topc(sK0) | ~spl6_2),
% 2.30/0.67    inference(avatar_component_clause,[],[f104])).
% 2.30/0.67  fof(f104,plain,(
% 2.30/0.67    spl6_2 <=> v2_pre_topc(sK0)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.30/0.67  fof(f982,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f981,f111])).
% 2.30/0.67  fof(f111,plain,(
% 2.30/0.67    l1_pre_topc(sK0) | ~spl6_3),
% 2.30/0.67    inference(avatar_component_clause,[],[f109])).
% 2.30/0.67  fof(f109,plain,(
% 2.30/0.67    spl6_3 <=> l1_pre_topc(sK0)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.30/0.67  fof(f981,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f980,f116])).
% 2.30/0.67  fof(f116,plain,(
% 2.30/0.67    ~v2_struct_0(sK1) | spl6_4),
% 2.30/0.67    inference(avatar_component_clause,[],[f114])).
% 2.30/0.67  fof(f114,plain,(
% 2.30/0.67    spl6_4 <=> v2_struct_0(sK1)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.30/0.67  fof(f980,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f979,f121])).
% 2.30/0.67  fof(f121,plain,(
% 2.30/0.67    v2_pre_topc(sK1) | ~spl6_5),
% 2.30/0.67    inference(avatar_component_clause,[],[f119])).
% 2.30/0.67  fof(f119,plain,(
% 2.30/0.67    spl6_5 <=> v2_pre_topc(sK1)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.30/0.67  fof(f979,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f978,f126])).
% 2.30/0.67  fof(f126,plain,(
% 2.30/0.67    l1_pre_topc(sK1) | ~spl6_6),
% 2.30/0.67    inference(avatar_component_clause,[],[f124])).
% 2.30/0.67  fof(f124,plain,(
% 2.30/0.67    spl6_6 <=> l1_pre_topc(sK1)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.30/0.67  fof(f978,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_7 | spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f977,f131])).
% 2.30/0.67  fof(f131,plain,(
% 2.30/0.67    ~v2_struct_0(sK2) | spl6_7),
% 2.30/0.67    inference(avatar_component_clause,[],[f129])).
% 2.30/0.67  fof(f129,plain,(
% 2.30/0.67    spl6_7 <=> v2_struct_0(sK2)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.30/0.67  fof(f977,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f976,f151])).
% 2.30/0.67  fof(f151,plain,(
% 2.30/0.67    m1_pre_topc(sK2,sK0) | ~spl6_11),
% 2.30/0.67    inference(avatar_component_clause,[],[f149])).
% 2.30/0.67  fof(f149,plain,(
% 2.30/0.67    spl6_11 <=> m1_pre_topc(sK2,sK0)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.30/0.67  fof(f976,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_8 | ~spl6_10 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f975,f136])).
% 2.30/0.67  fof(f136,plain,(
% 2.30/0.67    ~v2_struct_0(sK3) | spl6_8),
% 2.30/0.67    inference(avatar_component_clause,[],[f134])).
% 2.30/0.67  fof(f134,plain,(
% 2.30/0.67    spl6_8 <=> v2_struct_0(sK3)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.30/0.67  fof(f975,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f974,f156])).
% 2.30/0.67  fof(f156,plain,(
% 2.30/0.67    m1_pre_topc(sK3,sK0) | ~spl6_12),
% 2.30/0.67    inference(avatar_component_clause,[],[f154])).
% 2.30/0.67  fof(f154,plain,(
% 2.30/0.67    spl6_12 <=> m1_pre_topc(sK3,sK0)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.30/0.67  fof(f974,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f973,f176])).
% 2.30/0.67  fof(f176,plain,(
% 2.30/0.67    r4_tsep_1(sK0,sK2,sK3) | ~spl6_16),
% 2.30/0.67    inference(avatar_component_clause,[],[f174])).
% 2.30/0.67  fof(f174,plain,(
% 2.30/0.67    spl6_16 <=> r4_tsep_1(sK0,sK2,sK3)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.30/0.67  fof(f973,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~r4_tsep_1(sK0,sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_15 | ~spl6_18 | ~spl6_20 | ~spl6_28 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f972,f256])).
% 2.30/0.67  fof(f256,plain,(
% 2.30/0.67    v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl6_28),
% 2.30/0.67    inference(avatar_component_clause,[],[f255])).
% 2.30/0.67  fof(f255,plain,(
% 2.30/0.67    spl6_28 <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.30/0.67  fof(f972,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~r4_tsep_1(sK0,sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_15 | ~spl6_18 | ~spl6_20 | ~spl6_29 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f971,f260])).
% 2.30/0.67  fof(f260,plain,(
% 2.30/0.67    v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~spl6_29),
% 2.30/0.67    inference(avatar_component_clause,[],[f259])).
% 2.30/0.67  fof(f259,plain,(
% 2.30/0.67    spl6_29 <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 2.30/0.67  fof(f971,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~r4_tsep_1(sK0,sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_15 | ~spl6_18 | ~spl6_20 | spl6_30 | ~spl6_31 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f970,f268])).
% 2.30/0.67  fof(f268,plain,(
% 2.30/0.67    m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~spl6_31),
% 2.30/0.67    inference(avatar_component_clause,[],[f267])).
% 2.30/0.67  fof(f267,plain,(
% 2.30/0.67    spl6_31 <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 2.30/0.67  fof(f970,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~r4_tsep_1(sK0,sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_15 | ~spl6_18 | ~spl6_20 | spl6_30 | ~spl6_76 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f969,f634])).
% 2.30/0.67  fof(f634,plain,(
% 2.30/0.67    v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~spl6_76),
% 2.30/0.67    inference(avatar_component_clause,[],[f633])).
% 2.30/0.67  fof(f633,plain,(
% 2.30/0.67    spl6_76 <=> v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).
% 2.30/0.67  fof(f969,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~r4_tsep_1(sK0,sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_15 | ~spl6_18 | ~spl6_20 | spl6_30 | ~spl6_77 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f968,f638])).
% 2.30/0.67  fof(f638,plain,(
% 2.30/0.67    v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl6_77),
% 2.30/0.67    inference(avatar_component_clause,[],[f637])).
% 2.30/0.67  fof(f637,plain,(
% 2.30/0.67    spl6_77 <=> v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 2.30/0.67  fof(f968,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~r4_tsep_1(sK0,sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_15 | ~spl6_18 | ~spl6_20 | spl6_30 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f967,f265])).
% 2.30/0.67  fof(f265,plain,(
% 2.30/0.67    ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) | spl6_30),
% 2.30/0.67    inference(avatar_component_clause,[],[f263])).
% 2.30/0.67  fof(f263,plain,(
% 2.30/0.67    spl6_30 <=> v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 2.30/0.67  fof(f967,plain,(
% 2.30/0.67    v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~r4_tsep_1(sK0,sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_15 | ~spl6_18 | ~spl6_20 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f966,f186])).
% 2.30/0.67  fof(f186,plain,(
% 2.30/0.67    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl6_18),
% 2.30/0.67    inference(avatar_component_clause,[],[f184])).
% 2.30/0.67  fof(f184,plain,(
% 2.30/0.67    spl6_18 <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 2.30/0.67  fof(f966,plain,(
% 2.30/0.67    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~r4_tsep_1(sK0,sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_15 | ~spl6_20 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f965,f171])).
% 2.30/0.67  fof(f171,plain,(
% 2.30/0.67    v5_pre_topc(sK5,sK3,sK1) | ~spl6_15),
% 2.30/0.67    inference(avatar_component_clause,[],[f169])).
% 2.30/0.67  fof(f169,plain,(
% 2.30/0.67    spl6_15 <=> v5_pre_topc(sK5,sK3,sK1)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.30/0.67  fof(f965,plain,(
% 2.30/0.67    ~v5_pre_topc(sK5,sK3,sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~r4_tsep_1(sK0,sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_20 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f964,f196])).
% 2.30/0.67  fof(f196,plain,(
% 2.30/0.67    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl6_20),
% 2.30/0.67    inference(avatar_component_clause,[],[f194])).
% 2.30/0.67  fof(f194,plain,(
% 2.30/0.67    spl6_20 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 2.30/0.67  fof(f964,plain,(
% 2.30/0.67    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(sK5,sK3,sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~r4_tsep_1(sK0,sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_83)),
% 2.30/0.67    inference(subsumption_resolution,[],[f959,f146])).
% 2.30/0.67  fof(f146,plain,(
% 2.30/0.67    v1_funct_1(sK5) | ~spl6_10),
% 2.30/0.67    inference(avatar_component_clause,[],[f144])).
% 2.30/0.67  fof(f144,plain,(
% 2.30/0.67    spl6_10 <=> v1_funct_1(sK5)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.30/0.67  fof(f959,plain,(
% 2.30/0.67    ~v1_funct_1(sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(sK5,sK3,sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~r4_tsep_1(sK0,sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_83),
% 2.30/0.67    inference(superposition,[],[f76,f664])).
% 2.30/0.67  fof(f664,plain,(
% 2.30/0.67    sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl6_83),
% 2.30/0.67    inference(avatar_component_clause,[],[f662])).
% 2.30/0.67  fof(f662,plain,(
% 2.30/0.67    spl6_83 <=> sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 2.30/0.67  fof(f76,plain,(
% 2.30/0.67    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f38])).
% 2.30/0.67  fof(f38,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.67    inference(flattening,[],[f37])).
% 2.30/0.67  fof(f37,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.67    inference(nnf_transformation,[],[f17])).
% 2.30/0.67  fof(f17,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.67    inference(flattening,[],[f16])).
% 2.30/0.67  fof(f16,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.30/0.67    inference(ennf_transformation,[],[f4])).
% 2.30/0.67  fof(f4,axiom,(
% 2.30/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).
% 2.30/0.67  fof(f1001,plain,(
% 2.30/0.67    spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_78 | ~spl6_94),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f1000])).
% 2.30/0.67  fof(f1000,plain,(
% 2.30/0.67    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_78 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f999,f101])).
% 2.30/0.67  fof(f999,plain,(
% 2.30/0.67    v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_78 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f998,f106])).
% 2.30/0.67  fof(f998,plain,(
% 2.30/0.67    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_78 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f997,f111])).
% 2.30/0.67  fof(f997,plain,(
% 2.30/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_78 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f996,f116])).
% 2.30/0.67  fof(f996,plain,(
% 2.30/0.67    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_78 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f995,f121])).
% 2.30/0.67  fof(f995,plain,(
% 2.30/0.67    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_78 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f994,f126])).
% 2.30/0.67  fof(f994,plain,(
% 2.30/0.67    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_11 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_78 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f993,f786])).
% 2.30/0.67  fof(f786,plain,(
% 2.30/0.67    m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~spl6_94),
% 2.30/0.67    inference(avatar_component_clause,[],[f785])).
% 2.30/0.67  fof(f785,plain,(
% 2.30/0.67    spl6_94 <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 2.30/0.67  fof(f993,plain,(
% 2.30/0.67    ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_11 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_78)),
% 2.30/0.67    inference(subsumption_resolution,[],[f992,f151])).
% 2.30/0.67  fof(f992,plain,(
% 2.30/0.67    ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_78)),
% 2.30/0.67    inference(subsumption_resolution,[],[f991,f256])).
% 2.30/0.67  fof(f991,plain,(
% 2.30/0.67    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_29 | ~spl6_31 | spl6_78)),
% 2.30/0.67    inference(subsumption_resolution,[],[f990,f260])).
% 2.30/0.67  fof(f990,plain,(
% 2.30/0.67    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_31 | spl6_78)),
% 2.30/0.67    inference(subsumption_resolution,[],[f987,f268])).
% 2.30/0.67  fof(f987,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_78),
% 2.30/0.67    inference(resolution,[],[f643,f84])).
% 2.30/0.67  fof(f84,plain,(
% 2.30/0.67    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f25])).
% 2.30/0.67  fof(f25,plain,(
% 2.30/0.67    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.67    inference(flattening,[],[f24])).
% 2.30/0.67  fof(f24,plain,(
% 2.30/0.67    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.30/0.67    inference(ennf_transformation,[],[f3])).
% 2.30/0.67  fof(f3,axiom,(
% 2.30/0.67    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.30/0.67  fof(f643,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | spl6_78),
% 2.30/0.67    inference(avatar_component_clause,[],[f641])).
% 2.30/0.67  fof(f641,plain,(
% 2.30/0.67    spl6_78 <=> m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 2.30/0.67  fof(f955,plain,(
% 2.30/0.67    spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_81 | ~spl6_94),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f954])).
% 2.30/0.67  fof(f954,plain,(
% 2.30/0.67    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_81 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f953,f101])).
% 2.30/0.67  fof(f953,plain,(
% 2.30/0.67    v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_81 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f952,f106])).
% 2.30/0.67  fof(f952,plain,(
% 2.30/0.67    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_81 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f951,f111])).
% 2.30/0.67  fof(f951,plain,(
% 2.30/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_81 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f950,f116])).
% 2.30/0.67  fof(f950,plain,(
% 2.30/0.67    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_81 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f949,f121])).
% 2.30/0.67  fof(f949,plain,(
% 2.30/0.67    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_12 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_81 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f948,f126])).
% 2.30/0.67  fof(f948,plain,(
% 2.30/0.67    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_12 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_81 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f947,f786])).
% 2.30/0.67  fof(f947,plain,(
% 2.30/0.67    ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_12 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_81)),
% 2.30/0.67    inference(subsumption_resolution,[],[f946,f156])).
% 2.30/0.67  fof(f946,plain,(
% 2.30/0.67    ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_81)),
% 2.30/0.67    inference(subsumption_resolution,[],[f945,f256])).
% 2.30/0.67  fof(f945,plain,(
% 2.30/0.67    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_29 | ~spl6_31 | spl6_81)),
% 2.30/0.67    inference(subsumption_resolution,[],[f944,f260])).
% 2.30/0.67  fof(f944,plain,(
% 2.30/0.67    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_31 | spl6_81)),
% 2.30/0.67    inference(subsumption_resolution,[],[f942,f268])).
% 2.30/0.67  fof(f942,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_81),
% 2.30/0.67    inference(resolution,[],[f656,f83])).
% 2.30/0.67  fof(f83,plain,(
% 2.30/0.67    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f25])).
% 2.30/0.67  fof(f656,plain,(
% 2.30/0.67    ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) | spl6_81),
% 2.30/0.67    inference(avatar_component_clause,[],[f654])).
% 2.30/0.67  fof(f654,plain,(
% 2.30/0.67    spl6_81 <=> v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).
% 2.30/0.67  fof(f929,plain,(
% 2.30/0.67    spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_82 | ~spl6_94),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f926])).
% 2.30/0.67  fof(f926,plain,(
% 2.30/0.67    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_28 | ~spl6_29 | ~spl6_31 | spl6_82 | ~spl6_94)),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f101,f106,f111,f116,f121,f126,f156,f786,f256,f260,f660,f268,f84])).
% 2.30/0.67  fof(f660,plain,(
% 2.30/0.67    ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl6_82),
% 2.30/0.67    inference(avatar_component_clause,[],[f658])).
% 2.30/0.67  fof(f658,plain,(
% 2.30/0.67    spl6_82 <=> m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).
% 2.30/0.67  fof(f920,plain,(
% 2.30/0.67    spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f919])).
% 2.30/0.67  fof(f919,plain,(
% 2.30/0.67    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f918,f101])).
% 2.30/0.67  fof(f918,plain,(
% 2.30/0.67    v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f917,f106])).
% 2.30/0.67  fof(f917,plain,(
% 2.30/0.67    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f916,f111])).
% 2.30/0.67  fof(f916,plain,(
% 2.30/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f915,f116])).
% 2.30/0.67  fof(f915,plain,(
% 2.30/0.67    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f914,f121])).
% 2.30/0.67  fof(f914,plain,(
% 2.30/0.67    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f913,f126])).
% 2.30/0.67  fof(f913,plain,(
% 2.30/0.67    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f912,f131])).
% 2.30/0.67  fof(f912,plain,(
% 2.30/0.67    v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f911,f151])).
% 2.30/0.67  fof(f911,plain,(
% 2.30/0.67    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f910,f136])).
% 2.30/0.67  fof(f910,plain,(
% 2.30/0.67    v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f909,f156])).
% 2.30/0.67  fof(f909,plain,(
% 2.30/0.67    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f908,f141])).
% 2.30/0.67  fof(f141,plain,(
% 2.30/0.67    v1_funct_1(sK4) | ~spl6_9),
% 2.30/0.67    inference(avatar_component_clause,[],[f139])).
% 2.30/0.67  fof(f139,plain,(
% 2.30/0.67    spl6_9 <=> v1_funct_1(sK4)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.30/0.67  fof(f908,plain,(
% 2.30/0.67    ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f907,f181])).
% 2.30/0.67  fof(f181,plain,(
% 2.30/0.67    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl6_17),
% 2.30/0.67    inference(avatar_component_clause,[],[f179])).
% 2.30/0.67  fof(f179,plain,(
% 2.30/0.67    spl6_17 <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 2.30/0.67  fof(f907,plain,(
% 2.30/0.67    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f906,f191])).
% 2.30/0.67  fof(f906,plain,(
% 2.30/0.67    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_18 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f905,f146])).
% 2.30/0.67  fof(f905,plain,(
% 2.30/0.67    ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_18 | ~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f904,f186])).
% 2.30/0.67  fof(f904,plain,(
% 2.30/0.67    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_20 | spl6_31)),
% 2.30/0.67    inference(subsumption_resolution,[],[f902,f196])).
% 2.30/0.67  fof(f902,plain,(
% 2.30/0.67    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_31),
% 2.30/0.67    inference(resolution,[],[f269,f87])).
% 2.30/0.67  fof(f87,plain,(
% 2.30/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f27])).
% 2.30/0.67  fof(f27,plain,(
% 2.30/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.67    inference(flattening,[],[f26])).
% 2.30/0.67  fof(f26,plain,(
% 2.30/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.30/0.67    inference(ennf_transformation,[],[f2])).
% 2.30/0.67  fof(f2,axiom,(
% 2.30/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 2.30/0.67  fof(f269,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | spl6_31),
% 2.30/0.67    inference(avatar_component_clause,[],[f267])).
% 2.30/0.67  fof(f895,plain,(
% 2.30/0.67    ~spl6_31 | spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | spl6_77 | ~spl6_94),
% 2.30/0.67    inference(avatar_split_clause,[],[f882,f785,f637,f259,f255,f149,f124,f119,f114,f109,f104,f99,f267])).
% 2.30/0.67  fof(f882,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | spl6_77 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f881,f101])).
% 2.30/0.67  fof(f881,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | spl6_77 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f880,f106])).
% 2.30/0.67  fof(f880,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | spl6_77 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f879,f111])).
% 2.30/0.67  fof(f879,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | spl6_77 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f878,f116])).
% 2.30/0.67  fof(f878,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | spl6_77 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f877,f121])).
% 2.30/0.67  fof(f877,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_11 | ~spl6_28 | ~spl6_29 | spl6_77 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f876,f126])).
% 2.30/0.67  fof(f876,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_11 | ~spl6_28 | ~spl6_29 | spl6_77 | ~spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f875,f786])).
% 2.30/0.67  fof(f875,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_11 | ~spl6_28 | ~spl6_29 | spl6_77)),
% 2.30/0.67    inference(subsumption_resolution,[],[f874,f151])).
% 2.30/0.67  fof(f874,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_28 | ~spl6_29 | spl6_77)),
% 2.30/0.67    inference(subsumption_resolution,[],[f873,f256])).
% 2.30/0.67  fof(f873,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_29 | spl6_77)),
% 2.30/0.67    inference(subsumption_resolution,[],[f871,f260])).
% 2.30/0.67  fof(f871,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_77),
% 2.30/0.67    inference(resolution,[],[f639,f83])).
% 2.30/0.67  fof(f639,plain,(
% 2.30/0.67    ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | spl6_77),
% 2.30/0.67    inference(avatar_component_clause,[],[f637])).
% 2.30/0.67  fof(f843,plain,(
% 2.30/0.67    ~spl6_12 | spl6_80 | ~spl6_95),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f842])).
% 2.30/0.67  fof(f842,plain,(
% 2.30/0.67    $false | (~spl6_12 | spl6_80 | ~spl6_95)),
% 2.30/0.67    inference(subsumption_resolution,[],[f832,f652])).
% 2.30/0.67  fof(f652,plain,(
% 2.30/0.67    ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | spl6_80),
% 2.30/0.67    inference(avatar_component_clause,[],[f650])).
% 2.30/0.67  fof(f650,plain,(
% 2.30/0.67    spl6_80 <=> v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 2.30/0.67  fof(f832,plain,(
% 2.30/0.67    v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_12 | ~spl6_95)),
% 2.30/0.67    inference(resolution,[],[f790,f156])).
% 2.30/0.67  fof(f790,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))) ) | ~spl6_95),
% 2.30/0.67    inference(avatar_component_clause,[],[f789])).
% 2.30/0.67  fof(f789,plain,(
% 2.30/0.67    spl6_95 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).
% 2.30/0.67  fof(f841,plain,(
% 2.30/0.67    ~spl6_11 | spl6_76 | ~spl6_95),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f840])).
% 2.30/0.67  fof(f840,plain,(
% 2.30/0.67    $false | (~spl6_11 | spl6_76 | ~spl6_95)),
% 2.30/0.67    inference(subsumption_resolution,[],[f831,f635])).
% 2.30/0.67  fof(f635,plain,(
% 2.30/0.67    ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | spl6_76),
% 2.30/0.67    inference(avatar_component_clause,[],[f633])).
% 2.30/0.67  fof(f831,plain,(
% 2.30/0.67    v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_11 | ~spl6_95)),
% 2.30/0.67    inference(resolution,[],[f790,f151])).
% 2.30/0.67  fof(f809,plain,(
% 2.30/0.67    spl6_7 | spl6_8 | ~spl6_11 | ~spl6_12 | ~spl6_38 | spl6_94),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f808])).
% 2.30/0.67  fof(f808,plain,(
% 2.30/0.67    $false | (spl6_7 | spl6_8 | ~spl6_11 | ~spl6_12 | ~spl6_38 | spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f807,f151])).
% 2.30/0.67  fof(f807,plain,(
% 2.30/0.67    ~m1_pre_topc(sK2,sK0) | (spl6_7 | spl6_8 | ~spl6_12 | ~spl6_38 | spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f806,f131])).
% 2.30/0.67  fof(f806,plain,(
% 2.30/0.67    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | (spl6_8 | ~spl6_12 | ~spl6_38 | spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f805,f156])).
% 2.30/0.67  fof(f805,plain,(
% 2.30/0.67    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | (spl6_8 | ~spl6_38 | spl6_94)),
% 2.30/0.67    inference(subsumption_resolution,[],[f799,f136])).
% 2.30/0.67  fof(f799,plain,(
% 2.30/0.67    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | (~spl6_38 | spl6_94)),
% 2.30/0.67    inference(resolution,[],[f787,f361])).
% 2.30/0.67  fof(f361,plain,(
% 2.30/0.67    ( ! [X4,X5] : (m1_pre_topc(k1_tsep_1(sK0,X4,X5),sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0)) ) | ~spl6_38),
% 2.30/0.67    inference(avatar_component_clause,[],[f360])).
% 2.30/0.67  fof(f360,plain,(
% 2.30/0.67    spl6_38 <=> ! [X5,X4] : (~m1_pre_topc(X4,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X4) | m1_pre_topc(k1_tsep_1(sK0,X4,X5),sK0))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 2.30/0.67  fof(f787,plain,(
% 2.30/0.67    ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | spl6_94),
% 2.30/0.67    inference(avatar_component_clause,[],[f785])).
% 2.30/0.67  fof(f791,plain,(
% 2.30/0.67    ~spl6_94 | spl6_95 | spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90),
% 2.30/0.67    inference(avatar_split_clause,[],[f745,f717,f259,f194,f189,f184,f179,f154,f149,f144,f139,f134,f129,f124,f119,f114,f109,f104,f99,f789,f785])).
% 2.30/0.67  fof(f717,plain,(
% 2.30/0.67    spl6_90 <=> ! [X5,X4] : (~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(X4),u1_struct_0(sK1)) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).
% 2.30/0.67  fof(f745,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f744,f101])).
% 2.30/0.67  fof(f744,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f743,f106])).
% 2.30/0.67  fof(f743,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f742,f111])).
% 2.30/0.67  fof(f742,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f741,f116])).
% 2.30/0.67  fof(f741,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f740,f121])).
% 2.30/0.67  fof(f740,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f739,f126])).
% 2.30/0.67  fof(f739,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f738,f131])).
% 2.30/0.67  fof(f738,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f737,f151])).
% 2.30/0.67  fof(f737,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f736,f136])).
% 2.30/0.67  fof(f736,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f735,f156])).
% 2.30/0.67  fof(f735,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_9 | ~spl6_10 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f734,f141])).
% 2.30/0.67  fof(f734,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_10 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f733,f181])).
% 2.30/0.67  fof(f733,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_10 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f732,f191])).
% 2.30/0.67  fof(f732,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_10 | ~spl6_18 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f731,f146])).
% 2.30/0.67  fof(f731,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_18 | ~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f730,f186])).
% 2.30/0.67  fof(f730,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_20 | ~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f729,f196])).
% 2.30/0.67  fof(f729,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_29 | ~spl6_90)),
% 2.30/0.67    inference(subsumption_resolution,[],[f728,f260])).
% 2.30/0.67  fof(f728,plain,(
% 2.30/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_90),
% 2.30/0.67    inference(resolution,[],[f718,f87])).
% 2.30/0.67  fof(f718,plain,(
% 2.30/0.67    ( ! [X4,X5] : (~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(X4),u1_struct_0(sK1)) | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))) ) | ~spl6_90),
% 2.30/0.67    inference(avatar_component_clause,[],[f717])).
% 2.30/0.67  fof(f719,plain,(
% 2.30/0.67    spl6_90 | ~spl6_28 | ~spl6_65),
% 2.30/0.67    inference(avatar_split_clause,[],[f580,f567,f255,f717])).
% 2.30/0.67  fof(f567,plain,(
% 2.30/0.67    spl6_65 <=> ! [X3,X5,X4] : (~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3)))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 2.30/0.67  fof(f580,plain,(
% 2.30/0.67    ( ! [X4,X5] : (~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(X4),u1_struct_0(sK1)) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))) ) | (~spl6_28 | ~spl6_65)),
% 2.30/0.67    inference(resolution,[],[f568,f256])).
% 2.30/0.67  fof(f568,plain,(
% 2.30/0.67    ( ! [X4,X5,X3] : (~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1)) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3))) ) | ~spl6_65),
% 2.30/0.67    inference(avatar_component_clause,[],[f567])).
% 2.30/0.67  fof(f665,plain,(
% 2.30/0.67    ~spl6_80 | ~spl6_81 | ~spl6_82 | spl6_83 | ~spl6_10 | ~spl6_18 | ~spl6_20 | ~spl6_41),
% 2.30/0.67    inference(avatar_split_clause,[],[f420,f401,f194,f184,f144,f662,f658,f654,f650])).
% 2.30/0.67  fof(f401,plain,(
% 2.30/0.67    spl6_41 <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 2.30/0.67  fof(f420,plain,(
% 2.30/0.67    sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_10 | ~spl6_18 | ~spl6_20 | ~spl6_41)),
% 2.30/0.67    inference(subsumption_resolution,[],[f419,f146])).
% 2.30/0.67  fof(f419,plain,(
% 2.30/0.67    sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_1(sK5) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_18 | ~spl6_20 | ~spl6_41)),
% 2.30/0.67    inference(subsumption_resolution,[],[f418,f186])).
% 2.30/0.67  fof(f418,plain,(
% 2.30/0.67    sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_20 | ~spl6_41)),
% 2.30/0.67    inference(subsumption_resolution,[],[f417,f196])).
% 2.30/0.67  fof(f417,plain,(
% 2.30/0.67    sK5 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~spl6_41),
% 2.30/0.67    inference(resolution,[],[f403,f80])).
% 2.30/0.67  fof(f80,plain,(
% 2.30/0.67    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f39])).
% 2.30/0.67  fof(f39,plain,(
% 2.30/0.67    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.30/0.67    inference(nnf_transformation,[],[f23])).
% 2.30/0.67  fof(f23,plain,(
% 2.30/0.67    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.30/0.67    inference(flattening,[],[f22])).
% 2.30/0.67  fof(f22,plain,(
% 2.30/0.67    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.30/0.67    inference(ennf_transformation,[],[f1])).
% 2.30/0.67  fof(f1,axiom,(
% 2.30/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.30/0.67  fof(f403,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~spl6_41),
% 2.30/0.67    inference(avatar_component_clause,[],[f401])).
% 2.30/0.67  fof(f648,plain,(
% 2.30/0.67    ~spl6_76 | ~spl6_77 | ~spl6_78 | spl6_79 | ~spl6_9 | ~spl6_17 | ~spl6_19 | ~spl6_40),
% 2.30/0.67    inference(avatar_split_clause,[],[f412,f393,f189,f179,f139,f645,f641,f637,f633])).
% 2.30/0.67  fof(f393,plain,(
% 2.30/0.67    spl6_40 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 2.30/0.67  fof(f412,plain,(
% 2.30/0.67    sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_9 | ~spl6_17 | ~spl6_19 | ~spl6_40)),
% 2.30/0.67    inference(subsumption_resolution,[],[f411,f141])).
% 2.30/0.67  fof(f411,plain,(
% 2.30/0.67    sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_1(sK4) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_17 | ~spl6_19 | ~spl6_40)),
% 2.30/0.67    inference(subsumption_resolution,[],[f410,f181])).
% 2.30/0.67  fof(f410,plain,(
% 2.30/0.67    sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_19 | ~spl6_40)),
% 2.30/0.67    inference(subsumption_resolution,[],[f409,f191])).
% 2.30/0.67  fof(f409,plain,(
% 2.30/0.67    sK4 = k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~spl6_40),
% 2.30/0.67    inference(resolution,[],[f395,f80])).
% 2.30/0.67  fof(f395,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~spl6_40),
% 2.30/0.67    inference(avatar_component_clause,[],[f393])).
% 2.30/0.67  fof(f569,plain,(
% 2.30/0.67    spl6_65 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_44),
% 2.30/0.67    inference(avatar_split_clause,[],[f447,f427,f124,f119,f114,f567])).
% 2.30/0.67  fof(f427,plain,(
% 2.30/0.67    spl6_44 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0)))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 2.30/0.67  fof(f447,plain,(
% 2.30/0.67    ( ! [X4,X5,X3] : (~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3))) ) | (spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_44)),
% 2.30/0.67    inference(subsumption_resolution,[],[f446,f116])).
% 2.30/0.67  fof(f446,plain,(
% 2.30/0.67    ( ! [X4,X5,X3] : (~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3))) ) | (~spl6_5 | ~spl6_6 | ~spl6_44)),
% 2.30/0.67    inference(subsumption_resolution,[],[f443,f121])).
% 2.30/0.67  fof(f443,plain,(
% 2.30/0.67    ( ! [X4,X5,X3] : (~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X5,sK0) | ~m1_pre_topc(X4,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK0,sK1,X4,X5,X3))) ) | (~spl6_6 | ~spl6_44)),
% 2.30/0.67    inference(resolution,[],[f428,f126])).
% 2.30/0.67  fof(f428,plain,(
% 2.30/0.67    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X2) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0))) ) | ~spl6_44),
% 2.30/0.67    inference(avatar_component_clause,[],[f427])).
% 2.30/0.67  fof(f429,plain,(
% 2.30/0.67    spl6_44 | spl6_1 | ~spl6_2 | ~spl6_3),
% 2.30/0.67    inference(avatar_split_clause,[],[f242,f109,f104,f99,f427])).
% 2.30/0.67  fof(f242,plain,(
% 2.30/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 2.30/0.67    inference(subsumption_resolution,[],[f241,f101])).
% 2.30/0.67  fof(f241,plain,(
% 2.30/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3)),
% 2.30/0.67    inference(subsumption_resolution,[],[f239,f106])).
% 2.30/0.67  fof(f239,plain,(
% 2.30/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v1_funct_1(k3_tmap_1(sK0,X2,X1,X3,X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_3),
% 2.30/0.67    inference(resolution,[],[f82,f111])).
% 2.30/0.67  fof(f82,plain,(
% 2.30/0.67    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f25])).
% 2.30/0.67  fof(f404,plain,(
% 2.30/0.67    spl6_41 | spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23),
% 2.30/0.67    inference(avatar_split_clause,[],[f380,f213,f194,f189,f184,f179,f159,f154,f149,f144,f139,f134,f129,f124,f119,f114,f109,f104,f99,f401])).
% 2.30/0.67  fof(f159,plain,(
% 2.30/0.67    spl6_13 <=> r1_tsep_1(sK2,sK3)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.30/0.67  fof(f213,plain,(
% 2.30/0.67    spl6_23 <=> r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 2.30/0.67  fof(f380,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f379,f101])).
% 2.30/0.67  fof(f379,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f378,f106])).
% 2.30/0.67  fof(f378,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f377,f111])).
% 2.30/0.67  fof(f377,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f376,f116])).
% 2.30/0.67  fof(f376,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f375,f121])).
% 2.30/0.67  fof(f375,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f374,f126])).
% 2.30/0.67  fof(f374,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f373,f131])).
% 2.30/0.67  fof(f373,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f372,f151])).
% 2.30/0.67  fof(f372,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f371,f136])).
% 2.30/0.67  fof(f371,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f370,f156])).
% 2.30/0.67  fof(f370,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f369,f161])).
% 2.30/0.67  fof(f161,plain,(
% 2.30/0.67    ~r1_tsep_1(sK2,sK3) | spl6_13),
% 2.30/0.67    inference(avatar_component_clause,[],[f159])).
% 2.30/0.67  fof(f369,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f368,f141])).
% 2.30/0.67  fof(f368,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f367,f181])).
% 2.30/0.67  fof(f367,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f366,f191])).
% 2.30/0.67  fof(f366,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_18 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f365,f146])).
% 2.30/0.67  fof(f365,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_18 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f364,f186])).
% 2.30/0.67  fof(f364,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f363,f196])).
% 2.30/0.67  fof(f363,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_23),
% 2.30/0.67    inference(resolution,[],[f65,f215])).
% 2.30/0.67  fof(f215,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) | ~spl6_23),
% 2.30/0.67    inference(avatar_component_clause,[],[f213])).
% 2.30/0.67  fof(f65,plain,(
% 2.30/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f36])).
% 2.30/0.67  fof(f36,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) & (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.67    inference(flattening,[],[f35])).
% 2.30/0.67  fof(f35,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) & (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.67    inference(nnf_transformation,[],[f15])).
% 2.30/0.67  fof(f15,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.67    inference(flattening,[],[f14])).
% 2.30/0.67  fof(f14,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.30/0.67    inference(ennf_transformation,[],[f5])).
% 2.30/0.67  fof(f5,axiom,(
% 2.30/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))))))))))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_tmap_1)).
% 2.30/0.67  fof(f396,plain,(
% 2.30/0.67    spl6_40 | spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23),
% 2.30/0.67    inference(avatar_split_clause,[],[f358,f213,f194,f189,f184,f179,f159,f154,f149,f144,f139,f134,f129,f124,f119,f114,f109,f104,f99,f393])).
% 2.30/0.67  fof(f358,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f357,f101])).
% 2.30/0.67  fof(f357,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f356,f106])).
% 2.30/0.67  fof(f356,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f355,f111])).
% 2.30/0.67  fof(f355,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f354,f116])).
% 2.30/0.67  fof(f354,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f353,f121])).
% 2.30/0.67  fof(f353,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f352,f126])).
% 2.30/0.67  fof(f352,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f351,f131])).
% 2.30/0.67  fof(f351,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f350,f151])).
% 2.30/0.67  fof(f350,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f349,f136])).
% 2.30/0.67  fof(f349,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_12 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f348,f156])).
% 2.30/0.67  fof(f348,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | spl6_13 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f347,f161])).
% 2.30/0.67  fof(f347,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f346,f141])).
% 2.30/0.67  fof(f346,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f345,f181])).
% 2.30/0.67  fof(f345,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f344,f191])).
% 2.30/0.67  fof(f344,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_18 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f343,f146])).
% 2.30/0.67  fof(f343,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_18 | ~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f342,f186])).
% 2.30/0.67  fof(f342,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_20 | ~spl6_23)),
% 2.30/0.67    inference(subsumption_resolution,[],[f341,f196])).
% 2.30/0.67  fof(f341,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | r1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_23),
% 2.30/0.67    inference(resolution,[],[f64,f215])).
% 2.30/0.67  fof(f64,plain,(
% 2.30/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f36])).
% 2.30/0.67  fof(f362,plain,(
% 2.30/0.67    spl6_38 | spl6_1 | ~spl6_3 | ~spl6_34),
% 2.30/0.67    inference(avatar_split_clause,[],[f332,f319,f109,f99,f360])).
% 2.30/0.67  fof(f319,plain,(
% 2.30/0.67    spl6_34 <=> ! [X1,X0,X2] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X2,X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X2) | m1_pre_topc(k1_tsep_1(sK0,X2,X0),X1))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 2.30/0.67  fof(f332,plain,(
% 2.30/0.67    ( ! [X4,X5] : (~m1_pre_topc(X4,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X4) | m1_pre_topc(k1_tsep_1(sK0,X4,X5),sK0)) ) | (spl6_1 | ~spl6_3 | ~spl6_34)),
% 2.30/0.67    inference(subsumption_resolution,[],[f331,f111])).
% 2.30/0.67  fof(f331,plain,(
% 2.30/0.67    ( ! [X4,X5] : (~m1_pre_topc(X4,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X4) | m1_pre_topc(k1_tsep_1(sK0,X4,X5),sK0) | ~l1_pre_topc(sK0)) ) | (spl6_1 | ~spl6_34)),
% 2.30/0.67    inference(subsumption_resolution,[],[f328,f101])).
% 2.30/0.67  fof(f328,plain,(
% 2.30/0.67    ( ! [X4,X5] : (~m1_pre_topc(X4,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | v2_struct_0(sK0) | v2_struct_0(X4) | m1_pre_topc(k1_tsep_1(sK0,X4,X5),sK0) | ~l1_pre_topc(sK0)) ) | ~spl6_34),
% 2.30/0.67    inference(resolution,[],[f320,f62])).
% 2.30/0.67  fof(f62,plain,(
% 2.30/0.67    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f13])).
% 2.30/0.67  fof(f13,plain,(
% 2.30/0.67    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.30/0.67    inference(ennf_transformation,[],[f7])).
% 2.30/0.67  fof(f7,axiom,(
% 2.30/0.67    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.30/0.67  fof(f320,plain,(
% 2.30/0.67    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X1) | v2_struct_0(X2) | m1_pre_topc(k1_tsep_1(sK0,X2,X0),X1)) ) | ~spl6_34),
% 2.30/0.67    inference(avatar_component_clause,[],[f319])).
% 2.30/0.67  fof(f321,plain,(
% 2.30/0.67    spl6_34 | spl6_1 | ~spl6_2 | ~spl6_3),
% 2.30/0.67    inference(avatar_split_clause,[],[f235,f109,f104,f99,f319])).
% 2.30/0.67  fof(f235,plain,(
% 2.30/0.67    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X2,X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X2) | m1_pre_topc(k1_tsep_1(sK0,X2,X0),X1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 2.30/0.67    inference(subsumption_resolution,[],[f234,f101])).
% 2.30/0.67  fof(f234,plain,(
% 2.30/0.67    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X2,X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X2) | m1_pre_topc(k1_tsep_1(sK0,X2,X0),X1) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3)),
% 2.30/0.67    inference(subsumption_resolution,[],[f232,f106])).
% 2.30/0.67  fof(f232,plain,(
% 2.30/0.67    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X2,X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_struct_0(X2) | m1_pre_topc(k1_tsep_1(sK0,X2,X0),X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_3),
% 2.30/0.67    inference(resolution,[],[f230,f111])).
% 2.30/0.67  fof(f230,plain,(
% 2.30/0.67    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | v2_struct_0(X1) | m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.67    inference(subsumption_resolution,[],[f229,f79])).
% 2.30/0.67  fof(f79,plain,(
% 2.30/0.67    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,X0) | ~v2_pre_topc(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f21])).
% 2.30/0.67  fof(f21,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.30/0.67    inference(flattening,[],[f20])).
% 2.30/0.67  fof(f20,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.30/0.67    inference(ennf_transformation,[],[f8])).
% 2.30/0.67  fof(f8,axiom,(
% 2.30/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.30/0.67  fof(f229,plain,(
% 2.30/0.67    ( ! [X2,X0,X3,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.67    inference(subsumption_resolution,[],[f78,f79])).
% 2.30/0.67  fof(f78,plain,(
% 2.30/0.67    ( ! [X2,X0,X3,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f19])).
% 2.30/0.67  fof(f19,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.67    inference(flattening,[],[f18])).
% 2.30/0.67  fof(f18,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | (~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.30/0.67    inference(ennf_transformation,[],[f6])).
% 2.30/0.67  fof(f6,axiom,(
% 2.30/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).
% 2.30/0.67  fof(f315,plain,(
% 2.30/0.67    spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f314])).
% 2.30/0.67  fof(f314,plain,(
% 2.30/0.67    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f313,f101])).
% 2.30/0.67  fof(f313,plain,(
% 2.30/0.67    v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f312,f106])).
% 2.30/0.67  fof(f312,plain,(
% 2.30/0.67    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f311,f111])).
% 2.30/0.67  fof(f311,plain,(
% 2.30/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f310,f116])).
% 2.30/0.67  fof(f310,plain,(
% 2.30/0.67    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f309,f121])).
% 2.30/0.67  fof(f309,plain,(
% 2.30/0.67    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f308,f126])).
% 2.30/0.67  fof(f308,plain,(
% 2.30/0.67    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f307,f131])).
% 2.30/0.67  fof(f307,plain,(
% 2.30/0.67    v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f306,f151])).
% 2.30/0.67  fof(f306,plain,(
% 2.30/0.67    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f305,f136])).
% 2.30/0.67  fof(f305,plain,(
% 2.30/0.67    v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f304,f156])).
% 2.30/0.67  fof(f304,plain,(
% 2.30/0.67    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f303,f141])).
% 2.30/0.67  fof(f303,plain,(
% 2.30/0.67    ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f302,f181])).
% 2.30/0.67  fof(f302,plain,(
% 2.30/0.67    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f301,f191])).
% 2.30/0.67  fof(f301,plain,(
% 2.30/0.67    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | ~spl6_18 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f300,f146])).
% 2.30/0.67  fof(f300,plain,(
% 2.30/0.67    ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_18 | ~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f299,f186])).
% 2.30/0.67  fof(f299,plain,(
% 2.30/0.67    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_20 | spl6_29)),
% 2.30/0.67    inference(subsumption_resolution,[],[f297,f196])).
% 2.30/0.67  fof(f297,plain,(
% 2.30/0.67    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_29),
% 2.30/0.67    inference(resolution,[],[f86,f261])).
% 2.30/0.67  fof(f261,plain,(
% 2.30/0.67    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | spl6_29),
% 2.30/0.67    inference(avatar_component_clause,[],[f259])).
% 2.30/0.67  fof(f86,plain,(
% 2.30/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f27])).
% 2.30/0.67  fof(f274,plain,(
% 2.30/0.67    spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_28),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f271])).
% 2.30/0.67  fof(f271,plain,(
% 2.30/0.67    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_20 | spl6_28)),
% 2.30/0.67    inference(unit_resulting_resolution,[],[f101,f106,f146,f116,f121,f126,f131,f141,f136,f111,f151,f156,f181,f257,f191,f186,f196,f85])).
% 2.30/0.67  fof(f85,plain,(
% 2.30/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f27])).
% 2.30/0.67  fof(f257,plain,(
% 2.30/0.67    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | spl6_28),
% 2.30/0.67    inference(avatar_component_clause,[],[f255])).
% 2.30/0.67  fof(f270,plain,(
% 2.30/0.67    ~spl6_28 | ~spl6_29 | ~spl6_30 | ~spl6_31),
% 2.30/0.67    inference(avatar_split_clause,[],[f61,f267,f263,f259,f255])).
% 2.30/0.67  fof(f61,plain,(
% 2.30/0.67    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f34,plain,(
% 2.30/0.67    ((((((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) & r4_tsep_1(sK0,sK2,sK3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(sK5,sK3,sK1) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4)) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.30/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f33,f32,f31,f30,f29,f28])).
% 2.30/0.67  fof(f28,plain,(
% 2.30/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5))) & r4_tsep_1(sK0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK0,X1,X2,k2_tsep_1(sK0,X2,X3),X4),k3_tmap_1(sK0,X1,X3,k2_tsep_1(sK0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.30/0.67    introduced(choice_axiom,[])).
% 2.30/0.67  fof(f29,plain,(
% 2.30/0.67    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5))) & r4_tsep_1(sK0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK0,X1,X2,k2_tsep_1(sK0,X2,X3),X4),k3_tmap_1(sK0,X1,X3,k2_tsep_1(sK0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5))) & r4_tsep_1(sK0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,X2,X3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X2,k2_tsep_1(sK0,X2,X3),X4),k3_tmap_1(sK0,sK1,X3,k2_tsep_1(sK0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.30/0.67    introduced(choice_axiom,[])).
% 2.30/0.67  fof(f30,plain,(
% 2.30/0.67    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_tsep_1(sK0,X2,X3),sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5))) & r4_tsep_1(sK0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,X2,X3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X2,k2_tsep_1(sK0,X2,X3),X4),k3_tmap_1(sK0,sK1,X3,k2_tsep_1(sK0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_tsep_1(sK0,sK2,X3),sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5))) & r4_tsep_1(sK0,sK2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,X3),X4),k3_tmap_1(sK0,sK1,X3,k2_tsep_1(sK0,sK2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & ~r1_tsep_1(sK2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 2.30/0.67    introduced(choice_axiom,[])).
% 2.30/0.67  fof(f31,plain,(
% 2.30/0.67    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_tsep_1(sK0,sK2,X3),sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5))) & r4_tsep_1(sK0,sK2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,X3),X4),k3_tmap_1(sK0,sK1,X3,k2_tsep_1(sK0,sK2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & ~r1_tsep_1(sK2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5))) & r4_tsep_1(sK0,sK2,sK3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),X4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(X5,sK3,sK1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 2.30/0.67    introduced(choice_axiom,[])).
% 2.30/0.67  fof(f32,plain,(
% 2.30/0.67    ? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5))) & r4_tsep_1(sK0,sK2,sK3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),X4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(X5,sK3,sK1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5))) & r4_tsep_1(sK0,sK2,sK3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(X5,sK3,sK1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 2.30/0.67    introduced(choice_axiom,[])).
% 2.30/0.67  fof(f33,plain,(
% 2.30/0.67    ? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5))) & r4_tsep_1(sK0,sK2,sK3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(X5,sK3,sK1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) & r4_tsep_1(sK0,sK2,sK3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(sK5,sK3,sK1) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 2.30/0.67    introduced(choice_axiom,[])).
% 2.30/0.67  fof(f12,plain,(
% 2.30/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.30/0.67    inference(flattening,[],[f11])).
% 2.30/0.67  fof(f11,plain,(
% 2.30/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & ~r1_tsep_1(X2,X3)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.30/0.67    inference(ennf_transformation,[],[f10])).
% 2.30/0.67  fof(f10,negated_conjecture,(
% 2.30/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 2.30/0.67    inference(negated_conjecture,[],[f9])).
% 2.30/0.67  fof(f9,conjecture,(
% 2.30/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_tmap_1)).
% 2.30/0.67  fof(f216,plain,(
% 2.30/0.67    spl6_23),
% 2.30/0.67    inference(avatar_split_clause,[],[f59,f213])).
% 2.30/0.67  fof(f59,plain,(
% 2.30/0.67    r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5))),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f197,plain,(
% 2.30/0.67    spl6_20),
% 2.30/0.67    inference(avatar_split_clause,[],[f58,f194])).
% 2.30/0.67  fof(f58,plain,(
% 2.30/0.67    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f192,plain,(
% 2.30/0.67    spl6_19),
% 2.30/0.67    inference(avatar_split_clause,[],[f54,f189])).
% 2.30/0.67  fof(f54,plain,(
% 2.30/0.67    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f187,plain,(
% 2.30/0.67    spl6_18),
% 2.30/0.67    inference(avatar_split_clause,[],[f56,f184])).
% 2.30/0.67  fof(f56,plain,(
% 2.30/0.67    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f182,plain,(
% 2.30/0.67    spl6_17),
% 2.30/0.67    inference(avatar_split_clause,[],[f52,f179])).
% 2.30/0.67  fof(f52,plain,(
% 2.30/0.67    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f177,plain,(
% 2.30/0.67    spl6_16),
% 2.30/0.67    inference(avatar_split_clause,[],[f60,f174])).
% 2.30/0.67  fof(f60,plain,(
% 2.30/0.67    r4_tsep_1(sK0,sK2,sK3)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f172,plain,(
% 2.30/0.67    spl6_15),
% 2.30/0.67    inference(avatar_split_clause,[],[f57,f169])).
% 2.30/0.67  fof(f57,plain,(
% 2.30/0.67    v5_pre_topc(sK5,sK3,sK1)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f167,plain,(
% 2.30/0.67    spl6_14),
% 2.30/0.67    inference(avatar_split_clause,[],[f53,f164])).
% 2.30/0.67  fof(f53,plain,(
% 2.30/0.67    v5_pre_topc(sK4,sK2,sK1)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f162,plain,(
% 2.30/0.67    ~spl6_13),
% 2.30/0.67    inference(avatar_split_clause,[],[f50,f159])).
% 2.30/0.67  fof(f50,plain,(
% 2.30/0.67    ~r1_tsep_1(sK2,sK3)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f157,plain,(
% 2.30/0.67    spl6_12),
% 2.30/0.67    inference(avatar_split_clause,[],[f49,f154])).
% 2.30/0.67  fof(f49,plain,(
% 2.30/0.67    m1_pre_topc(sK3,sK0)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f152,plain,(
% 2.30/0.67    spl6_11),
% 2.30/0.67    inference(avatar_split_clause,[],[f47,f149])).
% 2.30/0.67  fof(f47,plain,(
% 2.30/0.67    m1_pre_topc(sK2,sK0)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f147,plain,(
% 2.30/0.67    spl6_10),
% 2.30/0.67    inference(avatar_split_clause,[],[f55,f144])).
% 2.30/0.67  fof(f55,plain,(
% 2.30/0.67    v1_funct_1(sK5)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f142,plain,(
% 2.30/0.67    spl6_9),
% 2.30/0.67    inference(avatar_split_clause,[],[f51,f139])).
% 2.30/0.67  fof(f51,plain,(
% 2.30/0.67    v1_funct_1(sK4)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f137,plain,(
% 2.30/0.67    ~spl6_8),
% 2.30/0.67    inference(avatar_split_clause,[],[f48,f134])).
% 2.30/0.67  fof(f48,plain,(
% 2.30/0.67    ~v2_struct_0(sK3)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f132,plain,(
% 2.30/0.67    ~spl6_7),
% 2.30/0.67    inference(avatar_split_clause,[],[f46,f129])).
% 2.30/0.67  fof(f46,plain,(
% 2.30/0.67    ~v2_struct_0(sK2)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f127,plain,(
% 2.30/0.67    spl6_6),
% 2.30/0.67    inference(avatar_split_clause,[],[f45,f124])).
% 2.30/0.67  fof(f45,plain,(
% 2.30/0.67    l1_pre_topc(sK1)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f122,plain,(
% 2.30/0.67    spl6_5),
% 2.30/0.67    inference(avatar_split_clause,[],[f44,f119])).
% 2.30/0.67  fof(f44,plain,(
% 2.30/0.67    v2_pre_topc(sK1)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f117,plain,(
% 2.30/0.67    ~spl6_4),
% 2.30/0.67    inference(avatar_split_clause,[],[f43,f114])).
% 2.30/0.67  fof(f43,plain,(
% 2.30/0.67    ~v2_struct_0(sK1)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f112,plain,(
% 2.30/0.67    spl6_3),
% 2.30/0.67    inference(avatar_split_clause,[],[f42,f109])).
% 2.30/0.67  fof(f42,plain,(
% 2.30/0.67    l1_pre_topc(sK0)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f107,plain,(
% 2.30/0.67    spl6_2),
% 2.30/0.67    inference(avatar_split_clause,[],[f41,f104])).
% 2.30/0.67  fof(f41,plain,(
% 2.30/0.67    v2_pre_topc(sK0)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  fof(f102,plain,(
% 2.30/0.67    ~spl6_1),
% 2.30/0.67    inference(avatar_split_clause,[],[f40,f99])).
% 2.30/0.67  fof(f40,plain,(
% 2.30/0.67    ~v2_struct_0(sK0)),
% 2.30/0.67    inference(cnf_transformation,[],[f34])).
% 2.30/0.67  % SZS output end Proof for theBenchmark
% 2.30/0.67  % (19307)------------------------------
% 2.30/0.67  % (19307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.67  % (19307)Termination reason: Refutation
% 2.30/0.67  
% 2.30/0.67  % (19307)Memory used [KB]: 7931
% 2.30/0.67  % (19307)Time elapsed: 0.258 s
% 2.30/0.67  % (19307)------------------------------
% 2.30/0.67  % (19307)------------------------------
% 2.30/0.67  % (19304)Success in time 0.315 s
%------------------------------------------------------------------------------

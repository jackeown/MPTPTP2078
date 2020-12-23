%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:52 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  259 ( 973 expanded)
%              Number of leaves         :   52 ( 521 expanded)
%              Depth                    :   36
%              Number of atoms          : 2491 (12198 expanded)
%              Number of equality atoms :   44 ( 462 expanded)
%              Maximal formula depth    :   29 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f169,f174,f179,f184,f189,f194,f199,f204,f209,f214,f219,f225,f231,f278,f311,f409,f520,f539,f739,f744,f754,f759,f769,f774,f790,f806,f2191])).

fof(f2191,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_96
    | ~ spl6_97 ),
    inference(avatar_contradiction_clause,[],[f2190])).

fof(f2190,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_96
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2189,f158])).

fof(f158,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl6_15
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f2189,plain,
    ( ~ v1_funct_1(sK4)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_96
    | ~ spl6_97 ),
    inference(forward_demodulation,[],[f2188,f789])).

fof(f789,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f787])).

fof(f787,plain,
    ( spl6_96
  <=> sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f2188,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_96
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2187,f153])).

fof(f153,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl6_14
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f2187,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_96
    | ~ spl6_97 ),
    inference(forward_demodulation,[],[f2186,f789])).

fof(f2186,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_96
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2185,f148])).

fof(f148,plain,
    ( v5_pre_topc(sK4,sK2,sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_13
  <=> v5_pre_topc(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f2185,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_96
    | ~ spl6_97 ),
    inference(forward_demodulation,[],[f2184,f789])).

fof(f2184,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_96
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2183,f143])).

fof(f143,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl6_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f2183,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_96
    | ~ spl6_97 ),
    inference(forward_demodulation,[],[f2182,f789])).

fof(f2182,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2181,f203])).

fof(f203,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl6_24
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f2181,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | v2_struct_0(sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2180,f198])).

fof(f198,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl6_23
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f2180,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2179,f193])).

fof(f193,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_22
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f2179,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2178,f90])).

fof(f90,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_1
  <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f2178,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2177,f94])).

fof(f94,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_2
  <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f2177,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2176,f102])).

fof(f102,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_4
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f2176,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl6_3
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2175,f99])).

fof(f99,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_3
  <=> v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f2175,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2174,f138])).

fof(f138,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_11
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f2174,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2173,f133])).

fof(f133,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_10
  <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f2173,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2172,f128])).

fof(f128,plain,
    ( v5_pre_topc(sK5,sK3,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_9
  <=> v5_pre_topc(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f2172,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f2164,f123])).

fof(f123,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_8
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f2164,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_7
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41
    | ~ spl6_97 ),
    inference(superposition,[],[f343,f805])).

fof(f805,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_97 ),
    inference(avatar_component_clause,[],[f803])).

fof(f803,plain,
    ( spl6_97
  <=> sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f343,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
        | ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7))
        | v5_pre_topc(X7,sK0,X6)
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl6_7
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f342,f218])).

fof(f218,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl6_27
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f342,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7))
        | v5_pre_topc(X7,sK0,X6)
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f341,f213])).

fof(f213,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl6_26
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f341,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7))
        | v5_pre_topc(X7,sK0,X6)
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_25
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f340,f208])).

fof(f208,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl6_25
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f340,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7))
        | v5_pre_topc(X7,sK0,X6)
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f339,f188])).

fof(f188,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl6_21
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f339,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7))
        | v5_pre_topc(X7,sK0,X6)
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f338,f178])).

fof(f178,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl6_19
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f338,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7))
        | v5_pre_topc(X7,sK0,X6)
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_16
    | spl6_18
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f337,f173])).

fof(f173,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_18
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f337,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7))
        | v5_pre_topc(X7,sK0,X6)
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_16
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f336,f163])).

fof(f163,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl6_16
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f336,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7))
        | v5_pre_topc(X7,sK0,X6)
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f314,f310])).

fof(f310,plain,
    ( r4_tsep_1(sK0,sK2,sK3)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl6_41
  <=> r4_tsep_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f314,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
        | ~ m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6))))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7))
        | v5_pre_topc(X7,sK0,X6)
        | ~ v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6))
        | ~ v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
        | ~ v1_funct_1(X7)
        | ~ r4_tsep_1(sK0,sK2,sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_7 ),
    inference(superposition,[],[f74,f118])).

fof(f118,plain,
    ( sK0 = k1_tsep_1(sK0,sK2,sK3)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_7
  <=> sK0 = k1_tsep_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
      | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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

fof(f806,plain,
    ( spl6_97
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_29
    | ~ spl6_89
    | ~ spl6_92
    | ~ spl6_95 ),
    inference(avatar_split_clause,[],[f801,f771,f756,f741,f228,f136,f131,f121,f803])).

fof(f228,plain,
    ( spl6_29
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f741,plain,
    ( spl6_89
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f756,plain,
    ( spl6_92
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f771,plain,
    ( spl6_95
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f801,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_29
    | ~ spl6_89
    | ~ spl6_92
    | ~ spl6_95 ),
    inference(subsumption_resolution,[],[f800,f773])).

fof(f773,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_95 ),
    inference(avatar_component_clause,[],[f771])).

fof(f800,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_29
    | ~ spl6_89
    | ~ spl6_92 ),
    inference(subsumption_resolution,[],[f799,f758])).

fof(f758,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f756])).

fof(f799,plain,
    ( sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_29
    | ~ spl6_89 ),
    inference(subsumption_resolution,[],[f798,f138])).

fof(f798,plain,
    ( ~ v1_funct_1(sK5)
    | sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_29
    | ~ spl6_89 ),
    inference(subsumption_resolution,[],[f797,f133])).

fof(f797,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_8
    | ~ spl6_29
    | ~ spl6_89 ),
    inference(subsumption_resolution,[],[f796,f743])).

fof(f743,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_89 ),
    inference(avatar_component_clause,[],[f741])).

fof(f796,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_8
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f795,f123])).

fof(f795,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_29 ),
    inference(resolution,[],[f230,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | X2 = X3
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f230,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f228])).

fof(f790,plain,
    ( spl6_96
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_28
    | ~ spl6_88
    | ~ spl6_91
    | ~ spl6_94 ),
    inference(avatar_split_clause,[],[f785,f766,f751,f736,f222,f156,f151,f141,f787])).

fof(f222,plain,
    ( spl6_28
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f736,plain,
    ( spl6_88
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f751,plain,
    ( spl6_91
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f766,plain,
    ( spl6_94
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f785,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_28
    | ~ spl6_88
    | ~ spl6_91
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f784,f768])).

fof(f768,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f766])).

fof(f784,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_28
    | ~ spl6_88
    | ~ spl6_91 ),
    inference(subsumption_resolution,[],[f783,f753])).

fof(f753,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f751])).

fof(f783,plain,
    ( sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_28
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f782,f158])).

fof(f782,plain,
    ( ~ v1_funct_1(sK4)
    | sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_28
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f781,f153])).

fof(f781,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_12
    | ~ spl6_28
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f780,f738])).

fof(f738,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f736])).

fof(f780,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_12
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f779,f143])).

fof(f779,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_28 ),
    inference(resolution,[],[f224,f56])).

fof(f224,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f222])).

fof(f774,plain,
    ( spl6_95
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f617,f275,f216,f211,f206,f201,f196,f191,f161,f101,f93,f89,f771])).

fof(f275,plain,
    ( spl6_37
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f617,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f163,f277,f90,f94,f102,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f277,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f275])).

fof(f769,plain,
    ( spl6_94
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f618,f275,f216,f211,f206,f201,f196,f191,f176,f101,f93,f89,f766])).

fof(f618,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f178,f277,f90,f94,f102,f58])).

fof(f759,plain,
    ( spl6_92
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f620,f275,f216,f211,f206,f201,f196,f191,f161,f101,f93,f89,f756])).

fof(f620,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f163,f277,f90,f94,f102,f59])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f754,plain,
    ( spl6_91
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f621,f275,f216,f211,f206,f201,f196,f191,f176,f101,f93,f89,f751])).

fof(f621,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f178,f277,f90,f94,f102,f59])).

fof(f744,plain,
    ( spl6_89
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f623,f275,f216,f211,f206,f201,f196,f191,f161,f101,f93,f89,f741])).

fof(f623,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f163,f277,f90,f94,f102,f60])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f739,plain,
    ( spl6_88
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f624,f275,f216,f211,f206,f201,f196,f191,f176,f101,f93,f89,f736])).

fof(f624,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f178,f277,f90,f94,f102,f60])).

fof(f539,plain,
    ( spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27 ),
    inference(avatar_split_clause,[],[f532,f216,f211,f206,f201,f196,f191,f186,f176,f171,f161,f156,f151,f141,f136,f131,f121,f116,f93])).

fof(f532,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27 ),
    inference(forward_demodulation,[],[f492,f118])).

fof(f492,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27 ),
    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f188,f173,f178,f163,f158,f138,f153,f133,f123,f143,f62])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f520,plain,
    ( spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27 ),
    inference(avatar_split_clause,[],[f519,f216,f211,f206,f201,f196,f191,f186,f176,f171,f161,f156,f151,f141,f136,f131,f121,f116,f101])).

fof(f519,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27 ),
    inference(forward_demodulation,[],[f496,f118])).

fof(f496,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27 ),
    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f188,f173,f178,f163,f158,f138,f153,f133,f123,f143,f63])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f409,plain,
    ( spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27 ),
    inference(subsumption_resolution,[],[f407,f218])).

fof(f407,plain,
    ( v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f406,f213])).

fof(f406,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f405,f208])).

fof(f405,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23
    | spl6_24 ),
    inference(subsumption_resolution,[],[f404,f203])).

fof(f404,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f403,f198])).

fof(f403,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f402,f193])).

fof(f402,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19
    | spl6_21 ),
    inference(subsumption_resolution,[],[f401,f188])).

fof(f401,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f400,f178])).

fof(f400,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18 ),
    inference(subsumption_resolution,[],[f399,f173])).

fof(f399,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f398,f163])).

fof(f398,plain,
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
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f397,f158])).

fof(f397,plain,
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
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f396,f153])).

fof(f396,plain,
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
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f395,f143])).

fof(f395,plain,
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
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f394,f138])).

fof(f394,plain,
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
    | spl6_1
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f393,f133])).

fof(f393,plain,
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
    | spl6_1
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f392,f123])).

fof(f392,plain,
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
    | spl6_1 ),
    inference(resolution,[],[f91,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
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
    inference(cnf_transformation,[],[f16])).

fof(f91,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f311,plain,
    ( spl6_41
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27 ),
    inference(avatar_split_clause,[],[f292,f216,f211,f206,f181,f176,f166,f161,f308])).

fof(f166,plain,
    ( spl6_17
  <=> v1_borsuk_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f181,plain,
    ( spl6_20
  <=> v1_borsuk_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f292,plain,
    ( r4_tsep_1(sK0,sK2,sK3)
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_26
    | spl6_27 ),
    inference(unit_resulting_resolution,[],[f218,f213,f208,f168,f163,f178,f183,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r4_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
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
            & v1_borsuk_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tsep_1)).

fof(f183,plain,
    ( v1_borsuk_1(sK2,sK0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f168,plain,
    ( v1_borsuk_1(sK3,sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f166])).

fof(f278,plain,
    ( spl6_37
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f273,f206,f275])).

fof(f273,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f208,f76])).

fof(f76,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f231,plain,
    ( spl6_29
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f226,f116,f106,f228])).

fof(f106,plain,
    ( spl6_5
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f226,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f108,f118])).

fof(f108,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f225,plain,
    ( spl6_28
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f220,f116,f111,f222])).

fof(f111,plain,
    ( spl6_6
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f220,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f113,f118])).

fof(f113,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f219,plain,(
    ~ spl6_27 ),
    inference(avatar_split_clause,[],[f32,f216])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    & sK0 = k1_tsep_1(sK0,sK2,sK3)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v5_pre_topc(sK5,sK3,sK1)
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(sK4,sK2,sK1)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & v1_borsuk_1(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & v1_borsuk_1(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f27,f26,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                            & k1_tsep_1(X0,X2,X3) = X0
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),sK0,X1)
                            | ~ v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X4)
                          & sK0 = k1_tsep_1(sK0,X2,X3)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & v1_borsuk_1(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & v1_borsuk_1(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),sK0,X1)
                          | ~ v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(X1))
                          | ~ v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5)) )
                        & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X5)
                        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X4)
                        & sK0 = k1_tsep_1(sK0,X2,X3)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & v1_borsuk_1(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & v1_borsuk_1(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                        | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),sK0,sK1)
                        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
                        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5)) )
                      & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X5)
                      & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X4)
                      & sK0 = k1_tsep_1(sK0,X2,X3)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v5_pre_topc(X5,X3,sK1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                  & v5_pre_topc(X4,X2,sK1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & v1_borsuk_1(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & v1_borsuk_1(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),sK0,sK1)
                      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
                      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5)) )
                    & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X5)
                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X4)
                    & sK0 = k1_tsep_1(sK0,X2,X3)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v5_pre_topc(X5,X3,sK1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                & v5_pre_topc(X4,X2,sK1)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & v1_borsuk_1(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & v1_borsuk_1(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK0,sK1)
                    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
                    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)) )
                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),X3,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X5)
                  & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),sK2,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X4)
                  & sK0 = k1_tsep_1(sK0,sK2,X3)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v5_pre_topc(X5,X3,sK1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v5_pre_topc(X4,sK2,sK1)
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & v1_borsuk_1(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & v1_borsuk_1(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK0,sK1)
                  | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
                  | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)) )
                & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),X3,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X5)
                & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),sK2,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X4)
                & sK0 = k1_tsep_1(sK0,sK2,X3)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v5_pre_topc(X5,X3,sK1)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v5_pre_topc(X4,sK2,sK1)
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & v1_borsuk_1(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK0,sK1)
                | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
                | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)) )
              & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X5)
              & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X4)
              & sK0 = k1_tsep_1(sK0,sK2,sK3)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v5_pre_topc(X5,sK3,sK1)
              & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v5_pre_topc(X4,sK2,sK1)
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & v1_borsuk_1(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK0,sK1)
              | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
              | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)) )
            & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X5)
            & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X4)
            & sK0 = k1_tsep_1(sK0,sK2,sK3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            & v5_pre_topc(X5,sK3,sK1)
            & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v5_pre_topc(X4,sK2,sK1)
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK0,sK1)
            | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
            | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)) )
          & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),X5)
          & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),sK4)
          & sK0 = k1_tsep_1(sK0,sK2,sK3)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v5_pre_topc(X5,sK3,sK1)
          & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v5_pre_topc(sK4,sK2,sK1)
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK0,sK1)
          | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(sK0),u1_struct_0(sK1))
          | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)) )
        & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),X5)
        & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),sK4)
        & sK0 = k1_tsep_1(sK0,sK2,sK3)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v5_pre_topc(X5,sK3,sK1)
        & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
      & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
      & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
      & sK0 = k1_tsep_1(sK0,sK2,sK3)
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
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
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
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
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
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
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
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                                & k1_tsep_1(X0,X2,X3) = X0 )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
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
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
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
                         => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                              & k1_tsep_1(X0,X2,X3) = X0 )
                           => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                              & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_tmap_1)).

fof(f214,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f33,f211])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f209,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f34,f206])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f204,plain,(
    ~ spl6_24 ),
    inference(avatar_split_clause,[],[f35,f201])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f199,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f36,f196])).

fof(f36,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f194,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f37,f191])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f189,plain,(
    ~ spl6_21 ),
    inference(avatar_split_clause,[],[f38,f186])).

fof(f38,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f184,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f39,f181])).

fof(f39,plain,(
    v1_borsuk_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f179,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f40,f176])).

fof(f40,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f174,plain,(
    ~ spl6_18 ),
    inference(avatar_split_clause,[],[f41,f171])).

fof(f41,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f169,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f42,f166])).

fof(f42,plain,(
    v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f164,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f43,f161])).

fof(f43,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f159,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f44,f156])).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f154,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f45,f151])).

fof(f45,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f149,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f46,f146])).

fof(f46,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f144,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f47,f141])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f139,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f48,f136])).

fof(f48,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f134,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f49,f131])).

fof(f49,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f129,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f50,f126])).

fof(f50,plain,(
    v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f124,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f51,f121])).

fof(f51,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f119,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f52,f116])).

fof(f52,plain,(
    sK0 = k1_tsep_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f114,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f53,f111])).

fof(f53,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f109,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f54,f106])).

fof(f54,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f104,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f55,f101,f97,f93,f89])).

fof(f55,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:18:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.49  % (14018)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (14026)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (14016)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.54  % (14010)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.54  % (14011)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.54  % (14008)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.54  % (14029)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (14013)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.55  % (14023)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.55  % (14019)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.55  % (14025)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.55  % (14027)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.56  % (14021)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.56  % (14005)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.56  % (14014)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.56  % (14015)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.57  % (14020)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.57  % (14006)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.57  % (14009)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.57  % (14022)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.72/0.58  % (14012)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.72/0.58  % (14007)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.72/0.58  % (14030)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.72/0.58  % (14017)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.72/0.58  % (14024)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.72/0.59  % (14028)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.84/0.61  % (14018)Refutation found. Thanks to Tanya!
% 1.84/0.61  % SZS status Theorem for theBenchmark
% 2.10/0.62  % SZS output start Proof for theBenchmark
% 2.10/0.62  fof(f2192,plain,(
% 2.10/0.62    $false),
% 2.10/0.62    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f164,f169,f174,f179,f184,f189,f194,f199,f204,f209,f214,f219,f225,f231,f278,f311,f409,f520,f539,f739,f744,f754,f759,f769,f774,f790,f806,f2191])).
% 2.10/0.62  fof(f2191,plain,(
% 2.10/0.62    ~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_96 | ~spl6_97),
% 2.10/0.62    inference(avatar_contradiction_clause,[],[f2190])).
% 2.10/0.62  fof(f2190,plain,(
% 2.10/0.62    $false | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_96 | ~spl6_97)),
% 2.10/0.62    inference(subsumption_resolution,[],[f2189,f158])).
% 2.10/0.62  fof(f158,plain,(
% 2.10/0.62    v1_funct_1(sK4) | ~spl6_15),
% 2.10/0.62    inference(avatar_component_clause,[],[f156])).
% 2.10/0.62  fof(f156,plain,(
% 2.10/0.62    spl6_15 <=> v1_funct_1(sK4)),
% 2.10/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.10/0.62  fof(f2189,plain,(
% 2.10/0.62    ~v1_funct_1(sK4) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_96 | ~spl6_97)),
% 2.10/0.62    inference(forward_demodulation,[],[f2188,f789])).
% 2.10/0.62  fof(f789,plain,(
% 2.10/0.62    sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl6_96),
% 2.10/0.62    inference(avatar_component_clause,[],[f787])).
% 2.10/0.62  fof(f787,plain,(
% 2.10/0.62    spl6_96 <=> sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.10/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).
% 2.10/0.62  fof(f2188,plain,(
% 2.10/0.62    ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_96 | ~spl6_97)),
% 2.10/0.62    inference(subsumption_resolution,[],[f2187,f153])).
% 2.10/0.62  fof(f153,plain,(
% 2.10/0.62    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl6_14),
% 2.10/0.62    inference(avatar_component_clause,[],[f151])).
% 2.10/0.62  fof(f151,plain,(
% 2.10/0.62    spl6_14 <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.10/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.10/0.62  fof(f2187,plain,(
% 2.10/0.62    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_96 | ~spl6_97)),
% 2.10/0.62    inference(forward_demodulation,[],[f2186,f789])).
% 2.10/0.62  fof(f2186,plain,(
% 2.10/0.62    ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_96 | ~spl6_97)),
% 2.10/0.62    inference(subsumption_resolution,[],[f2185,f148])).
% 2.10/0.62  fof(f148,plain,(
% 2.10/0.62    v5_pre_topc(sK4,sK2,sK1) | ~spl6_13),
% 2.10/0.62    inference(avatar_component_clause,[],[f146])).
% 2.10/0.62  fof(f146,plain,(
% 2.10/0.62    spl6_13 <=> v5_pre_topc(sK4,sK2,sK1)),
% 2.10/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.10/0.62  fof(f2185,plain,(
% 2.10/0.62    ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_96 | ~spl6_97)),
% 2.10/0.62    inference(forward_demodulation,[],[f2184,f789])).
% 2.10/0.62  fof(f2184,plain,(
% 2.10/0.62    ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_96 | ~spl6_97)),
% 2.10/0.62    inference(subsumption_resolution,[],[f2183,f143])).
% 2.10/0.62  fof(f143,plain,(
% 2.10/0.62    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~spl6_12),
% 2.10/0.62    inference(avatar_component_clause,[],[f141])).
% 2.10/0.62  fof(f141,plain,(
% 2.10/0.62    spl6_12 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.10/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.10/0.62  fof(f2183,plain,(
% 2.10/0.62    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_96 | ~spl6_97)),
% 2.10/0.62    inference(forward_demodulation,[],[f2182,f789])).
% 2.10/0.62  fof(f2182,plain,(
% 2.10/0.62    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_97)),
% 2.10/0.62    inference(subsumption_resolution,[],[f2181,f203])).
% 2.10/0.62  fof(f203,plain,(
% 2.10/0.62    ~v2_struct_0(sK1) | spl6_24),
% 2.10/0.62    inference(avatar_component_clause,[],[f201])).
% 2.10/0.62  fof(f201,plain,(
% 2.10/0.62    spl6_24 <=> v2_struct_0(sK1)),
% 2.10/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 2.10/0.62  fof(f2181,plain,(
% 2.10/0.62    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | v2_struct_0(sK1) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_97)),
% 2.10/0.62    inference(subsumption_resolution,[],[f2180,f198])).
% 2.10/0.62  fof(f198,plain,(
% 2.10/0.62    v2_pre_topc(sK1) | ~spl6_23),
% 2.10/0.62    inference(avatar_component_clause,[],[f196])).
% 2.10/0.62  fof(f196,plain,(
% 2.10/0.62    spl6_23 <=> v2_pre_topc(sK1)),
% 2.10/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 2.10/0.62  fof(f2180,plain,(
% 2.10/0.62    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_97)),
% 2.10/0.62    inference(subsumption_resolution,[],[f2179,f193])).
% 2.10/0.62  fof(f193,plain,(
% 2.10/0.62    l1_pre_topc(sK1) | ~spl6_22),
% 2.10/0.62    inference(avatar_component_clause,[],[f191])).
% 2.10/0.62  fof(f191,plain,(
% 2.10/0.62    spl6_22 <=> l1_pre_topc(sK1)),
% 2.10/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 2.10/0.62  fof(f2179,plain,(
% 2.10/0.62    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_97)),
% 2.10/0.62    inference(subsumption_resolution,[],[f2178,f90])).
% 2.10/0.62  fof(f90,plain,(
% 2.10/0.62    v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl6_1),
% 2.10/0.62    inference(avatar_component_clause,[],[f89])).
% 2.10/0.62  fof(f89,plain,(
% 2.10/0.62    spl6_1 <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.10/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.10/0.62  fof(f2178,plain,(
% 2.10/0.62    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_2 | spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_97)),
% 2.10/0.62    inference(subsumption_resolution,[],[f2177,f94])).
% 2.10/0.62  fof(f94,plain,(
% 2.10/0.62    v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl6_2),
% 2.10/0.62    inference(avatar_component_clause,[],[f93])).
% 2.10/0.62  fof(f93,plain,(
% 2.10/0.62    spl6_2 <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.10/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.10/0.62  fof(f2177,plain,(
% 2.10/0.62    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl6_3 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_97)),
% 2.10/0.62    inference(subsumption_resolution,[],[f2176,f102])).
% 2.10/0.62  fof(f102,plain,(
% 2.10/0.62    m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl6_4),
% 2.10/0.62    inference(avatar_component_clause,[],[f101])).
% 2.10/0.62  fof(f101,plain,(
% 2.10/0.62    spl6_4 <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.10/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.10/0.62  fof(f2176,plain,(
% 2.10/0.62    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl6_3 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_97)),
% 2.10/0.62    inference(subsumption_resolution,[],[f2175,f99])).
% 2.10/0.62  fof(f99,plain,(
% 2.10/0.62    ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | spl6_3),
% 2.10/0.62    inference(avatar_component_clause,[],[f97])).
% 2.10/0.62  fof(f97,plain,(
% 2.10/0.62    spl6_3 <=> v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 2.10/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.10/0.62  fof(f2175,plain,(
% 2.10/0.62    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_97)),
% 2.10/0.62    inference(subsumption_resolution,[],[f2174,f138])).
% 2.10/0.63  fof(f138,plain,(
% 2.10/0.63    v1_funct_1(sK5) | ~spl6_11),
% 2.10/0.63    inference(avatar_component_clause,[],[f136])).
% 2.10/0.63  fof(f136,plain,(
% 2.10/0.63    spl6_11 <=> v1_funct_1(sK5)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.10/0.63  fof(f2174,plain,(
% 2.10/0.63    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_97)),
% 2.10/0.63    inference(subsumption_resolution,[],[f2173,f133])).
% 2.10/0.63  fof(f133,plain,(
% 2.10/0.63    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl6_10),
% 2.10/0.63    inference(avatar_component_clause,[],[f131])).
% 2.10/0.63  fof(f131,plain,(
% 2.10/0.63    spl6_10 <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.10/0.63  fof(f2173,plain,(
% 2.10/0.63    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_97)),
% 2.10/0.63    inference(subsumption_resolution,[],[f2172,f128])).
% 2.10/0.63  fof(f128,plain,(
% 2.10/0.63    v5_pre_topc(sK5,sK3,sK1) | ~spl6_9),
% 2.10/0.63    inference(avatar_component_clause,[],[f126])).
% 2.10/0.63  fof(f126,plain,(
% 2.10/0.63    spl6_9 <=> v5_pre_topc(sK5,sK3,sK1)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.10/0.63  fof(f2172,plain,(
% 2.10/0.63    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK5,sK3,sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_7 | ~spl6_8 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_97)),
% 2.10/0.63    inference(subsumption_resolution,[],[f2164,f123])).
% 2.10/0.63  fof(f123,plain,(
% 2.10/0.63    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl6_8),
% 2.10/0.63    inference(avatar_component_clause,[],[f121])).
% 2.10/0.63  fof(f121,plain,(
% 2.10/0.63    spl6_8 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.10/0.63  fof(f2164,plain,(
% 2.10/0.63    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK5,sK3,sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_7 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41 | ~spl6_97)),
% 2.10/0.63    inference(superposition,[],[f343,f805])).
% 2.10/0.63  fof(f805,plain,(
% 2.10/0.63    sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl6_97),
% 2.10/0.63    inference(avatar_component_clause,[],[f803])).
% 2.10/0.63  fof(f803,plain,(
% 2.10/0.63    spl6_97 <=> sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).
% 2.10/0.63  fof(f343,plain,(
% 2.10/0.63    ( ! [X6,X7] : (~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | ~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7)) | v5_pre_topc(X7,sK0,X6) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | (~spl6_7 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_41)),
% 2.10/0.63    inference(subsumption_resolution,[],[f342,f218])).
% 2.10/0.63  fof(f218,plain,(
% 2.10/0.63    ~v2_struct_0(sK0) | spl6_27),
% 2.10/0.63    inference(avatar_component_clause,[],[f216])).
% 2.10/0.63  fof(f216,plain,(
% 2.10/0.63    spl6_27 <=> v2_struct_0(sK0)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.10/0.63  fof(f342,plain,(
% 2.10/0.63    ( ! [X6,X7] : (~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7)) | v5_pre_topc(X7,sK0,X6) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | v2_struct_0(sK0)) ) | (~spl6_7 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_25 | ~spl6_26 | ~spl6_41)),
% 2.10/0.63    inference(subsumption_resolution,[],[f341,f213])).
% 2.10/0.63  fof(f213,plain,(
% 2.10/0.63    v2_pre_topc(sK0) | ~spl6_26),
% 2.10/0.63    inference(avatar_component_clause,[],[f211])).
% 2.10/0.63  fof(f211,plain,(
% 2.10/0.63    spl6_26 <=> v2_pre_topc(sK0)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.10/0.63  fof(f341,plain,(
% 2.10/0.63    ( ! [X6,X7] : (~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7)) | v5_pre_topc(X7,sK0,X6) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_7 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_25 | ~spl6_41)),
% 2.10/0.63    inference(subsumption_resolution,[],[f340,f208])).
% 2.10/0.63  fof(f208,plain,(
% 2.10/0.63    l1_pre_topc(sK0) | ~spl6_25),
% 2.10/0.63    inference(avatar_component_clause,[],[f206])).
% 2.10/0.63  fof(f206,plain,(
% 2.10/0.63    spl6_25 <=> l1_pre_topc(sK0)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 2.10/0.63  fof(f340,plain,(
% 2.10/0.63    ( ! [X6,X7] : (~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7)) | v5_pre_topc(X7,sK0,X6) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_7 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_41)),
% 2.10/0.63    inference(subsumption_resolution,[],[f339,f188])).
% 2.10/0.63  fof(f188,plain,(
% 2.10/0.63    ~v2_struct_0(sK2) | spl6_21),
% 2.10/0.63    inference(avatar_component_clause,[],[f186])).
% 2.10/0.63  fof(f186,plain,(
% 2.10/0.63    spl6_21 <=> v2_struct_0(sK2)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 2.10/0.63  fof(f339,plain,(
% 2.10/0.63    ( ! [X6,X7] : (~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7)) | v5_pre_topc(X7,sK0,X6) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | v2_struct_0(sK2) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_7 | ~spl6_16 | spl6_18 | ~spl6_19 | ~spl6_41)),
% 2.10/0.63    inference(subsumption_resolution,[],[f338,f178])).
% 2.10/0.63  fof(f178,plain,(
% 2.10/0.63    m1_pre_topc(sK2,sK0) | ~spl6_19),
% 2.10/0.63    inference(avatar_component_clause,[],[f176])).
% 2.10/0.63  fof(f176,plain,(
% 2.10/0.63    spl6_19 <=> m1_pre_topc(sK2,sK0)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 2.10/0.63  fof(f338,plain,(
% 2.10/0.63    ( ! [X6,X7] : (~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7)) | v5_pre_topc(X7,sK0,X6) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_7 | ~spl6_16 | spl6_18 | ~spl6_41)),
% 2.10/0.63    inference(subsumption_resolution,[],[f337,f173])).
% 2.10/0.63  fof(f173,plain,(
% 2.10/0.63    ~v2_struct_0(sK3) | spl6_18),
% 2.10/0.63    inference(avatar_component_clause,[],[f171])).
% 2.10/0.63  fof(f171,plain,(
% 2.10/0.63    spl6_18 <=> v2_struct_0(sK3)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 2.10/0.63  fof(f337,plain,(
% 2.10/0.63    ( ! [X6,X7] : (~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7)) | v5_pre_topc(X7,sK0,X6) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_7 | ~spl6_16 | ~spl6_41)),
% 2.10/0.63    inference(subsumption_resolution,[],[f336,f163])).
% 2.10/0.63  fof(f163,plain,(
% 2.10/0.63    m1_pre_topc(sK3,sK0) | ~spl6_16),
% 2.10/0.63    inference(avatar_component_clause,[],[f161])).
% 2.10/0.63  fof(f161,plain,(
% 2.10/0.63    spl6_16 <=> m1_pre_topc(sK3,sK0)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.10/0.63  fof(f336,plain,(
% 2.10/0.63    ( ! [X6,X7] : (~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7)) | v5_pre_topc(X7,sK0,X6) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_7 | ~spl6_41)),
% 2.10/0.63    inference(subsumption_resolution,[],[f314,f310])).
% 2.10/0.63  fof(f310,plain,(
% 2.10/0.63    r4_tsep_1(sK0,sK2,sK3) | ~spl6_41),
% 2.10/0.63    inference(avatar_component_clause,[],[f308])).
% 2.10/0.63  fof(f308,plain,(
% 2.10/0.63    spl6_41 <=> r4_tsep_1(sK0,sK2,sK3)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 2.10/0.63  fof(f314,plain,(
% 2.10/0.63    ( ! [X6,X7] : (~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK2,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6)))) | ~m1_subset_1(k3_tmap_1(sK0,X6,sK0,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X6)))) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK3,X7),sK3,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK3,X7),u1_struct_0(sK3),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK3,X7)) | v5_pre_topc(X7,sK0,X6) | ~v5_pre_topc(k3_tmap_1(sK0,X6,sK0,sK2,X7),sK2,X6) | ~v1_funct_2(k3_tmap_1(sK0,X6,sK0,sK2,X7),u1_struct_0(sK2),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(sK0,X6,sK0,sK2,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~r4_tsep_1(sK0,sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_7),
% 2.10/0.63    inference(superposition,[],[f74,f118])).
% 2.10/0.63  fof(f118,plain,(
% 2.10/0.63    sK0 = k1_tsep_1(sK0,sK2,sK3) | ~spl6_7),
% 2.10/0.63    inference(avatar_component_clause,[],[f116])).
% 2.10/0.63  fof(f116,plain,(
% 2.10/0.63    spl6_7 <=> sK0 = k1_tsep_1(sK0,sK2,sK3)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.10/0.63  fof(f74,plain,(
% 2.10/0.63    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f31])).
% 2.10/0.63  fof(f31,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.63    inference(flattening,[],[f30])).
% 2.10/0.63  fof(f30,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.63    inference(nnf_transformation,[],[f18])).
% 2.10/0.63  fof(f18,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.63    inference(flattening,[],[f17])).
% 2.10/0.63  fof(f17,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.63    inference(ennf_transformation,[],[f4])).
% 2.10/0.63  fof(f4,axiom,(
% 2.10/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).
% 2.10/0.63  fof(f806,plain,(
% 2.10/0.63    spl6_97 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_29 | ~spl6_89 | ~spl6_92 | ~spl6_95),
% 2.10/0.63    inference(avatar_split_clause,[],[f801,f771,f756,f741,f228,f136,f131,f121,f803])).
% 2.10/0.63  fof(f228,plain,(
% 2.10/0.63    spl6_29 <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 2.10/0.63  fof(f741,plain,(
% 2.10/0.63    spl6_89 <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).
% 2.10/0.63  fof(f756,plain,(
% 2.10/0.63    spl6_92 <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).
% 2.10/0.63  fof(f771,plain,(
% 2.10/0.63    spl6_95 <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).
% 2.10/0.63  fof(f801,plain,(
% 2.10/0.63    sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_29 | ~spl6_89 | ~spl6_92 | ~spl6_95)),
% 2.10/0.63    inference(subsumption_resolution,[],[f800,f773])).
% 2.10/0.63  fof(f773,plain,(
% 2.10/0.63    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~spl6_95),
% 2.10/0.63    inference(avatar_component_clause,[],[f771])).
% 2.10/0.63  fof(f800,plain,(
% 2.10/0.63    sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_29 | ~spl6_89 | ~spl6_92)),
% 2.10/0.63    inference(subsumption_resolution,[],[f799,f758])).
% 2.10/0.63  fof(f758,plain,(
% 2.10/0.63    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl6_92),
% 2.10/0.63    inference(avatar_component_clause,[],[f756])).
% 2.10/0.63  fof(f799,plain,(
% 2.10/0.63    sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_29 | ~spl6_89)),
% 2.10/0.63    inference(subsumption_resolution,[],[f798,f138])).
% 2.10/0.63  fof(f798,plain,(
% 2.10/0.63    ~v1_funct_1(sK5) | sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_8 | ~spl6_10 | ~spl6_29 | ~spl6_89)),
% 2.10/0.63    inference(subsumption_resolution,[],[f797,f133])).
% 2.10/0.63  fof(f797,plain,(
% 2.10/0.63    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_8 | ~spl6_29 | ~spl6_89)),
% 2.10/0.63    inference(subsumption_resolution,[],[f796,f743])).
% 2.10/0.63  fof(f743,plain,(
% 2.10/0.63    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl6_89),
% 2.10/0.63    inference(avatar_component_clause,[],[f741])).
% 2.10/0.63  fof(f796,plain,(
% 2.10/0.63    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_8 | ~spl6_29)),
% 2.10/0.63    inference(subsumption_resolution,[],[f795,f123])).
% 2.10/0.63  fof(f795,plain,(
% 2.10/0.63    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | sK5 = k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~spl6_29),
% 2.10/0.63    inference(resolution,[],[f230,f56])).
% 2.10/0.63  fof(f56,plain,(
% 2.10/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | X2 = X3 | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f29])).
% 2.10/0.63  fof(f29,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.10/0.63    inference(nnf_transformation,[],[f12])).
% 2.10/0.63  fof(f12,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.10/0.63    inference(flattening,[],[f11])).
% 2.10/0.63  fof(f11,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.10/0.63    inference(ennf_transformation,[],[f1])).
% 2.10/0.63  fof(f1,axiom,(
% 2.10/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.10/0.63  fof(f230,plain,(
% 2.10/0.63    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~spl6_29),
% 2.10/0.63    inference(avatar_component_clause,[],[f228])).
% 2.10/0.63  fof(f790,plain,(
% 2.10/0.63    spl6_96 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_28 | ~spl6_88 | ~spl6_91 | ~spl6_94),
% 2.10/0.63    inference(avatar_split_clause,[],[f785,f766,f751,f736,f222,f156,f151,f141,f787])).
% 2.10/0.63  fof(f222,plain,(
% 2.10/0.63    spl6_28 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.10/0.63  fof(f736,plain,(
% 2.10/0.63    spl6_88 <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).
% 2.10/0.63  fof(f751,plain,(
% 2.10/0.63    spl6_91 <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).
% 2.10/0.63  fof(f766,plain,(
% 2.10/0.63    spl6_94 <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 2.10/0.63  fof(f785,plain,(
% 2.10/0.63    sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_28 | ~spl6_88 | ~spl6_91 | ~spl6_94)),
% 2.10/0.63    inference(subsumption_resolution,[],[f784,f768])).
% 2.10/0.63  fof(f768,plain,(
% 2.10/0.63    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~spl6_94),
% 2.10/0.63    inference(avatar_component_clause,[],[f766])).
% 2.10/0.63  fof(f784,plain,(
% 2.10/0.63    sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_28 | ~spl6_88 | ~spl6_91)),
% 2.10/0.63    inference(subsumption_resolution,[],[f783,f753])).
% 2.10/0.63  fof(f753,plain,(
% 2.10/0.63    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl6_91),
% 2.10/0.63    inference(avatar_component_clause,[],[f751])).
% 2.10/0.63  fof(f783,plain,(
% 2.10/0.63    sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_28 | ~spl6_88)),
% 2.10/0.63    inference(subsumption_resolution,[],[f782,f158])).
% 2.10/0.63  fof(f782,plain,(
% 2.10/0.63    ~v1_funct_1(sK4) | sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_12 | ~spl6_14 | ~spl6_28 | ~spl6_88)),
% 2.10/0.63    inference(subsumption_resolution,[],[f781,f153])).
% 2.10/0.63  fof(f781,plain,(
% 2.10/0.63    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_12 | ~spl6_28 | ~spl6_88)),
% 2.10/0.63    inference(subsumption_resolution,[],[f780,f738])).
% 2.10/0.63  fof(f738,plain,(
% 2.10/0.63    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~spl6_88),
% 2.10/0.63    inference(avatar_component_clause,[],[f736])).
% 2.10/0.63  fof(f780,plain,(
% 2.10/0.63    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_12 | ~spl6_28)),
% 2.10/0.63    inference(subsumption_resolution,[],[f779,f143])).
% 2.10/0.63  fof(f779,plain,(
% 2.10/0.63    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | sK4 = k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | ~spl6_28),
% 2.10/0.63    inference(resolution,[],[f224,f56])).
% 2.10/0.63  fof(f224,plain,(
% 2.10/0.63    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~spl6_28),
% 2.10/0.63    inference(avatar_component_clause,[],[f222])).
% 2.10/0.63  fof(f774,plain,(
% 2.10/0.63    spl6_95 | ~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_16 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_37),
% 2.10/0.63    inference(avatar_split_clause,[],[f617,f275,f216,f211,f206,f201,f196,f191,f161,f101,f93,f89,f771])).
% 2.10/0.63  fof(f275,plain,(
% 2.10/0.63    spl6_37 <=> m1_pre_topc(sK0,sK0)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 2.10/0.63  fof(f617,plain,(
% 2.10/0.63    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_16 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_37)),
% 2.10/0.63    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f163,f277,f90,f94,f102,f58])).
% 2.10/0.63  fof(f58,plain,(
% 2.10/0.63    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f14])).
% 2.10/0.63  fof(f14,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.63    inference(flattening,[],[f13])).
% 2.10/0.63  fof(f13,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.63    inference(ennf_transformation,[],[f3])).
% 2.10/0.63  fof(f3,axiom,(
% 2.10/0.63    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.10/0.63  fof(f277,plain,(
% 2.10/0.63    m1_pre_topc(sK0,sK0) | ~spl6_37),
% 2.10/0.63    inference(avatar_component_clause,[],[f275])).
% 2.10/0.63  fof(f769,plain,(
% 2.10/0.63    spl6_94 | ~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_19 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_37),
% 2.10/0.63    inference(avatar_split_clause,[],[f618,f275,f216,f211,f206,f201,f196,f191,f176,f101,f93,f89,f766])).
% 2.10/0.63  fof(f618,plain,(
% 2.10/0.63    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_19 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_37)),
% 2.10/0.63    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f178,f277,f90,f94,f102,f58])).
% 2.10/0.63  fof(f759,plain,(
% 2.10/0.63    spl6_92 | ~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_16 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_37),
% 2.10/0.63    inference(avatar_split_clause,[],[f620,f275,f216,f211,f206,f201,f196,f191,f161,f101,f93,f89,f756])).
% 2.10/0.63  fof(f620,plain,(
% 2.10/0.63    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_16 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_37)),
% 2.10/0.63    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f163,f277,f90,f94,f102,f59])).
% 2.10/0.63  fof(f59,plain,(
% 2.10/0.63    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f14])).
% 2.10/0.63  fof(f754,plain,(
% 2.10/0.63    spl6_91 | ~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_19 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_37),
% 2.10/0.63    inference(avatar_split_clause,[],[f621,f275,f216,f211,f206,f201,f196,f191,f176,f101,f93,f89,f751])).
% 2.10/0.63  fof(f621,plain,(
% 2.10/0.63    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_19 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_37)),
% 2.10/0.63    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f178,f277,f90,f94,f102,f59])).
% 2.10/0.63  fof(f744,plain,(
% 2.10/0.63    spl6_89 | ~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_16 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_37),
% 2.10/0.63    inference(avatar_split_clause,[],[f623,f275,f216,f211,f206,f201,f196,f191,f161,f101,f93,f89,f741])).
% 2.10/0.63  fof(f623,plain,(
% 2.10/0.63    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_16 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_37)),
% 2.10/0.63    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f163,f277,f90,f94,f102,f60])).
% 2.10/0.63  fof(f60,plain,(
% 2.10/0.63    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f14])).
% 2.10/0.63  fof(f739,plain,(
% 2.10/0.63    spl6_88 | ~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_19 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_37),
% 2.10/0.63    inference(avatar_split_clause,[],[f624,f275,f216,f211,f206,f201,f196,f191,f176,f101,f93,f89,f736])).
% 2.10/0.63  fof(f624,plain,(
% 2.10/0.63    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_19 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27 | ~spl6_37)),
% 2.10/0.63    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f178,f277,f90,f94,f102,f60])).
% 2.10/0.63  fof(f539,plain,(
% 2.10/0.63    spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27),
% 2.10/0.63    inference(avatar_split_clause,[],[f532,f216,f211,f206,f201,f196,f191,f186,f176,f171,f161,f156,f151,f141,f136,f131,f121,f116,f93])).
% 2.10/0.63  fof(f532,plain,(
% 2.10/0.63    v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27)),
% 2.10/0.63    inference(forward_demodulation,[],[f492,f118])).
% 2.10/0.63  fof(f492,plain,(
% 2.10/0.63    v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) | (~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27)),
% 2.10/0.63    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f188,f173,f178,f163,f158,f138,f153,f133,f123,f143,f62])).
% 2.10/0.63  fof(f62,plain,(
% 2.10/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f16])).
% 2.10/0.63  fof(f16,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.63    inference(flattening,[],[f15])).
% 2.10/0.63  fof(f15,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.63    inference(ennf_transformation,[],[f2])).
% 2.10/0.63  fof(f2,axiom,(
% 2.10/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 2.10/0.63  fof(f520,plain,(
% 2.10/0.63    spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27),
% 2.10/0.63    inference(avatar_split_clause,[],[f519,f216,f211,f206,f201,f196,f191,f186,f176,f171,f161,f156,f151,f141,f136,f131,f121,f116,f101])).
% 2.10/0.63  fof(f519,plain,(
% 2.10/0.63    m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27)),
% 2.10/0.63    inference(forward_demodulation,[],[f496,f118])).
% 2.10/0.63  fof(f496,plain,(
% 2.10/0.63    m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) | (~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27)),
% 2.10/0.63    inference(unit_resulting_resolution,[],[f218,f213,f208,f203,f198,f193,f188,f173,f178,f163,f158,f138,f153,f133,f123,f143,f63])).
% 2.10/0.63  fof(f63,plain,(
% 2.10/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f16])).
% 2.10/0.63  fof(f409,plain,(
% 2.10/0.63    spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27),
% 2.10/0.63    inference(avatar_contradiction_clause,[],[f408])).
% 2.10/0.63  fof(f408,plain,(
% 2.10/0.63    $false | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26 | spl6_27)),
% 2.10/0.63    inference(subsumption_resolution,[],[f407,f218])).
% 2.10/0.63  fof(f407,plain,(
% 2.10/0.63    v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25 | ~spl6_26)),
% 2.10/0.63    inference(subsumption_resolution,[],[f406,f213])).
% 2.10/0.63  fof(f406,plain,(
% 2.10/0.63    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24 | ~spl6_25)),
% 2.10/0.63    inference(subsumption_resolution,[],[f405,f208])).
% 2.10/0.63  fof(f405,plain,(
% 2.10/0.63    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23 | spl6_24)),
% 2.10/0.63    inference(subsumption_resolution,[],[f404,f203])).
% 2.10/0.63  fof(f404,plain,(
% 2.10/0.63    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22 | ~spl6_23)),
% 2.10/0.63    inference(subsumption_resolution,[],[f403,f198])).
% 2.10/0.63  fof(f403,plain,(
% 2.10/0.63    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21 | ~spl6_22)),
% 2.10/0.63    inference(subsumption_resolution,[],[f402,f193])).
% 2.10/0.63  fof(f402,plain,(
% 2.10/0.63    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19 | spl6_21)),
% 2.10/0.63    inference(subsumption_resolution,[],[f401,f188])).
% 2.10/0.63  fof(f401,plain,(
% 2.10/0.63    v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_19)),
% 2.10/0.63    inference(subsumption_resolution,[],[f400,f178])).
% 2.10/0.63  fof(f400,plain,(
% 2.10/0.63    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_18)),
% 2.10/0.63    inference(subsumption_resolution,[],[f399,f173])).
% 2.10/0.63  fof(f399,plain,(
% 2.10/0.63    v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_16)),
% 2.10/0.63    inference(subsumption_resolution,[],[f398,f163])).
% 2.10/0.63  fof(f398,plain,(
% 2.10/0.63    ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 2.10/0.63    inference(subsumption_resolution,[],[f397,f158])).
% 2.10/0.63  fof(f397,plain,(
% 2.10/0.63    ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14)),
% 2.10/0.63    inference(subsumption_resolution,[],[f396,f153])).
% 2.10/0.63  fof(f396,plain,(
% 2.10/0.63    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 2.10/0.63    inference(subsumption_resolution,[],[f395,f143])).
% 2.10/0.63  fof(f395,plain,(
% 2.10/0.63    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10 | ~spl6_11)),
% 2.10/0.63    inference(subsumption_resolution,[],[f394,f138])).
% 2.10/0.63  fof(f394,plain,(
% 2.10/0.63    ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8 | ~spl6_10)),
% 2.10/0.63    inference(subsumption_resolution,[],[f393,f133])).
% 2.10/0.63  fof(f393,plain,(
% 2.10/0.63    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl6_1 | ~spl6_8)),
% 2.10/0.63    inference(subsumption_resolution,[],[f392,f123])).
% 2.10/0.63  fof(f392,plain,(
% 2.10/0.63    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_1),
% 2.10/0.63    inference(resolution,[],[f91,f61])).
% 2.10/0.63  fof(f61,plain,(
% 2.10/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f16])).
% 2.10/0.63  fof(f91,plain,(
% 2.10/0.63    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | spl6_1),
% 2.10/0.63    inference(avatar_component_clause,[],[f89])).
% 2.10/0.63  fof(f311,plain,(
% 2.10/0.63    spl6_41 | ~spl6_16 | ~spl6_17 | ~spl6_19 | ~spl6_20 | ~spl6_25 | ~spl6_26 | spl6_27),
% 2.10/0.63    inference(avatar_split_clause,[],[f292,f216,f211,f206,f181,f176,f166,f161,f308])).
% 2.10/0.63  fof(f166,plain,(
% 2.10/0.63    spl6_17 <=> v1_borsuk_1(sK3,sK0)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 2.10/0.63  fof(f181,plain,(
% 2.10/0.63    spl6_20 <=> v1_borsuk_1(sK2,sK0)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 2.10/0.63  fof(f292,plain,(
% 2.10/0.63    r4_tsep_1(sK0,sK2,sK3) | (~spl6_16 | ~spl6_17 | ~spl6_19 | ~spl6_20 | ~spl6_25 | ~spl6_26 | spl6_27)),
% 2.10/0.63    inference(unit_resulting_resolution,[],[f218,f213,f208,f168,f163,f178,f183,f77])).
% 2.10/0.63  fof(f77,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r4_tsep_1(X0,X1,X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f21])).
% 2.10/0.63  fof(f21,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.10/0.63    inference(flattening,[],[f20])).
% 2.10/0.63  fof(f20,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.10/0.63    inference(ennf_transformation,[],[f6])).
% 2.10/0.63  fof(f6,axiom,(
% 2.10/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tsep_1)).
% 2.10/0.63  fof(f183,plain,(
% 2.10/0.63    v1_borsuk_1(sK2,sK0) | ~spl6_20),
% 2.10/0.63    inference(avatar_component_clause,[],[f181])).
% 2.10/0.63  fof(f168,plain,(
% 2.10/0.63    v1_borsuk_1(sK3,sK0) | ~spl6_17),
% 2.10/0.63    inference(avatar_component_clause,[],[f166])).
% 2.10/0.63  fof(f278,plain,(
% 2.10/0.63    spl6_37 | ~spl6_25),
% 2.10/0.63    inference(avatar_split_clause,[],[f273,f206,f275])).
% 2.10/0.63  fof(f273,plain,(
% 2.10/0.63    m1_pre_topc(sK0,sK0) | ~spl6_25),
% 2.10/0.63    inference(unit_resulting_resolution,[],[f208,f76])).
% 2.10/0.63  fof(f76,plain,(
% 2.10/0.63    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  fof(f19,plain,(
% 2.10/0.63    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f5])).
% 2.10/0.63  fof(f5,axiom,(
% 2.10/0.63    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.10/0.63  fof(f231,plain,(
% 2.10/0.63    spl6_29 | ~spl6_5 | ~spl6_7),
% 2.10/0.63    inference(avatar_split_clause,[],[f226,f116,f106,f228])).
% 2.10/0.63  fof(f106,plain,(
% 2.10/0.63    spl6_5 <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.10/0.63  fof(f226,plain,(
% 2.10/0.63    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | (~spl6_5 | ~spl6_7)),
% 2.10/0.63    inference(forward_demodulation,[],[f108,f118])).
% 2.10/0.63  fof(f108,plain,(
% 2.10/0.63    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) | ~spl6_5),
% 2.10/0.63    inference(avatar_component_clause,[],[f106])).
% 2.10/0.63  fof(f225,plain,(
% 2.10/0.63    spl6_28 | ~spl6_6 | ~spl6_7),
% 2.10/0.63    inference(avatar_split_clause,[],[f220,f116,f111,f222])).
% 2.10/0.63  fof(f111,plain,(
% 2.10/0.63    spl6_6 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.10/0.63  fof(f220,plain,(
% 2.10/0.63    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | (~spl6_6 | ~spl6_7)),
% 2.10/0.63    inference(forward_demodulation,[],[f113,f118])).
% 2.10/0.63  fof(f113,plain,(
% 2.10/0.63    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~spl6_6),
% 2.10/0.63    inference(avatar_component_clause,[],[f111])).
% 2.10/0.63  fof(f219,plain,(
% 2.10/0.63    ~spl6_27),
% 2.10/0.63    inference(avatar_split_clause,[],[f32,f216])).
% 2.10/0.63  fof(f32,plain,(
% 2.10/0.63    ~v2_struct_0(sK0)),
% 2.10/0.63    inference(cnf_transformation,[],[f28])).
% 2.10/0.63  fof(f28,plain,(
% 2.10/0.63    ((((((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) & sK0 = k1_tsep_1(sK0,sK2,sK3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(sK5,sK3,sK1) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & v1_borsuk_1(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.10/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f27,f26,f25,f24,f23,f22])).
% 2.10/0.63  fof(f22,plain,(
% 2.10/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),sK0,X1) | ~v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X4) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & v1_borsuk_1(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f23,plain,(
% 2.10/0.63    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),sK0,X1) | ~v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X4) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & v1_borsuk_1(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X4) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & v1_borsuk_1(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f24,plain,(
% 2.10/0.63    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,sK1,X2,X3,X4,X5)),X4) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & v1_borsuk_1(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),X3,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),sK2,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X4) & sK0 = k1_tsep_1(sK0,sK2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & v1_borsuk_1(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0) & ~v2_struct_0(sK2))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f25,plain,(
% 2.10/0.63    ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),X3,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,X3),sK2,k10_tmap_1(sK0,sK1,sK2,X3,X4,X5)),X4) & sK0 = k1_tsep_1(sK0,sK2,X3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & v1_borsuk_1(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5))) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X4) & sK0 = k1_tsep_1(sK0,sK2,sK3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(X5,sK3,sK1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & v1_borsuk_1(sK3,sK0) & ~v2_struct_0(sK3))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f26,plain,(
% 2.10/0.63    ? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5))) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X4,X5)),X4) & sK0 = k1_tsep_1(sK0,sK2,sK3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(X5,sK3,sK1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(X4,sK2,sK1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5))) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),sK4) & sK0 = k1_tsep_1(sK0,sK2,sK3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(X5,sK3,sK1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f27,plain,(
% 2.10/0.63    ? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5))) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,X5)),sK4) & sK0 = k1_tsep_1(sK0,sK2,sK3) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(X5,sK3,sK1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) & sK0 = k1_tsep_1(sK0,sK2,sK3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(sK5,sK3,sK1) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f10,plain,(
% 2.10/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.10/0.63    inference(flattening,[],[f9])).
% 2.16/0.63  fof(f9,plain,(
% 2.16/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.16/0.63    inference(ennf_transformation,[],[f8])).
% 2.16/0.63  fof(f8,negated_conjecture,(
% 2.16/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 2.16/0.63    inference(negated_conjecture,[],[f7])).
% 2.16/0.63  fof(f7,conjecture,(
% 2.16/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_tmap_1)).
% 2.16/0.63  fof(f214,plain,(
% 2.16/0.63    spl6_26),
% 2.16/0.63    inference(avatar_split_clause,[],[f33,f211])).
% 2.16/0.63  fof(f33,plain,(
% 2.16/0.63    v2_pre_topc(sK0)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f209,plain,(
% 2.16/0.63    spl6_25),
% 2.16/0.63    inference(avatar_split_clause,[],[f34,f206])).
% 2.16/0.63  fof(f34,plain,(
% 2.16/0.63    l1_pre_topc(sK0)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f204,plain,(
% 2.16/0.63    ~spl6_24),
% 2.16/0.63    inference(avatar_split_clause,[],[f35,f201])).
% 2.16/0.63  fof(f35,plain,(
% 2.16/0.63    ~v2_struct_0(sK1)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f199,plain,(
% 2.16/0.63    spl6_23),
% 2.16/0.63    inference(avatar_split_clause,[],[f36,f196])).
% 2.16/0.63  fof(f36,plain,(
% 2.16/0.63    v2_pre_topc(sK1)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f194,plain,(
% 2.16/0.63    spl6_22),
% 2.16/0.63    inference(avatar_split_clause,[],[f37,f191])).
% 2.16/0.63  fof(f37,plain,(
% 2.16/0.63    l1_pre_topc(sK1)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f189,plain,(
% 2.16/0.63    ~spl6_21),
% 2.16/0.63    inference(avatar_split_clause,[],[f38,f186])).
% 2.16/0.63  fof(f38,plain,(
% 2.16/0.63    ~v2_struct_0(sK2)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f184,plain,(
% 2.16/0.63    spl6_20),
% 2.16/0.63    inference(avatar_split_clause,[],[f39,f181])).
% 2.16/0.63  fof(f39,plain,(
% 2.16/0.63    v1_borsuk_1(sK2,sK0)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f179,plain,(
% 2.16/0.63    spl6_19),
% 2.16/0.63    inference(avatar_split_clause,[],[f40,f176])).
% 2.16/0.63  fof(f40,plain,(
% 2.16/0.63    m1_pre_topc(sK2,sK0)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f174,plain,(
% 2.16/0.63    ~spl6_18),
% 2.16/0.63    inference(avatar_split_clause,[],[f41,f171])).
% 2.16/0.63  fof(f41,plain,(
% 2.16/0.63    ~v2_struct_0(sK3)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f169,plain,(
% 2.16/0.63    spl6_17),
% 2.16/0.63    inference(avatar_split_clause,[],[f42,f166])).
% 2.16/0.63  fof(f42,plain,(
% 2.16/0.63    v1_borsuk_1(sK3,sK0)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f164,plain,(
% 2.16/0.63    spl6_16),
% 2.16/0.63    inference(avatar_split_clause,[],[f43,f161])).
% 2.16/0.63  fof(f43,plain,(
% 2.16/0.63    m1_pre_topc(sK3,sK0)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f159,plain,(
% 2.16/0.63    spl6_15),
% 2.16/0.63    inference(avatar_split_clause,[],[f44,f156])).
% 2.16/0.63  fof(f44,plain,(
% 2.16/0.63    v1_funct_1(sK4)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f154,plain,(
% 2.16/0.63    spl6_14),
% 2.16/0.63    inference(avatar_split_clause,[],[f45,f151])).
% 2.16/0.63  fof(f45,plain,(
% 2.16/0.63    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f149,plain,(
% 2.16/0.63    spl6_13),
% 2.16/0.63    inference(avatar_split_clause,[],[f46,f146])).
% 2.16/0.63  fof(f46,plain,(
% 2.16/0.63    v5_pre_topc(sK4,sK2,sK1)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f144,plain,(
% 2.16/0.63    spl6_12),
% 2.16/0.63    inference(avatar_split_clause,[],[f47,f141])).
% 2.16/0.63  fof(f47,plain,(
% 2.16/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f139,plain,(
% 2.16/0.63    spl6_11),
% 2.16/0.63    inference(avatar_split_clause,[],[f48,f136])).
% 2.16/0.63  fof(f48,plain,(
% 2.16/0.63    v1_funct_1(sK5)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f134,plain,(
% 2.16/0.63    spl6_10),
% 2.16/0.63    inference(avatar_split_clause,[],[f49,f131])).
% 2.16/0.63  fof(f49,plain,(
% 2.16/0.63    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f129,plain,(
% 2.16/0.63    spl6_9),
% 2.16/0.63    inference(avatar_split_clause,[],[f50,f126])).
% 2.16/0.63  fof(f50,plain,(
% 2.16/0.63    v5_pre_topc(sK5,sK3,sK1)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f124,plain,(
% 2.16/0.63    spl6_8),
% 2.16/0.63    inference(avatar_split_clause,[],[f51,f121])).
% 2.16/0.63  fof(f51,plain,(
% 2.16/0.63    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f119,plain,(
% 2.16/0.63    spl6_7),
% 2.16/0.63    inference(avatar_split_clause,[],[f52,f116])).
% 2.16/0.63  fof(f52,plain,(
% 2.16/0.63    sK0 = k1_tsep_1(sK0,sK2,sK3)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f114,plain,(
% 2.16/0.63    spl6_6),
% 2.16/0.63    inference(avatar_split_clause,[],[f53,f111])).
% 2.16/0.63  fof(f53,plain,(
% 2.16/0.63    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f109,plain,(
% 2.16/0.63    spl6_5),
% 2.16/0.63    inference(avatar_split_clause,[],[f54,f106])).
% 2.16/0.63  fof(f54,plain,(
% 2.16/0.63    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f104,plain,(
% 2.16/0.63    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 2.16/0.63    inference(avatar_split_clause,[],[f55,f101,f97,f93,f89])).
% 2.16/0.63  fof(f55,plain,(
% 2.16/0.63    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  % SZS output end Proof for theBenchmark
% 2.16/0.63  % (14018)------------------------------
% 2.16/0.63  % (14018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.63  % (14018)Termination reason: Refutation
% 2.16/0.63  
% 2.16/0.63  % (14018)Memory used [KB]: 9850
% 2.16/0.63  % (14018)Time elapsed: 0.185 s
% 2.16/0.63  % (14018)------------------------------
% 2.16/0.63  % (14018)------------------------------
% 2.16/0.63  % (14004)Success in time 0.28 s
%------------------------------------------------------------------------------

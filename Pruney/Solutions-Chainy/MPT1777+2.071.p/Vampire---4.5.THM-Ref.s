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
% DateTime   : Thu Dec  3 13:19:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  294 ( 706 expanded)
%              Number of leaves         :   71 ( 354 expanded)
%              Depth                    :   32
%              Number of atoms          : 1581 (6460 expanded)
%              Number of equality atoms :   67 ( 740 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f175,f180,f185,f190,f195,f202,f208,f220,f246,f272,f277,f286,f291,f296,f318,f326,f365,f366,f369,f372,f380,f388,f398,f449,f456,f728,f914,f1107,f1193,f1225,f1249,f1342,f1444])).

fof(f1444,plain,
    ( spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(avatar_contradiction_clause,[],[f1443])).

fof(f1443,plain,
    ( $false
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1442,f308])).

fof(f308,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl9_38
  <=> v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f1442,plain,
    ( ~ v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(forward_demodulation,[],[f1441,f387])).

fof(f387,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl9_42
  <=> u1_struct_0(sK5) = k2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f1441,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK5),k2_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(forward_demodulation,[],[f1440,f245])).

fof(f245,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl9_26
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f1440,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1439,f303])).

fof(f303,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl9_37
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f1439,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(forward_demodulation,[],[f1438,f387])).

fof(f1438,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(forward_demodulation,[],[f1437,f245])).

fof(f1437,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1436,f295])).

fof(f295,plain,
    ( m1_subset_1(sK7,k2_struct_0(sK5))
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl9_36
  <=> m1_subset_1(sK7,k2_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f1436,plain,
    ( ~ m1_subset_1(sK7,k2_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_32
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(forward_demodulation,[],[f1435,f387])).

fof(f1435,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_32
    | ~ spl9_41
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1434,f276])).

fof(f276,plain,
    ( m1_subset_1(sK7,k2_struct_0(sK4))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl9_32
  <=> m1_subset_1(sK7,k2_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f1434,plain,
    ( ~ m1_subset_1(sK7,k2_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_41
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(forward_demodulation,[],[f1433,f379])).

fof(f379,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl9_41
  <=> u1_struct_0(sK4) = k2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f1433,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1432,f194])).

fof(f194,plain,
    ( ~ v2_struct_0(sK2)
    | spl9_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl9_19
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f1432,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_21
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1431,f189])).

fof(f189,plain,
    ( v2_pre_topc(sK2)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl9_18
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f1431,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1430,f184])).

fof(f184,plain,
    ( l1_pre_topc(sK2)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl9_17
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f1430,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_21
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1429,f179])).

fof(f179,plain,
    ( ~ v2_struct_0(sK3)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl9_16
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f1429,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_21
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1428,f174])).

fof(f174,plain,
    ( v2_pre_topc(sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl9_15
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f1428,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_21
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1427,f169])).

fof(f169,plain,
    ( l1_pre_topc(sK3)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl9_14
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f1427,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_21
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1426,f164])).

fof(f164,plain,
    ( ~ v2_struct_0(sK4)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl9_13
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f1426,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | ~ spl9_21
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1425,f159])).

fof(f159,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl9_12
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f1425,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_21
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1424,f154])).

fof(f154,plain,
    ( ~ v2_struct_0(sK5)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl9_11
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f1424,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_21
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1423,f149])).

fof(f149,plain,
    ( m1_pre_topc(sK5,sK2)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl9_10
  <=> m1_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f1423,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_21
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1422,f144])).

fof(f144,plain,
    ( v1_funct_1(sK6)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_9
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f1422,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_21
    | ~ spl9_116
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1421,f1327])).

fof(f1327,plain,
    ( v1_tsep_1(sK4,sK5)
    | ~ spl9_136 ),
    inference(avatar_component_clause,[],[f1326])).

fof(f1326,plain,
    ( spl9_136
  <=> v1_tsep_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f1421,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_21
    | ~ spl9_116 ),
    inference(subsumption_resolution,[],[f1420,f1106])).

fof(f1106,plain,
    ( m1_pre_topc(sK4,sK5)
    | ~ spl9_116 ),
    inference(avatar_component_clause,[],[f1104])).

fof(f1104,plain,
    ( spl9_116
  <=> m1_pre_topc(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).

fof(f1420,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_pre_topc(sK4,sK5)
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1419,f104])).

fof(f104,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl9_1
  <=> r1_tmap_1(sK5,sK3,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f1419,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_pre_topc(sK4,sK5)
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_21 ),
    inference(resolution,[],[f98,f207])).

fof(f207,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl9_21
  <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f98,plain,(
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
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f1342,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_43
    | ~ spl9_47
    | ~ spl9_72
    | ~ spl9_122
    | ~ spl9_129
    | spl9_136 ),
    inference(avatar_contradiction_clause,[],[f1341])).

fof(f1341,plain,
    ( $false
    | spl9_11
    | spl9_13
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_43
    | ~ spl9_47
    | ~ spl9_72
    | ~ spl9_122
    | ~ spl9_129
    | spl9_136 ),
    inference(subsumption_resolution,[],[f1340,f1163])).

fof(f1163,plain,
    ( r1_tarski(k2_struct_0(sK4),k2_struct_0(sK5))
    | ~ spl9_122 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f1161,plain,
    ( spl9_122
  <=> r1_tarski(k2_struct_0(sK4),k2_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).

fof(f1340,plain,
    ( ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK5))
    | spl9_11
    | spl9_13
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_43
    | ~ spl9_47
    | ~ spl9_72
    | ~ spl9_129
    | spl9_136 ),
    inference(forward_demodulation,[],[f1339,f379])).

fof(f1339,plain,
    ( ~ r1_tarski(u1_struct_0(sK4),k2_struct_0(sK5))
    | spl9_11
    | spl9_13
    | ~ spl9_39
    | ~ spl9_42
    | ~ spl9_43
    | ~ spl9_47
    | ~ spl9_72
    | ~ spl9_129
    | spl9_136 ),
    inference(forward_demodulation,[],[f1337,f387])).

fof(f1337,plain,
    ( ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK5))
    | spl9_11
    | spl9_13
    | ~ spl9_39
    | ~ spl9_43
    | ~ spl9_47
    | ~ spl9_72
    | ~ spl9_129
    | spl9_136 ),
    inference(unit_resulting_resolution,[],[f164,f437,f315,f154,f1247,f397,f727,f1328,f87])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f1328,plain,
    ( ~ v1_tsep_1(sK4,sK5)
    | spl9_136 ),
    inference(avatar_component_clause,[],[f1326])).

fof(f727,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl9_72 ),
    inference(avatar_component_clause,[],[f725])).

fof(f725,plain,
    ( spl9_72
  <=> m1_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f397,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl9_43
  <=> m1_pre_topc(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f1247,plain,
    ( v1_tsep_1(sK4,sK4)
    | ~ spl9_129 ),
    inference(avatar_component_clause,[],[f1245])).

fof(f1245,plain,
    ( spl9_129
  <=> v1_tsep_1(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_129])])).

fof(f315,plain,
    ( l1_pre_topc(sK4)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl9_39
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f437,plain,
    ( v2_pre_topc(sK4)
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl9_47
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f1249,plain,
    ( spl9_129
    | ~ spl9_128 ),
    inference(avatar_split_clause,[],[f1243,f1220,f1245])).

fof(f1220,plain,
    ( spl9_128
  <=> sP0(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).

fof(f1243,plain,
    ( v1_tsep_1(sK4,sK4)
    | ~ spl9_128 ),
    inference(resolution,[],[f1222,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_pre_topc(X1,X0)
        & v1_tsep_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1222,plain,
    ( sP0(sK4,sK4)
    | ~ spl9_128 ),
    inference(avatar_component_clause,[],[f1220])).

fof(f1225,plain,
    ( spl9_128
    | ~ spl9_49
    | ~ spl9_95 ),
    inference(avatar_split_clause,[],[f1224,f911,f453,f1220])).

fof(f453,plain,
    ( spl9_49
  <=> v3_pre_topc(k2_struct_0(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f911,plain,
    ( spl9_95
  <=> sP1(sK4,k2_struct_0(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).

fof(f1224,plain,
    ( sP0(sK4,sK4)
    | ~ spl9_49
    | ~ spl9_95 ),
    inference(subsumption_resolution,[],[f1217,f455])).

fof(f455,plain,
    ( v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f453])).

fof(f1217,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK4),sK4)
    | sP0(sK4,sK4)
    | ~ spl9_95 ),
    inference(resolution,[],[f913,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | sP0(X0,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP0(X0,X2)
          | ~ v3_pre_topc(X1,X0) )
        & ( v3_pre_topc(X1,X0)
          | ~ sP0(X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X2,X1] :
      ( ( ( sP0(X0,X1)
          | ~ v3_pre_topc(X2,X0) )
        & ( v3_pre_topc(X2,X0)
          | ~ sP0(X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X1)
      <=> v3_pre_topc(X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f913,plain,
    ( sP1(sK4,k2_struct_0(sK4),sK4)
    | ~ spl9_95 ),
    inference(avatar_component_clause,[],[f911])).

fof(f1193,plain,
    ( spl9_122
    | ~ spl9_40
    | ~ spl9_41
    | ~ spl9_116 ),
    inference(avatar_split_clause,[],[f1141,f1104,f377,f322,f1161])).

fof(f322,plain,
    ( spl9_40
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f1141,plain,
    ( r1_tarski(k2_struct_0(sK4),k2_struct_0(sK5))
    | ~ spl9_40
    | ~ spl9_41
    | ~ spl9_116 ),
    inference(unit_resulting_resolution,[],[f323,f1106,f546])).

fof(f546,plain,
    ( ! [X0] :
        ( r1_tarski(k2_struct_0(sK4),k2_struct_0(X0))
        | ~ m1_pre_topc(sK4,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_41 ),
    inference(subsumption_resolution,[],[f539,f76])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f539,plain,
    ( ! [X0] :
        ( r1_tarski(k2_struct_0(sK4),k2_struct_0(X0))
        | ~ m1_pre_topc(sK4,X0)
        | ~ l1_pre_topc(X0)
        | ~ l1_struct_0(X0) )
    | ~ spl9_41 ),
    inference(superposition,[],[f475,f75])).

fof(f75,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f475,plain,
    ( ! [X4] :
        ( r1_tarski(k2_struct_0(sK4),u1_struct_0(X4))
        | ~ m1_pre_topc(sK4,X4)
        | ~ l1_pre_topc(X4) )
    | ~ spl9_41 ),
    inference(superposition,[],[f81,f379])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f323,plain,
    ( l1_pre_topc(sK5)
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f322])).

fof(f1107,plain,
    ( spl9_116
    | ~ spl9_31
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f1102,f395,f377,f314,f269,f1104])).

fof(f269,plain,
    ( spl9_31
  <=> sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f1102,plain,
    ( m1_pre_topc(sK4,sK5)
    | ~ spl9_31
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f1101,f271])).

fof(f271,plain,
    ( sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f269])).

fof(f1101,plain,
    ( m1_pre_topc(sK4,g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f1083,f379])).

fof(f1083,plain,
    ( m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl9_39
    | ~ spl9_43 ),
    inference(unit_resulting_resolution,[],[f315,f315,f397,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f914,plain,
    ( spl9_95
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f909,f435,f395,f377,f314,f911])).

fof(f909,plain,
    ( sP1(sK4,k2_struct_0(sK4),sK4)
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43
    | ~ spl9_47 ),
    inference(forward_demodulation,[],[f887,f379])).

fof(f887,plain,
    ( sP1(sK4,u1_struct_0(sK4),sK4)
    | ~ spl9_39
    | ~ spl9_43
    | ~ spl9_47 ),
    inference(unit_resulting_resolution,[],[f437,f315,f397,f196])).

fof(f196,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f100,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f38,f40,f39])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f728,plain,
    ( spl9_72
    | ~ spl9_31
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f723,f395,f377,f314,f269,f725])).

fof(f723,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl9_31
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f722,f271])).

fof(f722,plain,
    ( m1_pre_topc(g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)),sK4)
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f705,f379])).

fof(f705,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK4)
    | ~ spl9_39
    | ~ spl9_43 ),
    inference(unit_resulting_resolution,[],[f315,f397,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f456,plain,
    ( spl9_49
    | ~ spl9_39
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f451,f435,f314,f453])).

fof(f451,plain,
    ( v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ spl9_39
    | ~ spl9_47 ),
    inference(unit_resulting_resolution,[],[f315,f437,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f449,plain,
    ( spl9_47
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f448,f187,f182,f157,f435])).

fof(f448,plain,
    ( v2_pre_topc(sK4)
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f447,f189])).

fof(f447,plain,
    ( v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f428,f184])).

fof(f428,plain,
    ( v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_12 ),
    inference(resolution,[],[f90,f159])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f398,plain,
    ( spl9_43
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f392,f314,f395])).

fof(f392,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f315,f77])).

fof(f77,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f388,plain,
    ( spl9_42
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f383,f279,f385])).

fof(f279,plain,
    ( spl9_33
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f383,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl9_33 ),
    inference(unit_resulting_resolution,[],[f280,f75])).

fof(f280,plain,
    ( l1_struct_0(sK5)
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f279])).

fof(f380,plain,
    ( spl9_41
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f375,f265,f377])).

fof(f265,plain,
    ( spl9_30
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f375,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f266,f75])).

fof(f266,plain,
    ( l1_struct_0(sK4)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f265])).

fof(f372,plain,
    ( spl9_40
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f331,f182,f147,f322])).

fof(f331,plain,
    ( l1_pre_topc(sK5)
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(unit_resulting_resolution,[],[f184,f149,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f369,plain,
    ( spl9_39
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f334,f182,f157,f314])).

fof(f334,plain,
    ( l1_pre_topc(sK4)
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(unit_resulting_resolution,[],[f184,f159,f80])).

fof(f366,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))
    | ~ v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f365,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f326,plain,
    ( ~ spl9_40
    | spl9_33 ),
    inference(avatar_split_clause,[],[f320,f279,f322])).

fof(f320,plain,
    ( ~ l1_pre_topc(sK5)
    | spl9_33 ),
    inference(resolution,[],[f281,f76])).

fof(f281,plain,
    ( ~ l1_struct_0(sK5)
    | spl9_33 ),
    inference(avatar_component_clause,[],[f279])).

fof(f318,plain,
    ( ~ spl9_39
    | spl9_30 ),
    inference(avatar_split_clause,[],[f312,f265,f314])).

fof(f312,plain,
    ( ~ l1_pre_topc(sK4)
    | spl9_30 ),
    inference(resolution,[],[f267,f76])).

fof(f267,plain,
    ( ~ l1_struct_0(sK4)
    | spl9_30 ),
    inference(avatar_component_clause,[],[f265])).

fof(f296,plain,
    ( ~ spl9_33
    | spl9_36
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f241,f122,f293,f279])).

fof(f122,plain,
    ( spl9_5
  <=> m1_subset_1(sK7,u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f241,plain,
    ( m1_subset_1(sK7,k2_struct_0(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl9_5 ),
    inference(superposition,[],[f124,f75])).

fof(f124,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f291,plain,
    ( ~ spl9_33
    | spl9_35
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f240,f137,f288,f279])).

fof(f288,plain,
    ( spl9_35
  <=> v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f137,plain,
    ( spl9_8
  <=> v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f240,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(sK5)
    | ~ spl9_8 ),
    inference(superposition,[],[f139,f75])).

fof(f139,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f286,plain,
    ( ~ spl9_33
    | spl9_34
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f239,f132,f283,f279])).

fof(f283,plain,
    ( spl9_34
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f132,plain,
    ( spl9_7
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f239,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ spl9_7 ),
    inference(superposition,[],[f134,f75])).

fof(f134,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f132])).

fof(f277,plain,
    ( ~ spl9_30
    | spl9_32
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f238,f199,f274,f265])).

fof(f199,plain,
    ( spl9_20
  <=> m1_subset_1(sK7,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f238,plain,
    ( m1_subset_1(sK7,k2_struct_0(sK4))
    | ~ l1_struct_0(sK4)
    | ~ spl9_20 ),
    inference(superposition,[],[f201,f75])).

fof(f201,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f199])).

fof(f272,plain,
    ( ~ spl9_30
    | spl9_31
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f237,f127,f269,f265])).

fof(f127,plain,
    ( spl9_6
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f237,plain,
    ( sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ l1_struct_0(sK4)
    | ~ spl9_6 ),
    inference(superposition,[],[f129,f75])).

fof(f129,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f246,plain,
    ( spl9_26
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f234,f217,f243])).

fof(f217,plain,
    ( spl9_23
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f234,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl9_23 ),
    inference(unit_resulting_resolution,[],[f219,f75])).

fof(f219,plain,
    ( l1_struct_0(sK3)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f217])).

fof(f220,plain,
    ( spl9_23
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f209,f167,f217])).

fof(f209,plain,
    ( l1_struct_0(sK3)
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f169,f76])).

fof(f208,plain,
    ( spl9_21
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f203,f112,f107,f205])).

fof(f107,plain,
    ( spl9_2
  <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f112,plain,
    ( spl9_3
  <=> sK7 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f203,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f109,f114])).

fof(f114,plain,
    ( sK7 = sK8
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f109,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f202,plain,
    ( spl9_20
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f197,f117,f112,f199])).

fof(f117,plain,
    ( spl9_4
  <=> m1_subset_1(sK8,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f197,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(backward_demodulation,[],[f119,f114])).

fof(f119,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f195,plain,(
    ~ spl9_19 ),
    inference(avatar_split_clause,[],[f56,f192])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
    & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f18,f48,f47,f46,f45,f44,f43,f42])).

fof(f42,plain,
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
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,X1,X4,X5)
                            & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,sK3,X4,X5)
                          & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,sK3,X4,X5)
                        & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,sK3,X4,X5)
                      & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK4)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X3,sK3,X4,X5)
                    & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK5,sK3,X4,X5)
                  & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK4)) )
              & m1_subset_1(X5,u1_struct_0(sK5)) )
          & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK5,sK3,X4,X5)
                & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK4)) )
            & m1_subset_1(X5,u1_struct_0(sK5)) )
        & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK5,sK3,sK6,X5)
              & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK4)) )
          & m1_subset_1(X5,u1_struct_0(sK5)) )
      & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK5,sK3,sK6,X5)
            & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK4)) )
        & m1_subset_1(X5,u1_struct_0(sK5)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
          & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
          & sK7 = X6
          & m1_subset_1(X6,u1_struct_0(sK4)) )
      & m1_subset_1(sK7,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
        & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
        & sK7 = X6
        & m1_subset_1(X6,u1_struct_0(sK4)) )
   => ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
      & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
      & sK7 = sK8
      & m1_subset_1(sK8,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f190,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f57,f187])).

fof(f57,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f185,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f58,f182])).

fof(f58,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f180,plain,(
    ~ spl9_16 ),
    inference(avatar_split_clause,[],[f59,f177])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f175,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f60,f172])).

fof(f60,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f170,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f61,f167])).

fof(f61,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f165,plain,(
    ~ spl9_13 ),
    inference(avatar_split_clause,[],[f62,f162])).

fof(f62,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f160,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f63,f157])).

fof(f63,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f155,plain,(
    ~ spl9_11 ),
    inference(avatar_split_clause,[],[f64,f152])).

fof(f64,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f150,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f65,f147])).

fof(f65,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f145,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f66,f142])).

fof(f66,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f140,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f67,f137])).

fof(f67,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f135,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f68,f132])).

fof(f68,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f130,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f69,f127])).

fof(f69,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 ),
    inference(cnf_transformation,[],[f49])).

fof(f125,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f70,f122])).

fof(f70,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f49])).

fof(f120,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f71,f117])).

fof(f71,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f49])).

fof(f115,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f72,f112])).

fof(f72,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f49])).

fof(f110,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f73,f107])).

fof(f73,plain,(
    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    inference(cnf_transformation,[],[f49])).

fof(f105,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f74,f102])).

fof(f74,plain,(
    ~ r1_tmap_1(sK5,sK3,sK6,sK7) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:11:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (31083)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (31082)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (31092)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (31091)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (31093)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (31084)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (31088)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (31087)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (31078)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (31081)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (31080)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (31079)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (31077)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (31094)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.52  % (31096)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.52  % (31097)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.53  % (31098)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.53  % (31095)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.53  % (31085)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.53  % (31089)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (31086)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.54  % (31094)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f1445,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f175,f180,f185,f190,f195,f202,f208,f220,f246,f272,f277,f286,f291,f296,f318,f326,f365,f366,f369,f372,f380,f388,f398,f449,f456,f728,f914,f1107,f1193,f1225,f1249,f1342,f1444])).
% 0.20/0.54  fof(f1444,plain,(
% 0.20/0.54    spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_116 | ~spl9_136),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1443])).
% 0.20/0.54  fof(f1443,plain,(
% 0.20/0.54    $false | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1442,f308])).
% 0.20/0.54  fof(f308,plain,(
% 0.20/0.54    v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) | ~spl9_38),
% 0.20/0.54    inference(avatar_component_clause,[],[f307])).
% 0.20/0.54  fof(f307,plain,(
% 0.20/0.54    spl9_38 <=> v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 0.20/0.54  fof(f1442,plain,(
% 0.20/0.54    ~v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_41 | ~spl9_42 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(forward_demodulation,[],[f1441,f387])).
% 0.20/0.54  fof(f387,plain,(
% 0.20/0.54    u1_struct_0(sK5) = k2_struct_0(sK5) | ~spl9_42),
% 0.20/0.54    inference(avatar_component_clause,[],[f385])).
% 0.20/0.54  fof(f385,plain,(
% 0.20/0.54    spl9_42 <=> u1_struct_0(sK5) = k2_struct_0(sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 0.20/0.54  fof(f1441,plain,(
% 0.20/0.54    ~v1_funct_2(sK6,u1_struct_0(sK5),k2_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_41 | ~spl9_42 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(forward_demodulation,[],[f1440,f245])).
% 0.20/0.54  fof(f245,plain,(
% 0.20/0.54    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl9_26),
% 0.20/0.54    inference(avatar_component_clause,[],[f243])).
% 0.20/0.54  fof(f243,plain,(
% 0.20/0.54    spl9_26 <=> u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.20/0.54  fof(f1440,plain,(
% 0.20/0.54    ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_41 | ~spl9_42 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1439,f303])).
% 0.20/0.54  fof(f303,plain,(
% 0.20/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) | ~spl9_37),
% 0.20/0.54    inference(avatar_component_clause,[],[f302])).
% 0.20/0.54  fof(f302,plain,(
% 0.20/0.54    spl9_37 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 0.20/0.54  fof(f1439,plain,(
% 0.20/0.54    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_41 | ~spl9_42 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(forward_demodulation,[],[f1438,f387])).
% 0.20/0.54  fof(f1438,plain,(
% 0.20/0.54    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_41 | ~spl9_42 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(forward_demodulation,[],[f1437,f245])).
% 0.20/0.54  fof(f1437,plain,(
% 0.20/0.54    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_32 | ~spl9_36 | ~spl9_41 | ~spl9_42 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1436,f295])).
% 0.20/0.54  fof(f295,plain,(
% 0.20/0.54    m1_subset_1(sK7,k2_struct_0(sK5)) | ~spl9_36),
% 0.20/0.54    inference(avatar_component_clause,[],[f293])).
% 0.20/0.54  fof(f293,plain,(
% 0.20/0.54    spl9_36 <=> m1_subset_1(sK7,k2_struct_0(sK5))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 0.20/0.54  fof(f1436,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,k2_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_32 | ~spl9_41 | ~spl9_42 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(forward_demodulation,[],[f1435,f387])).
% 0.20/0.54  fof(f1435,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_32 | ~spl9_41 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1434,f276])).
% 0.20/0.54  fof(f276,plain,(
% 0.20/0.54    m1_subset_1(sK7,k2_struct_0(sK4)) | ~spl9_32),
% 0.20/0.54    inference(avatar_component_clause,[],[f274])).
% 0.20/0.54  fof(f274,plain,(
% 0.20/0.54    spl9_32 <=> m1_subset_1(sK7,k2_struct_0(sK4))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 0.20/0.54  fof(f1434,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,k2_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_41 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(forward_demodulation,[],[f1433,f379])).
% 0.20/0.54  fof(f379,plain,(
% 0.20/0.54    u1_struct_0(sK4) = k2_struct_0(sK4) | ~spl9_41),
% 0.20/0.54    inference(avatar_component_clause,[],[f377])).
% 0.20/0.54  fof(f377,plain,(
% 0.20/0.54    spl9_41 <=> u1_struct_0(sK4) = k2_struct_0(sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 0.20/0.54  fof(f1433,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1432,f194])).
% 0.20/0.54  fof(f194,plain,(
% 0.20/0.54    ~v2_struct_0(sK2) | spl9_19),
% 0.20/0.54    inference(avatar_component_clause,[],[f192])).
% 0.20/0.54  fof(f192,plain,(
% 0.20/0.54    spl9_19 <=> v2_struct_0(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.20/0.54  fof(f1432,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_21 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1431,f189])).
% 0.20/0.54  fof(f189,plain,(
% 0.20/0.54    v2_pre_topc(sK2) | ~spl9_18),
% 0.20/0.54    inference(avatar_component_clause,[],[f187])).
% 0.20/0.54  fof(f187,plain,(
% 0.20/0.54    spl9_18 <=> v2_pre_topc(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.20/0.54  fof(f1431,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_21 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1430,f184])).
% 0.20/0.54  fof(f184,plain,(
% 0.20/0.54    l1_pre_topc(sK2) | ~spl9_17),
% 0.20/0.54    inference(avatar_component_clause,[],[f182])).
% 0.20/0.54  fof(f182,plain,(
% 0.20/0.54    spl9_17 <=> l1_pre_topc(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.20/0.54  fof(f1430,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_21 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1429,f179])).
% 0.20/0.54  fof(f179,plain,(
% 0.20/0.54    ~v2_struct_0(sK3) | spl9_16),
% 0.20/0.54    inference(avatar_component_clause,[],[f177])).
% 0.20/0.54  fof(f177,plain,(
% 0.20/0.54    spl9_16 <=> v2_struct_0(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.20/0.54  fof(f1429,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_21 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1428,f174])).
% 0.20/0.54  fof(f174,plain,(
% 0.20/0.54    v2_pre_topc(sK3) | ~spl9_15),
% 0.20/0.54    inference(avatar_component_clause,[],[f172])).
% 0.20/0.54  fof(f172,plain,(
% 0.20/0.54    spl9_15 <=> v2_pre_topc(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.20/0.54  fof(f1428,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_21 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1427,f169])).
% 0.20/0.54  fof(f169,plain,(
% 0.20/0.54    l1_pre_topc(sK3) | ~spl9_14),
% 0.20/0.54    inference(avatar_component_clause,[],[f167])).
% 0.20/0.54  fof(f167,plain,(
% 0.20/0.54    spl9_14 <=> l1_pre_topc(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.20/0.54  fof(f1427,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_21 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1426,f164])).
% 0.20/0.54  fof(f164,plain,(
% 0.20/0.54    ~v2_struct_0(sK4) | spl9_13),
% 0.20/0.54    inference(avatar_component_clause,[],[f162])).
% 0.20/0.54  fof(f162,plain,(
% 0.20/0.54    spl9_13 <=> v2_struct_0(sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.20/0.54  fof(f1426,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | ~spl9_21 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1425,f159])).
% 0.20/0.54  fof(f159,plain,(
% 0.20/0.54    m1_pre_topc(sK4,sK2) | ~spl9_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f157])).
% 0.20/0.54  fof(f157,plain,(
% 0.20/0.54    spl9_12 <=> m1_pre_topc(sK4,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.20/0.54  fof(f1425,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_21 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1424,f154])).
% 0.20/0.54  fof(f154,plain,(
% 0.20/0.54    ~v2_struct_0(sK5) | spl9_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f152])).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    spl9_11 <=> v2_struct_0(sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.20/0.54  fof(f1424,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | ~spl9_21 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1423,f149])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    m1_pre_topc(sK5,sK2) | ~spl9_10),
% 0.20/0.54    inference(avatar_component_clause,[],[f147])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    spl9_10 <=> m1_pre_topc(sK5,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.20/0.54  fof(f1423,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_21 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1422,f144])).
% 0.20/0.54  fof(f144,plain,(
% 0.20/0.54    v1_funct_1(sK6) | ~spl9_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f142])).
% 0.20/0.54  fof(f142,plain,(
% 0.20/0.54    spl9_9 <=> v1_funct_1(sK6)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.20/0.54  fof(f1422,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_21 | ~spl9_116 | ~spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1421,f1327])).
% 0.20/0.54  fof(f1327,plain,(
% 0.20/0.54    v1_tsep_1(sK4,sK5) | ~spl9_136),
% 0.20/0.54    inference(avatar_component_clause,[],[f1326])).
% 0.20/0.54  fof(f1326,plain,(
% 0.20/0.54    spl9_136 <=> v1_tsep_1(sK4,sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).
% 0.20/0.54  fof(f1421,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_21 | ~spl9_116)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1420,f1106])).
% 0.20/0.54  fof(f1106,plain,(
% 0.20/0.54    m1_pre_topc(sK4,sK5) | ~spl9_116),
% 0.20/0.54    inference(avatar_component_clause,[],[f1104])).
% 0.20/0.54  fof(f1104,plain,(
% 0.20/0.54    spl9_116 <=> m1_pre_topc(sK4,sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).
% 0.20/0.54  fof(f1420,plain,(
% 0.20/0.54    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,sK5) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_21)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1419,f104])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    ~r1_tmap_1(sK5,sK3,sK6,sK7) | spl9_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f102])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    spl9_1 <=> r1_tmap_1(sK5,sK3,sK6,sK7)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.54  fof(f1419,plain,(
% 0.20/0.54    r1_tmap_1(sK5,sK3,sK6,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,sK5) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl9_21),
% 0.20/0.54    inference(resolution,[],[f98,f207])).
% 0.20/0.54  fof(f207,plain,(
% 0.20/0.54    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) | ~spl9_21),
% 0.20/0.54    inference(avatar_component_clause,[],[f205])).
% 0.20/0.54  fof(f205,plain,(
% 0.20/0.54    spl9_21 <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f86])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.20/0.54  fof(f1342,plain,(
% 0.20/0.54    spl9_11 | spl9_13 | ~spl9_39 | ~spl9_41 | ~spl9_42 | ~spl9_43 | ~spl9_47 | ~spl9_72 | ~spl9_122 | ~spl9_129 | spl9_136),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1341])).
% 0.20/0.54  fof(f1341,plain,(
% 0.20/0.54    $false | (spl9_11 | spl9_13 | ~spl9_39 | ~spl9_41 | ~spl9_42 | ~spl9_43 | ~spl9_47 | ~spl9_72 | ~spl9_122 | ~spl9_129 | spl9_136)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1340,f1163])).
% 0.20/0.54  fof(f1163,plain,(
% 0.20/0.54    r1_tarski(k2_struct_0(sK4),k2_struct_0(sK5)) | ~spl9_122),
% 0.20/0.54    inference(avatar_component_clause,[],[f1161])).
% 0.20/0.54  fof(f1161,plain,(
% 0.20/0.54    spl9_122 <=> r1_tarski(k2_struct_0(sK4),k2_struct_0(sK5))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).
% 0.20/0.54  fof(f1340,plain,(
% 0.20/0.54    ~r1_tarski(k2_struct_0(sK4),k2_struct_0(sK5)) | (spl9_11 | spl9_13 | ~spl9_39 | ~spl9_41 | ~spl9_42 | ~spl9_43 | ~spl9_47 | ~spl9_72 | ~spl9_129 | spl9_136)),
% 0.20/0.54    inference(forward_demodulation,[],[f1339,f379])).
% 0.20/0.54  fof(f1339,plain,(
% 0.20/0.54    ~r1_tarski(u1_struct_0(sK4),k2_struct_0(sK5)) | (spl9_11 | spl9_13 | ~spl9_39 | ~spl9_42 | ~spl9_43 | ~spl9_47 | ~spl9_72 | ~spl9_129 | spl9_136)),
% 0.20/0.54    inference(forward_demodulation,[],[f1337,f387])).
% 0.20/0.54  fof(f1337,plain,(
% 0.20/0.54    ~r1_tarski(u1_struct_0(sK4),u1_struct_0(sK5)) | (spl9_11 | spl9_13 | ~spl9_39 | ~spl9_43 | ~spl9_47 | ~spl9_72 | ~spl9_129 | spl9_136)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f164,f437,f315,f154,f1247,f397,f727,f1328,f87])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).
% 0.20/0.54  fof(f1328,plain,(
% 0.20/0.54    ~v1_tsep_1(sK4,sK5) | spl9_136),
% 0.20/0.54    inference(avatar_component_clause,[],[f1326])).
% 0.20/0.54  fof(f727,plain,(
% 0.20/0.54    m1_pre_topc(sK5,sK4) | ~spl9_72),
% 0.20/0.54    inference(avatar_component_clause,[],[f725])).
% 0.20/0.54  fof(f725,plain,(
% 0.20/0.54    spl9_72 <=> m1_pre_topc(sK5,sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).
% 0.20/0.54  fof(f397,plain,(
% 0.20/0.54    m1_pre_topc(sK4,sK4) | ~spl9_43),
% 0.20/0.54    inference(avatar_component_clause,[],[f395])).
% 0.20/0.54  fof(f395,plain,(
% 0.20/0.54    spl9_43 <=> m1_pre_topc(sK4,sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 0.20/0.54  fof(f1247,plain,(
% 0.20/0.54    v1_tsep_1(sK4,sK4) | ~spl9_129),
% 0.20/0.54    inference(avatar_component_clause,[],[f1245])).
% 0.20/0.54  fof(f1245,plain,(
% 0.20/0.54    spl9_129 <=> v1_tsep_1(sK4,sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_129])])).
% 0.20/0.54  fof(f315,plain,(
% 0.20/0.54    l1_pre_topc(sK4) | ~spl9_39),
% 0.20/0.54    inference(avatar_component_clause,[],[f314])).
% 0.20/0.54  fof(f314,plain,(
% 0.20/0.54    spl9_39 <=> l1_pre_topc(sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 0.20/0.54  fof(f437,plain,(
% 0.20/0.54    v2_pre_topc(sK4) | ~spl9_47),
% 0.20/0.54    inference(avatar_component_clause,[],[f435])).
% 0.20/0.54  fof(f435,plain,(
% 0.20/0.54    spl9_47 <=> v2_pre_topc(sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 0.20/0.54  fof(f1249,plain,(
% 0.20/0.54    spl9_129 | ~spl9_128),
% 0.20/0.54    inference(avatar_split_clause,[],[f1243,f1220,f1245])).
% 0.20/0.54  fof(f1220,plain,(
% 0.20/0.54    spl9_128 <=> sP0(sK4,sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).
% 0.20/0.54  fof(f1243,plain,(
% 0.20/0.54    v1_tsep_1(sK4,sK4) | ~spl9_128),
% 0.20/0.54    inference(resolution,[],[f1222,f94])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~sP0(X0,X1) | v1_tsep_1(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ! [X0,X1] : ((sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 0.20/0.54    inference(flattening,[],[f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ! [X0,X1] : ((sP0(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0,X1] : (sP0(X0,X1) <=> (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.54  fof(f1222,plain,(
% 0.20/0.54    sP0(sK4,sK4) | ~spl9_128),
% 0.20/0.54    inference(avatar_component_clause,[],[f1220])).
% 0.20/0.54  fof(f1225,plain,(
% 0.20/0.54    spl9_128 | ~spl9_49 | ~spl9_95),
% 0.20/0.54    inference(avatar_split_clause,[],[f1224,f911,f453,f1220])).
% 0.20/0.54  fof(f453,plain,(
% 0.20/0.54    spl9_49 <=> v3_pre_topc(k2_struct_0(sK4),sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 0.20/0.54  fof(f911,plain,(
% 0.20/0.54    spl9_95 <=> sP1(sK4,k2_struct_0(sK4),sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).
% 0.20/0.54  fof(f1224,plain,(
% 0.20/0.54    sP0(sK4,sK4) | (~spl9_49 | ~spl9_95)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1217,f455])).
% 0.20/0.54  fof(f455,plain,(
% 0.20/0.54    v3_pre_topc(k2_struct_0(sK4),sK4) | ~spl9_49),
% 0.20/0.54    inference(avatar_component_clause,[],[f453])).
% 0.20/0.54  fof(f1217,plain,(
% 0.20/0.54    ~v3_pre_topc(k2_struct_0(sK4),sK4) | sP0(sK4,sK4) | ~spl9_95),
% 0.20/0.54    inference(resolution,[],[f913,f93])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v3_pre_topc(X1,X0) | sP0(X0,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((sP0(X0,X2) | ~v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) | ~sP0(X0,X2))) | ~sP1(X0,X1,X2))),
% 0.20/0.54    inference(rectify,[],[f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ! [X0,X2,X1] : (((sP0(X0,X1) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~sP0(X0,X1))) | ~sP1(X0,X2,X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ! [X0,X2,X1] : ((sP0(X0,X1) <=> v3_pre_topc(X2,X0)) | ~sP1(X0,X2,X1))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.54  fof(f913,plain,(
% 0.20/0.54    sP1(sK4,k2_struct_0(sK4),sK4) | ~spl9_95),
% 0.20/0.54    inference(avatar_component_clause,[],[f911])).
% 0.20/0.54  fof(f1193,plain,(
% 0.20/0.54    spl9_122 | ~spl9_40 | ~spl9_41 | ~spl9_116),
% 0.20/0.54    inference(avatar_split_clause,[],[f1141,f1104,f377,f322,f1161])).
% 0.20/0.54  fof(f322,plain,(
% 0.20/0.54    spl9_40 <=> l1_pre_topc(sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 0.20/0.54  fof(f1141,plain,(
% 0.20/0.54    r1_tarski(k2_struct_0(sK4),k2_struct_0(sK5)) | (~spl9_40 | ~spl9_41 | ~spl9_116)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f323,f1106,f546])).
% 0.20/0.54  fof(f546,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k2_struct_0(sK4),k2_struct_0(X0)) | ~m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0)) ) | ~spl9_41),
% 0.20/0.54    inference(subsumption_resolution,[],[f539,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.54  fof(f539,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k2_struct_0(sK4),k2_struct_0(X0)) | ~m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0) | ~l1_struct_0(X0)) ) | ~spl9_41),
% 0.20/0.54    inference(superposition,[],[f475,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.55  fof(f475,plain,(
% 0.20/0.55    ( ! [X4] : (r1_tarski(k2_struct_0(sK4),u1_struct_0(X4)) | ~m1_pre_topc(sK4,X4) | ~l1_pre_topc(X4)) ) | ~spl9_41),
% 0.20/0.55    inference(superposition,[],[f81,f379])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.20/0.55  fof(f323,plain,(
% 0.20/0.55    l1_pre_topc(sK5) | ~spl9_40),
% 0.20/0.55    inference(avatar_component_clause,[],[f322])).
% 0.20/0.55  fof(f1107,plain,(
% 0.20/0.55    spl9_116 | ~spl9_31 | ~spl9_39 | ~spl9_41 | ~spl9_43),
% 0.20/0.55    inference(avatar_split_clause,[],[f1102,f395,f377,f314,f269,f1104])).
% 0.20/0.55  fof(f269,plain,(
% 0.20/0.55    spl9_31 <=> sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 0.20/0.55  fof(f1102,plain,(
% 0.20/0.55    m1_pre_topc(sK4,sK5) | (~spl9_31 | ~spl9_39 | ~spl9_41 | ~spl9_43)),
% 0.20/0.55    inference(forward_demodulation,[],[f1101,f271])).
% 0.20/0.55  fof(f271,plain,(
% 0.20/0.55    sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~spl9_31),
% 0.20/0.55    inference(avatar_component_clause,[],[f269])).
% 0.20/0.55  fof(f1101,plain,(
% 0.20/0.55    m1_pre_topc(sK4,g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))) | (~spl9_39 | ~spl9_41 | ~spl9_43)),
% 0.20/0.55    inference(forward_demodulation,[],[f1083,f379])).
% 0.20/0.55  fof(f1083,plain,(
% 0.20/0.55    m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | (~spl9_39 | ~spl9_43)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f315,f315,f397,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.20/0.55  fof(f914,plain,(
% 0.20/0.55    spl9_95 | ~spl9_39 | ~spl9_41 | ~spl9_43 | ~spl9_47),
% 0.20/0.55    inference(avatar_split_clause,[],[f909,f435,f395,f377,f314,f911])).
% 0.20/0.55  fof(f909,plain,(
% 0.20/0.55    sP1(sK4,k2_struct_0(sK4),sK4) | (~spl9_39 | ~spl9_41 | ~spl9_43 | ~spl9_47)),
% 0.20/0.55    inference(forward_demodulation,[],[f887,f379])).
% 0.20/0.55  fof(f887,plain,(
% 0.20/0.55    sP1(sK4,u1_struct_0(sK4),sK4) | (~spl9_39 | ~spl9_43 | ~spl9_47)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f437,f315,f397,f196])).
% 0.20/0.55  fof(f196,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f100,f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f97])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.55    inference(definition_folding,[],[f38,f40,f39])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.20/0.55  fof(f728,plain,(
% 0.20/0.55    spl9_72 | ~spl9_31 | ~spl9_39 | ~spl9_41 | ~spl9_43),
% 0.20/0.55    inference(avatar_split_clause,[],[f723,f395,f377,f314,f269,f725])).
% 0.20/0.55  fof(f723,plain,(
% 0.20/0.55    m1_pre_topc(sK5,sK4) | (~spl9_31 | ~spl9_39 | ~spl9_41 | ~spl9_43)),
% 0.20/0.55    inference(forward_demodulation,[],[f722,f271])).
% 0.20/0.55  fof(f722,plain,(
% 0.20/0.55    m1_pre_topc(g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)),sK4) | (~spl9_39 | ~spl9_41 | ~spl9_43)),
% 0.20/0.55    inference(forward_demodulation,[],[f705,f379])).
% 0.20/0.55  fof(f705,plain,(
% 0.20/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK4) | (~spl9_39 | ~spl9_43)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f315,f397,f84])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.20/0.55  fof(f456,plain,(
% 0.20/0.55    spl9_49 | ~spl9_39 | ~spl9_47),
% 0.20/0.55    inference(avatar_split_clause,[],[f451,f435,f314,f453])).
% 0.20/0.55  fof(f451,plain,(
% 0.20/0.55    v3_pre_topc(k2_struct_0(sK4),sK4) | (~spl9_39 | ~spl9_47)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f315,f437,f89])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.20/0.55  fof(f449,plain,(
% 0.20/0.55    spl9_47 | ~spl9_12 | ~spl9_17 | ~spl9_18),
% 0.20/0.55    inference(avatar_split_clause,[],[f448,f187,f182,f157,f435])).
% 0.20/0.55  fof(f448,plain,(
% 0.20/0.55    v2_pre_topc(sK4) | (~spl9_12 | ~spl9_17 | ~spl9_18)),
% 0.20/0.55    inference(subsumption_resolution,[],[f447,f189])).
% 0.20/0.55  fof(f447,plain,(
% 0.20/0.55    v2_pre_topc(sK4) | ~v2_pre_topc(sK2) | (~spl9_12 | ~spl9_17)),
% 0.20/0.55    inference(subsumption_resolution,[],[f428,f184])).
% 0.20/0.55  fof(f428,plain,(
% 0.20/0.55    v2_pre_topc(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~spl9_12),
% 0.20/0.55    inference(resolution,[],[f90,f159])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.55  fof(f398,plain,(
% 0.20/0.55    spl9_43 | ~spl9_39),
% 0.20/0.55    inference(avatar_split_clause,[],[f392,f314,f395])).
% 0.20/0.55  fof(f392,plain,(
% 0.20/0.55    m1_pre_topc(sK4,sK4) | ~spl9_39),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f315,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.55  fof(f388,plain,(
% 0.20/0.55    spl9_42 | ~spl9_33),
% 0.20/0.55    inference(avatar_split_clause,[],[f383,f279,f385])).
% 0.20/0.55  fof(f279,plain,(
% 0.20/0.55    spl9_33 <=> l1_struct_0(sK5)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 0.20/0.55  fof(f383,plain,(
% 0.20/0.55    u1_struct_0(sK5) = k2_struct_0(sK5) | ~spl9_33),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f280,f75])).
% 0.20/0.55  fof(f280,plain,(
% 0.20/0.55    l1_struct_0(sK5) | ~spl9_33),
% 0.20/0.55    inference(avatar_component_clause,[],[f279])).
% 0.20/0.55  fof(f380,plain,(
% 0.20/0.55    spl9_41 | ~spl9_30),
% 0.20/0.55    inference(avatar_split_clause,[],[f375,f265,f377])).
% 0.20/0.55  fof(f265,plain,(
% 0.20/0.55    spl9_30 <=> l1_struct_0(sK4)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 0.20/0.55  fof(f375,plain,(
% 0.20/0.55    u1_struct_0(sK4) = k2_struct_0(sK4) | ~spl9_30),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f266,f75])).
% 0.20/0.55  fof(f266,plain,(
% 0.20/0.55    l1_struct_0(sK4) | ~spl9_30),
% 0.20/0.55    inference(avatar_component_clause,[],[f265])).
% 0.20/0.55  fof(f372,plain,(
% 0.20/0.55    spl9_40 | ~spl9_10 | ~spl9_17),
% 0.20/0.55    inference(avatar_split_clause,[],[f331,f182,f147,f322])).
% 0.20/0.55  fof(f331,plain,(
% 0.20/0.55    l1_pre_topc(sK5) | (~spl9_10 | ~spl9_17)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f184,f149,f80])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.55  fof(f369,plain,(
% 0.20/0.55    spl9_39 | ~spl9_12 | ~spl9_17),
% 0.20/0.55    inference(avatar_split_clause,[],[f334,f182,f157,f314])).
% 0.20/0.55  fof(f334,plain,(
% 0.20/0.55    l1_pre_topc(sK4) | (~spl9_12 | ~spl9_17)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f184,f159,f80])).
% 0.20/0.55  fof(f366,plain,(
% 0.20/0.55    u1_struct_0(sK3) != k2_struct_0(sK3) | v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) | ~v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3))),
% 0.20/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.55  fof(f365,plain,(
% 0.20/0.55    u1_struct_0(sK3) != k2_struct_0(sK3) | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3))))),
% 0.20/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.55  fof(f326,plain,(
% 0.20/0.55    ~spl9_40 | spl9_33),
% 0.20/0.55    inference(avatar_split_clause,[],[f320,f279,f322])).
% 0.20/0.55  fof(f320,plain,(
% 0.20/0.55    ~l1_pre_topc(sK5) | spl9_33),
% 0.20/0.55    inference(resolution,[],[f281,f76])).
% 0.20/0.55  fof(f281,plain,(
% 0.20/0.55    ~l1_struct_0(sK5) | spl9_33),
% 0.20/0.55    inference(avatar_component_clause,[],[f279])).
% 0.20/0.55  fof(f318,plain,(
% 0.20/0.55    ~spl9_39 | spl9_30),
% 0.20/0.55    inference(avatar_split_clause,[],[f312,f265,f314])).
% 0.20/0.55  fof(f312,plain,(
% 0.20/0.55    ~l1_pre_topc(sK4) | spl9_30),
% 0.20/0.55    inference(resolution,[],[f267,f76])).
% 0.20/0.55  fof(f267,plain,(
% 0.20/0.55    ~l1_struct_0(sK4) | spl9_30),
% 0.20/0.55    inference(avatar_component_clause,[],[f265])).
% 0.20/0.55  fof(f296,plain,(
% 0.20/0.55    ~spl9_33 | spl9_36 | ~spl9_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f241,f122,f293,f279])).
% 0.20/0.55  fof(f122,plain,(
% 0.20/0.55    spl9_5 <=> m1_subset_1(sK7,u1_struct_0(sK5))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.20/0.55  fof(f241,plain,(
% 0.20/0.55    m1_subset_1(sK7,k2_struct_0(sK5)) | ~l1_struct_0(sK5) | ~spl9_5),
% 0.20/0.55    inference(superposition,[],[f124,f75])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    m1_subset_1(sK7,u1_struct_0(sK5)) | ~spl9_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f122])).
% 0.20/0.55  fof(f291,plain,(
% 0.20/0.55    ~spl9_33 | spl9_35 | ~spl9_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f240,f137,f288,f279])).
% 0.20/0.55  fof(f288,plain,(
% 0.20/0.55    spl9_35 <=> v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    spl9_8 <=> v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.20/0.55  fof(f240,plain,(
% 0.20/0.55    v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3)) | ~l1_struct_0(sK5) | ~spl9_8),
% 0.20/0.55    inference(superposition,[],[f139,f75])).
% 0.20/0.55  fof(f139,plain,(
% 0.20/0.55    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~spl9_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f137])).
% 0.20/0.55  fof(f286,plain,(
% 0.20/0.55    ~spl9_33 | spl9_34 | ~spl9_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f239,f132,f283,f279])).
% 0.20/0.55  fof(f283,plain,(
% 0.20/0.55    spl9_34 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3))))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    spl9_7 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.20/0.55  fof(f239,plain,(
% 0.20/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3)))) | ~l1_struct_0(sK5) | ~spl9_7),
% 0.20/0.55    inference(superposition,[],[f134,f75])).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~spl9_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f132])).
% 0.20/0.55  fof(f277,plain,(
% 0.20/0.55    ~spl9_30 | spl9_32 | ~spl9_20),
% 0.20/0.55    inference(avatar_split_clause,[],[f238,f199,f274,f265])).
% 0.20/0.55  fof(f199,plain,(
% 0.20/0.55    spl9_20 <=> m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    m1_subset_1(sK7,k2_struct_0(sK4)) | ~l1_struct_0(sK4) | ~spl9_20),
% 0.20/0.55    inference(superposition,[],[f201,f75])).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    m1_subset_1(sK7,u1_struct_0(sK4)) | ~spl9_20),
% 0.20/0.55    inference(avatar_component_clause,[],[f199])).
% 0.20/0.55  fof(f272,plain,(
% 0.20/0.55    ~spl9_30 | spl9_31 | ~spl9_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f237,f127,f269,f265])).
% 0.20/0.55  fof(f127,plain,(
% 0.20/0.55    spl9_6 <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.20/0.55  fof(f237,plain,(
% 0.20/0.55    sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~l1_struct_0(sK4) | ~spl9_6),
% 0.20/0.55    inference(superposition,[],[f129,f75])).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 | ~spl9_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f127])).
% 0.20/0.55  fof(f246,plain,(
% 0.20/0.55    spl9_26 | ~spl9_23),
% 0.20/0.55    inference(avatar_split_clause,[],[f234,f217,f243])).
% 0.20/0.55  fof(f217,plain,(
% 0.20/0.55    spl9_23 <=> l1_struct_0(sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.20/0.55  fof(f234,plain,(
% 0.20/0.55    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl9_23),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f219,f75])).
% 0.20/0.55  fof(f219,plain,(
% 0.20/0.55    l1_struct_0(sK3) | ~spl9_23),
% 0.20/0.55    inference(avatar_component_clause,[],[f217])).
% 0.20/0.55  fof(f220,plain,(
% 0.20/0.55    spl9_23 | ~spl9_14),
% 0.20/0.55    inference(avatar_split_clause,[],[f209,f167,f217])).
% 0.20/0.55  fof(f209,plain,(
% 0.20/0.55    l1_struct_0(sK3) | ~spl9_14),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f169,f76])).
% 0.20/0.55  fof(f208,plain,(
% 0.20/0.55    spl9_21 | ~spl9_2 | ~spl9_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f203,f112,f107,f205])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    spl9_2 <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    spl9_3 <=> sK7 = sK8),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.20/0.55  fof(f203,plain,(
% 0.20/0.55    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) | (~spl9_2 | ~spl9_3)),
% 0.20/0.55    inference(forward_demodulation,[],[f109,f114])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    sK7 = sK8 | ~spl9_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f112])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | ~spl9_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f107])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    spl9_20 | ~spl9_3 | ~spl9_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f197,f117,f112,f199])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    spl9_4 <=> m1_subset_1(sK8,u1_struct_0(sK4))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.20/0.55  fof(f197,plain,(
% 0.20/0.55    m1_subset_1(sK7,u1_struct_0(sK4)) | (~spl9_3 | ~spl9_4)),
% 0.20/0.55    inference(backward_demodulation,[],[f119,f114])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    m1_subset_1(sK8,u1_struct_0(sK4)) | ~spl9_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f117])).
% 0.20/0.55  fof(f195,plain,(
% 0.20/0.55    ~spl9_19),
% 0.20/0.55    inference(avatar_split_clause,[],[f56,f192])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ~v2_struct_0(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ((((((~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f18,f48,f47,f46,f45,f44,f43,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,sK6,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,sK6,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) => (? [X6] : (~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ? [X6] : (~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) => (~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,negated_conjecture,(
% 0.20/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.20/0.55    inference(negated_conjecture,[],[f15])).
% 0.20/0.55  fof(f15,conjecture,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.20/0.55  fof(f190,plain,(
% 0.20/0.55    spl9_18),
% 0.20/0.55    inference(avatar_split_clause,[],[f57,f187])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    v2_pre_topc(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f185,plain,(
% 0.20/0.55    spl9_17),
% 0.20/0.55    inference(avatar_split_clause,[],[f58,f182])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    l1_pre_topc(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f180,plain,(
% 0.20/0.55    ~spl9_16),
% 0.20/0.55    inference(avatar_split_clause,[],[f59,f177])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ~v2_struct_0(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f175,plain,(
% 0.20/0.55    spl9_15),
% 0.20/0.55    inference(avatar_split_clause,[],[f60,f172])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    v2_pre_topc(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    spl9_14),
% 0.20/0.55    inference(avatar_split_clause,[],[f61,f167])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    l1_pre_topc(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f165,plain,(
% 0.20/0.55    ~spl9_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f62,f162])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ~v2_struct_0(sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f160,plain,(
% 0.20/0.55    spl9_12),
% 0.20/0.55    inference(avatar_split_clause,[],[f63,f157])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    m1_pre_topc(sK4,sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f155,plain,(
% 0.20/0.55    ~spl9_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f64,f152])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ~v2_struct_0(sK5)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f150,plain,(
% 0.20/0.55    spl9_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f65,f147])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    m1_pre_topc(sK5,sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    spl9_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f66,f142])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    v1_funct_1(sK6)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f140,plain,(
% 0.20/0.55    spl9_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f67,f137])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    spl9_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f68,f132])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f130,plain,(
% 0.20/0.55    spl9_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f69,f127])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    spl9_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f70,f122])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    m1_subset_1(sK7,u1_struct_0(sK5))),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    spl9_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f71,f117])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    m1_subset_1(sK8,u1_struct_0(sK4))),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    spl9_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f72,f112])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    sK7 = sK8),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    spl9_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f73,f107])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    ~spl9_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f74,f102])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ~r1_tmap_1(sK5,sK3,sK6,sK7)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (31094)------------------------------
% 0.20/0.55  % (31094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31094)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (31094)Memory used [KB]: 11641
% 0.20/0.55  % (31094)Time elapsed: 0.107 s
% 0.20/0.55  % (31094)------------------------------
% 0.20/0.55  % (31094)------------------------------
% 0.20/0.55  % (31072)Success in time 0.189 s
%------------------------------------------------------------------------------

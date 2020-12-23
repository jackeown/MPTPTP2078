%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t89_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:21 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  364 (1030 expanded)
%              Number of leaves         :   66 ( 393 expanded)
%              Depth                    :   33
%              Number of atoms          : 2920 (6956 expanded)
%              Number of equality atoms :   43 (  85 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f781,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f109,f116,f123,f130,f137,f144,f151,f158,f165,f172,f179,f186,f193,f200,f207,f222,f259,f266,f275,f282,f330,f351,f362,f376,f386,f397,f405,f424,f438,f443,f565,f585,f680,f687,f706,f716,f726,f740,f751,f758,f768,f780])).

fof(f780,plain,
    ( ~ spl11_0
    | spl11_3
    | spl11_5
    | spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | spl11_37
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_96 ),
    inference(avatar_contradiction_clause,[],[f779])).

fof(f779,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_37
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_96 ),
    inference(subsumption_resolution,[],[f778,f246])).

fof(f246,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_37 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl11_37
  <=> ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).

fof(f778,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_96 ),
    inference(subsumption_resolution,[],[f777,f143])).

fof(f143,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl11_13
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f777,plain,
    ( v2_struct_0(sK0)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_96 ),
    inference(subsumption_resolution,[],[f776,f150])).

fof(f150,plain,
    ( v2_pre_topc(sK0)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl11_14
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f776,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_96 ),
    inference(subsumption_resolution,[],[f775,f164])).

fof(f164,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl11_18
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f775,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_96 ),
    inference(subsumption_resolution,[],[f774,f157])).

fof(f157,plain,
    ( l1_pre_topc(sK0)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl11_16
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f774,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_96 ),
    inference(subsumption_resolution,[],[f773,f171])).

fof(f171,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl11_20
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f773,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_96 ),
    inference(subsumption_resolution,[],[f772,f108])).

fof(f108,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl11_3
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f772,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_96 ),
    inference(subsumption_resolution,[],[f769,f178])).

fof(f178,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl11_22
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f769,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_96 ),
    inference(resolution,[],[f767,f537])).

fof(f537,plain,
    ( ! [X19,X18] :
        ( ~ m1_subset_1(sK7(sK1,X19,k3_tmap_1(X18,sK1,sK2,X19,sK4)),u1_struct_0(sK2))
        | ~ m1_pre_topc(sK2,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,sK2)
        | ~ v2_pre_topc(X18)
        | v2_struct_0(X18)
        | v5_pre_topc(k3_tmap_1(X18,sK1,sK2,X19,sK4),X19,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f536,f199])).

fof(f199,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl11_28
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f536,plain,
    ( ! [X19,X18] :
        ( ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(sK2,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_subset_1(sK7(sK1,X19,k3_tmap_1(X18,sK1,sK2,X19,sK4)),u1_struct_0(sK2))
        | ~ m1_pre_topc(X19,sK2)
        | ~ v2_pre_topc(X18)
        | v2_struct_0(X18)
        | v5_pre_topc(k3_tmap_1(X18,sK1,sK2,X19,sK4),X19,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f535,f192])).

fof(f192,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl11_26
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f535,plain,
    ( ! [X19,X18] :
        ( ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(sK2,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_subset_1(sK7(sK1,X19,k3_tmap_1(X18,sK1,sK2,X19,sK4)),u1_struct_0(sK2))
        | ~ m1_pre_topc(X19,sK2)
        | ~ v2_pre_topc(X18)
        | v2_struct_0(X18)
        | v5_pre_topc(k3_tmap_1(X18,sK1,sK2,X19,sK4),X19,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f534,f101])).

fof(f101,plain,
    ( v1_funct_1(sK4)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl11_0
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f534,plain,
    ( ! [X19,X18] :
        ( ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(sK2,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_subset_1(sK7(sK1,X19,k3_tmap_1(X18,sK1,sK2,X19,sK4)),u1_struct_0(sK2))
        | ~ m1_pre_topc(X19,sK2)
        | ~ v2_pre_topc(X18)
        | v2_struct_0(X18)
        | v5_pre_topc(k3_tmap_1(X18,sK1,sK2,X19,sK4),X19,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f533,f115])).

fof(f115,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl11_5
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f533,plain,
    ( ! [X19,X18] :
        ( ~ l1_pre_topc(X18)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_subset_1(sK7(sK1,X19,k3_tmap_1(X18,sK1,sK2,X19,sK4)),u1_struct_0(sK2))
        | ~ m1_pre_topc(X19,sK2)
        | ~ v2_pre_topc(X18)
        | v2_struct_0(X18)
        | v5_pre_topc(k3_tmap_1(X18,sK1,sK2,X19,sK4),X19,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f532,f136])).

fof(f136,plain,
    ( l1_pre_topc(sK1)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl11_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f532,plain,
    ( ! [X19,X18] :
        ( ~ l1_pre_topc(X18)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_subset_1(sK7(sK1,X19,k3_tmap_1(X18,sK1,sK2,X19,sK4)),u1_struct_0(sK2))
        | ~ m1_pre_topc(X19,sK2)
        | ~ v2_pre_topc(X18)
        | v2_struct_0(X18)
        | v5_pre_topc(k3_tmap_1(X18,sK1,sK2,X19,sK4),X19,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f531,f129])).

fof(f129,plain,
    ( v2_pre_topc(sK1)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl11_8
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f531,plain,
    ( ! [X19,X18] :
        ( ~ l1_pre_topc(X18)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_subset_1(sK7(sK1,X19,k3_tmap_1(X18,sK1,sK2,X19,sK4)),u1_struct_0(sK2))
        | ~ m1_pre_topc(X19,sK2)
        | ~ v2_pre_topc(X18)
        | v2_struct_0(X18)
        | v5_pre_topc(k3_tmap_1(X18,sK1,sK2,X19,sK4),X19,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f519,f122])).

fof(f122,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl11_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f519,plain,
    ( ! [X19,X18] :
        ( ~ l1_pre_topc(X18)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_subset_1(sK7(sK1,X19,k3_tmap_1(X18,sK1,sK2,X19,sK4)),u1_struct_0(sK2))
        | ~ m1_pre_topc(X19,sK2)
        | ~ v2_pre_topc(X18)
        | v2_struct_0(X18)
        | v5_pre_topc(k3_tmap_1(X18,sK1,sK2,X19,sK4),X19,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(duplicate_literal_removal,[],[f518])).

fof(f518,plain,
    ( ! [X19,X18] :
        ( ~ l1_pre_topc(X18)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_subset_1(sK7(sK1,X19,k3_tmap_1(X18,sK1,sK2,X19,sK4)),u1_struct_0(sK2))
        | ~ m1_pre_topc(X19,sK2)
        | ~ v2_pre_topc(X18)
        | v2_struct_0(X18)
        | v5_pre_topc(k3_tmap_1(X18,sK1,sK2,X19,sK4),X19,sK1)
        | ~ m1_subset_1(sK7(sK1,X19,k3_tmap_1(X18,sK1,sK2,X19,sK4)),u1_struct_0(sK2)) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(resolution,[],[f375,f314])).

fof(f314,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK2,sK1,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f313,f185])).

fof(f185,plain,
    ( v5_pre_topc(sK4,sK2,sK1)
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl11_24
  <=> v5_pre_topc(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK2,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f312,f122])).

fof(f312,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK2,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f311,f192])).

fof(f311,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK2,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f310,f101])).

fof(f310,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK2,sK1) )
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f309,f265])).

fof(f265,plain,
    ( l1_pre_topc(sK2)
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl11_42
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK2,sK1) )
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_28
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f308,f281])).

fof(f281,plain,
    ( v2_pre_topc(sK2)
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl11_46
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f308,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK2,sK1) )
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f307,f115])).

fof(f307,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK2,sK1) )
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f306,f136])).

fof(f306,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK2,sK1) )
    | ~ spl11_8
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f302,f129])).

fof(f302,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,sK4,X0)
        | ~ v5_pre_topc(sK4,sK2,sK1) )
    | ~ spl11_28 ),
    inference(resolution,[],[f81,f199])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_tmap_1(X1,X0,X2,X3)
      | ~ v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',t49_tmap_1)).

fof(f375,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,X4,sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)))
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
      | ~ m1_subset_1(sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)),u1_struct_0(X2))
      | ~ m1_pre_topc(X3,X2)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) ) ),
    inference(subsumption_resolution,[],[f374,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',dt_k3_tmap_1)).

fof(f374,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
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
      | ~ m1_subset_1(sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)),u1_struct_0(X2))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)))
      | v2_struct_0(X0)
      | ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) ) ),
    inference(subsumption_resolution,[],[f373,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f373,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
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
      | ~ m1_subset_1(sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)),u1_struct_0(X2))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)))
      | v2_struct_0(X0)
      | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) ) ),
    inference(subsumption_resolution,[],[f372,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',dt_m1_pre_topc)).

fof(f372,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
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
      | ~ m1_subset_1(sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)),u1_struct_0(X2))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) ) ),
    inference(subsumption_resolution,[],[f371,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',cc1_pre_topc)).

fof(f371,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
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
      | ~ m1_subset_1(sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)),u1_struct_0(X2))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) ) ),
    inference(subsumption_resolution,[],[f370,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | v2_struct_0(X0)
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f370,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
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
      | ~ m1_subset_1(sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)),u1_struct_0(X2))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) ) ),
    inference(subsumption_resolution,[],[f369,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f369,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
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
      | ~ m1_subset_1(sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)),u1_struct_0(X2))
      | ~ m1_subset_1(sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)),u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) ) ),
    inference(duplicate_literal_removal,[],[f368])).

fof(f368,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
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
      | ~ m1_subset_1(sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)),u1_struct_0(X2))
      | ~ m1_subset_1(sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)),u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,sK7(X1,X3,k3_tmap_1(X0,X1,X2,X3,X4)))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1) ) ),
    inference(resolution,[],[f95,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X1,X0,X2,sK7(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
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
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',t81_tmap_1)).

fof(f767,plain,
    ( m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK2))
    | ~ spl11_96 ),
    inference(avatar_component_clause,[],[f766])).

fof(f766,plain,
    ( spl11_96
  <=> m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_96])])).

fof(f768,plain,
    ( spl11_96
    | ~ spl11_86
    | ~ spl11_94 ),
    inference(avatar_split_clause,[],[f761,f749,f721,f766])).

fof(f721,plain,
    ( spl11_86
  <=> m1_subset_1(sK6(sK2,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_86])])).

fof(f749,plain,
    ( spl11_94
  <=> sK6(sK2,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) = sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_94])])).

fof(f761,plain,
    ( m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK2))
    | ~ spl11_86
    | ~ spl11_94 ),
    inference(backward_demodulation,[],[f750,f722])).

fof(f722,plain,
    ( m1_subset_1(sK6(sK2,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),u1_struct_0(sK2))
    | ~ spl11_86 ),
    inference(avatar_component_clause,[],[f721])).

fof(f750,plain,
    ( sK6(sK2,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) = sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | ~ spl11_94 ),
    inference(avatar_component_clause,[],[f749])).

fof(f758,plain,
    ( spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_88 ),
    inference(avatar_contradiction_clause,[],[f757])).

fof(f757,plain,
    ( $false
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_88 ),
    inference(subsumption_resolution,[],[f756,f157])).

fof(f756,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_88 ),
    inference(subsumption_resolution,[],[f755,f178])).

fof(f755,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_20
    | ~ spl11_88 ),
    inference(subsumption_resolution,[],[f754,f150])).

fof(f754,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl11_13
    | ~ spl11_20
    | ~ spl11_88 ),
    inference(subsumption_resolution,[],[f753,f143])).

fof(f753,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl11_20
    | ~ spl11_88 ),
    inference(resolution,[],[f725,f171])).

fof(f725,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl11_88 ),
    inference(avatar_component_clause,[],[f724])).

fof(f724,plain,
    ( spl11_88
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f751,plain,
    ( spl11_94
    | spl11_88
    | spl11_3
    | spl11_5
    | ~ spl11_18
    | ~ spl11_56 ),
    inference(avatar_split_clause,[],[f547,f422,f163,f114,f107,f724,f749])).

fof(f422,plain,
    ( spl11_56
  <=> m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f547,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | sK6(sK2,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) = sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) )
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_18
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f545,f115])).

fof(f545,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | sK6(sK2,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) = sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) )
    | ~ spl11_3
    | ~ spl11_18
    | ~ spl11_56 ),
    inference(resolution,[],[f428,f164])).

fof(f428,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(sK3,X3)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | sK6(X3,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) = sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) )
    | ~ spl11_3
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f426,f108])).

fof(f426,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X2)
        | sK6(X3,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) = sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) )
    | ~ spl11_56 ),
    inference(resolution,[],[f423,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X0)
      | sK6(X2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X2)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X2)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
             => ( m1_pre_topc(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ? [X4] :
                        ( X3 = X4
                        & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',t15_tmap_1)).

fof(f423,plain,
    ( m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK3))
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f422])).

fof(f740,plain,
    ( spl11_90
    | spl11_92
    | spl11_3
    | spl11_13
    | ~ spl11_20
    | ~ spl11_56 ),
    inference(avatar_split_clause,[],[f448,f422,f170,f142,f107,f738,f735])).

fof(f735,plain,
    ( spl11_90
  <=> m1_subset_1(sK6(sK0,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).

fof(f738,plain,
    ( spl11_92
  <=> ! [X1] :
        ( ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ m1_pre_topc(sK3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_92])])).

fof(f448,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | m1_subset_1(sK6(sK0,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),u1_struct_0(sK0)) )
    | ~ spl11_3
    | ~ spl11_13
    | ~ spl11_20
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f446,f143])).

fof(f446,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | m1_subset_1(sK6(sK0,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),u1_struct_0(sK0)) )
    | ~ spl11_3
    | ~ spl11_20
    | ~ spl11_56 ),
    inference(resolution,[],[f427,f171])).

fof(f427,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | m1_subset_1(sK6(X1,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),u1_struct_0(X1)) )
    | ~ spl11_3
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f425,f108])).

fof(f425,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X0)
        | m1_subset_1(sK6(X1,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),u1_struct_0(X1)) )
    | ~ spl11_56 ),
    inference(resolution,[],[f423,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X0)
      | m1_subset_1(sK6(X2,X3),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f726,plain,
    ( spl11_86
    | spl11_88
    | spl11_3
    | spl11_5
    | ~ spl11_18
    | ~ spl11_56 ),
    inference(avatar_split_clause,[],[f447,f422,f163,f114,f107,f724,f721])).

fof(f447,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | m1_subset_1(sK6(sK2,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),u1_struct_0(sK2)) )
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_18
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f445,f115])).

fof(f445,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | m1_subset_1(sK6(sK2,sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))),u1_struct_0(sK2)) )
    | ~ spl11_3
    | ~ spl11_18
    | ~ spl11_56 ),
    inference(resolution,[],[f427,f164])).

fof(f716,plain,
    ( ~ spl11_83
    | spl11_84
    | ~ spl11_0
    | spl11_5
    | spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f557,f280,f264,f198,f191,f184,f135,f128,f121,f114,f100,f714,f711])).

fof(f711,plain,
    ( spl11_83
  <=> ~ m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_83])])).

fof(f714,plain,
    ( spl11_84
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK2,sK4),sK2,sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_84])])).

fof(f557,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK2)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK2,sK4),sK2,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f556,f199])).

fof(f556,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK2)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK2,sK4),sK2,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f555,f192])).

fof(f555,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK2)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK2,sK4),sK2,sK1)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f554,f101])).

fof(f554,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK2)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK2,sK4),sK2,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f553,f136])).

fof(f553,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK2)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK2,sK4),sK2,sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f552,f129])).

fof(f552,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK2)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK2,sK4),sK2,sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f551,f122])).

fof(f551,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK2)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK2,sK4),sK2,sK1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f550,f115])).

fof(f550,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK2)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK2,sK4),sK2,sK1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(duplicate_literal_removal,[],[f549])).

fof(f549,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK2)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK2,sK4),sK2,sK1)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(k3_tmap_1(X0,sK1,sK2,sK2,sK4),sK2,sK1) )
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_24
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(resolution,[],[f537,f361])).

fof(f361,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( m1_subset_1(sK7(X14,X16,k3_tmap_1(X13,X14,X15,X16,X17)),u1_struct_0(X16))
      | ~ l1_pre_topc(X13)
      | v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X13)
      | ~ m1_pre_topc(X16,X13)
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
      | v2_struct_0(X13)
      | v2_struct_0(X16)
      | ~ v2_pre_topc(X13)
      | v5_pre_topc(k3_tmap_1(X13,X14,X15,X16,X17),X16,X14) ) ),
    inference(subsumption_resolution,[],[f360,f71])).

fof(f360,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X13)
      | ~ m1_pre_topc(X16,X13)
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
      | v2_struct_0(X13)
      | v2_struct_0(X16)
      | ~ v1_funct_2(k3_tmap_1(X13,X14,X15,X16,X17),u1_struct_0(X16),u1_struct_0(X14))
      | m1_subset_1(sK7(X14,X16,k3_tmap_1(X13,X14,X15,X16,X17)),u1_struct_0(X16))
      | v5_pre_topc(k3_tmap_1(X13,X14,X15,X16,X17),X16,X14) ) ),
    inference(subsumption_resolution,[],[f359,f93])).

fof(f359,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X13)
      | ~ m1_pre_topc(X16,X13)
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
      | v2_struct_0(X13)
      | v2_struct_0(X16)
      | ~ l1_pre_topc(X16)
      | ~ v1_funct_2(k3_tmap_1(X13,X14,X15,X16,X17),u1_struct_0(X16),u1_struct_0(X14))
      | m1_subset_1(sK7(X14,X16,k3_tmap_1(X13,X14,X15,X16,X17)),u1_struct_0(X16))
      | v5_pre_topc(k3_tmap_1(X13,X14,X15,X16,X17),X16,X14) ) ),
    inference(subsumption_resolution,[],[f358,f91])).

fof(f358,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X13)
      | ~ m1_pre_topc(X16,X13)
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
      | v2_struct_0(X13)
      | v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ v1_funct_2(k3_tmap_1(X13,X14,X15,X16,X17),u1_struct_0(X16),u1_struct_0(X14))
      | m1_subset_1(sK7(X14,X16,k3_tmap_1(X13,X14,X15,X16,X17)),u1_struct_0(X16))
      | v5_pre_topc(k3_tmap_1(X13,X14,X15,X16,X17),X16,X14) ) ),
    inference(subsumption_resolution,[],[f337,f70])).

fof(f337,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X13)
      | ~ m1_pre_topc(X16,X13)
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
      | v2_struct_0(X13)
      | v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ v1_funct_1(k3_tmap_1(X13,X14,X15,X16,X17))
      | ~ v1_funct_2(k3_tmap_1(X13,X14,X15,X16,X17),u1_struct_0(X16),u1_struct_0(X14))
      | m1_subset_1(sK7(X14,X16,k3_tmap_1(X13,X14,X15,X16,X17)),u1_struct_0(X16))
      | v5_pre_topc(k3_tmap_1(X13,X14,X15,X16,X17),X16,X14) ) ),
    inference(duplicate_literal_removal,[],[f334])).

fof(f334,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X13)
      | ~ m1_pre_topc(X16,X13)
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ v1_funct_1(k3_tmap_1(X13,X14,X15,X16,X17))
      | ~ v1_funct_2(k3_tmap_1(X13,X14,X15,X16,X17),u1_struct_0(X16),u1_struct_0(X14))
      | v2_struct_0(X14)
      | m1_subset_1(sK7(X14,X16,k3_tmap_1(X13,X14,X15,X16,X17)),u1_struct_0(X16))
      | v5_pre_topc(k3_tmap_1(X13,X14,X15,X16,X17),X16,X14) ) ),
    inference(resolution,[],[f72,f82])).

fof(f706,plain,
    ( spl11_76
    | spl11_78
    | ~ spl11_81
    | spl11_5
    | spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_22
    | ~ spl11_42 ),
    inference(avatar_split_clause,[],[f544,f264,f177,f156,f149,f142,f114,f704,f698,f692])).

fof(f692,plain,
    ( spl11_76
  <=> sK5(u1_struct_0(sK9(sK2))) = sK6(sK2,sK5(u1_struct_0(sK9(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_76])])).

fof(f698,plain,
    ( spl11_78
  <=> v2_struct_0(sK9(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_78])])).

fof(f704,plain,
    ( spl11_81
  <=> ~ m1_pre_topc(sK9(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_81])])).

fof(f544,plain,
    ( ~ m1_pre_topc(sK9(sK2),sK0)
    | v2_struct_0(sK9(sK2))
    | sK5(u1_struct_0(sK9(sK2))) = sK6(sK2,sK5(u1_struct_0(sK9(sK2))))
    | ~ spl11_5
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_22
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f541,f265])).

fof(f541,plain,
    ( ~ m1_pre_topc(sK9(sK2),sK0)
    | v2_struct_0(sK9(sK2))
    | sK5(u1_struct_0(sK9(sK2))) = sK6(sK2,sK5(u1_struct_0(sK9(sK2))))
    | ~ l1_pre_topc(sK2)
    | ~ spl11_5
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(resolution,[],[f488,f92])).

fof(f92,plain,(
    ! [X0] :
      ( m1_pre_topc(sK9(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',existence_m1_pre_topc)).

fof(f488,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | sK5(u1_struct_0(X2)) = sK6(sK2,sK5(u1_struct_0(X2))) )
    | ~ spl11_5
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f487,f143])).

fof(f487,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0)
        | sK5(u1_struct_0(X2)) = sK6(sK2,sK5(u1_struct_0(X2))) )
    | ~ spl11_5
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f486,f150])).

fof(f486,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0)
        | sK5(u1_struct_0(X2)) = sK6(sK2,sK5(u1_struct_0(X2))) )
    | ~ spl11_5
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f485,f115])).

fof(f485,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0)
        | sK5(u1_struct_0(X2)) = sK6(sK2,sK5(u1_struct_0(X2))) )
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f474,f157])).

fof(f474,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0)
        | sK5(u1_struct_0(X2)) = sK6(sK2,sK5(u1_struct_0(X2))) )
    | ~ spl11_22 ),
    inference(resolution,[],[f285,f178])).

fof(f285,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X0)
      | sK5(u1_struct_0(X1)) = sK6(X2,sK5(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f80,f78])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',existence_m1_subset_1)).

fof(f687,plain,
    ( spl11_68
    | spl11_70
    | ~ spl11_75
    | spl11_3
    | spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_32 ),
    inference(avatar_split_clause,[],[f539,f220,f170,f156,f149,f142,f107,f685,f672,f666])).

fof(f666,plain,
    ( spl11_68
  <=> sK5(u1_struct_0(sK9(sK3))) = sK6(sK3,sK5(u1_struct_0(sK9(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f672,plain,
    ( spl11_70
  <=> v2_struct_0(sK9(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f685,plain,
    ( spl11_75
  <=> ~ m1_pre_topc(sK9(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_75])])).

fof(f220,plain,
    ( spl11_32
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f539,plain,
    ( ~ m1_pre_topc(sK9(sK3),sK0)
    | v2_struct_0(sK9(sK3))
    | sK5(u1_struct_0(sK9(sK3))) = sK6(sK3,sK5(u1_struct_0(sK9(sK3))))
    | ~ spl11_3
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f538,f221])).

fof(f221,plain,
    ( l1_pre_topc(sK3)
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f220])).

fof(f538,plain,
    ( ~ m1_pre_topc(sK9(sK3),sK0)
    | v2_struct_0(sK9(sK3))
    | sK5(u1_struct_0(sK9(sK3))) = sK6(sK3,sK5(u1_struct_0(sK9(sK3))))
    | ~ l1_pre_topc(sK3)
    | ~ spl11_3
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(resolution,[],[f484,f92])).

fof(f484,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | sK5(u1_struct_0(X1)) = sK6(sK3,sK5(u1_struct_0(X1))) )
    | ~ spl11_3
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f483,f143])).

fof(f483,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK0)
        | sK5(u1_struct_0(X1)) = sK6(sK3,sK5(u1_struct_0(X1))) )
    | ~ spl11_3
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f482,f150])).

fof(f482,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK0)
        | sK5(u1_struct_0(X1)) = sK6(sK3,sK5(u1_struct_0(X1))) )
    | ~ spl11_3
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f481,f108])).

fof(f481,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK0)
        | sK5(u1_struct_0(X1)) = sK6(sK3,sK5(u1_struct_0(X1))) )
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f473,f157])).

fof(f473,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK0)
        | sK5(u1_struct_0(X1)) = sK6(sK3,sK5(u1_struct_0(X1))) )
    | ~ spl11_20 ),
    inference(resolution,[],[f285,f171])).

fof(f680,plain,
    ( spl11_68
    | spl11_70
    | ~ spl11_73
    | spl11_3
    | spl11_5
    | ~ spl11_18
    | ~ spl11_32
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f512,f280,f264,f220,f163,f114,f107,f678,f672,f666])).

fof(f678,plain,
    ( spl11_73
  <=> ~ m1_pre_topc(sK9(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_73])])).

fof(f512,plain,
    ( ~ m1_pre_topc(sK9(sK3),sK2)
    | v2_struct_0(sK9(sK3))
    | sK5(u1_struct_0(sK9(sK3))) = sK6(sK3,sK5(u1_struct_0(sK9(sK3))))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_18
    | ~ spl11_32
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f511,f221])).

fof(f511,plain,
    ( ~ m1_pre_topc(sK9(sK3),sK2)
    | v2_struct_0(sK9(sK3))
    | sK5(u1_struct_0(sK9(sK3))) = sK6(sK3,sK5(u1_struct_0(sK9(sK3))))
    | ~ l1_pre_topc(sK3)
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_18
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(resolution,[],[f480,f92])).

fof(f480,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | sK5(u1_struct_0(X0)) = sK6(sK3,sK5(u1_struct_0(X0))) )
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_18
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f479,f115])).

fof(f479,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK2)
        | sK5(u1_struct_0(X0)) = sK6(sK3,sK5(u1_struct_0(X0))) )
    | ~ spl11_3
    | ~ spl11_18
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f478,f281])).

fof(f478,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | ~ v2_pre_topc(sK2)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK2)
        | sK5(u1_struct_0(X0)) = sK6(sK3,sK5(u1_struct_0(X0))) )
    | ~ spl11_3
    | ~ spl11_18
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f477,f108])).

fof(f477,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK2)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK2)
        | sK5(u1_struct_0(X0)) = sK6(sK3,sK5(u1_struct_0(X0))) )
    | ~ spl11_18
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f472,f265])).

fof(f472,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK2)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK2)
        | sK5(u1_struct_0(X0)) = sK6(sK3,sK5(u1_struct_0(X0))) )
    | ~ spl11_18 ),
    inference(resolution,[],[f285,f164])).

fof(f585,plain,
    ( spl11_66
    | spl11_3
    | spl11_5
    | spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_64 ),
    inference(avatar_split_clause,[],[f576,f563,f177,f170,f163,f156,f149,f142,f114,f107,f583])).

fof(f583,plain,
    ( spl11_66
  <=> m1_subset_1(sK5(u1_struct_0(sK3)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f563,plain,
    ( spl11_64
  <=> sK5(u1_struct_0(sK3)) = sK6(sK2,sK5(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).

fof(f576,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK3)),u1_struct_0(sK2))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_64 ),
    inference(subsumption_resolution,[],[f575,f108])).

fof(f575,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK3)),u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | ~ spl11_5
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_64 ),
    inference(subsumption_resolution,[],[f574,f164])).

fof(f574,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ spl11_5
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_64 ),
    inference(subsumption_resolution,[],[f573,f171])).

fof(f573,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK3)),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ spl11_5
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_22
    | ~ spl11_64 ),
    inference(superposition,[],[f467,f564])).

fof(f564,plain,
    ( sK5(u1_struct_0(sK3)) = sK6(sK2,sK5(u1_struct_0(sK3)))
    | ~ spl11_64 ),
    inference(avatar_component_clause,[],[f563])).

fof(f467,plain,
    ( ! [X2] :
        ( m1_subset_1(sK6(sK2,sK5(u1_struct_0(X2))),u1_struct_0(sK2))
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X2) )
    | ~ spl11_5
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f466,f143])).

fof(f466,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0)
        | m1_subset_1(sK6(sK2,sK5(u1_struct_0(X2))),u1_struct_0(sK2)) )
    | ~ spl11_5
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f465,f150])).

fof(f465,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0)
        | m1_subset_1(sK6(sK2,sK5(u1_struct_0(X2))),u1_struct_0(sK2)) )
    | ~ spl11_5
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f464,f115])).

fof(f464,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0)
        | m1_subset_1(sK6(sK2,sK5(u1_struct_0(X2))),u1_struct_0(sK2)) )
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f453,f157])).

fof(f453,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(sK0)
        | m1_subset_1(sK6(sK2,sK5(u1_struct_0(X2))),u1_struct_0(sK2)) )
    | ~ spl11_22 ),
    inference(resolution,[],[f286,f178])).

fof(f286,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X0)
      | m1_subset_1(sK6(X2,sK5(u1_struct_0(X1))),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f79,f78])).

fof(f565,plain,
    ( spl11_64
    | spl11_3
    | spl11_5
    | spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f543,f177,f170,f163,f156,f149,f142,f114,f107,f563])).

fof(f543,plain,
    ( sK5(u1_struct_0(sK3)) = sK6(sK2,sK5(u1_struct_0(sK3)))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f542,f108])).

fof(f542,plain,
    ( v2_struct_0(sK3)
    | sK5(u1_struct_0(sK3)) = sK6(sK2,sK5(u1_struct_0(sK3)))
    | ~ spl11_5
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f540,f171])).

fof(f540,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | sK5(u1_struct_0(sK3)) = sK6(sK2,sK5(u1_struct_0(sK3)))
    | ~ spl11_5
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_22 ),
    inference(resolution,[],[f488,f164])).

fof(f443,plain,
    ( ~ spl11_41
    | spl11_62
    | spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_34
    | ~ spl11_38 ),
    inference(avatar_split_clause,[],[f417,f248,f236,f135,f128,f121,f441,f257])).

fof(f257,plain,
    ( spl11_41
  <=> ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).

fof(f441,plain,
    ( spl11_62
  <=> ! [X1,X2] :
        ( ~ v2_pre_topc(X1)
        | v1_funct_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_62])])).

fof(f236,plain,
    ( spl11_34
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f248,plain,
    ( spl11_38
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f417,plain,
    ( ! [X2,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X2,X1)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
        | v2_struct_0(X1)
        | v1_funct_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) )
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_34
    | ~ spl11_38 ),
    inference(subsumption_resolution,[],[f416,f249])).

fof(f249,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f248])).

fof(f416,plain,
    ( ! [X2,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X2,X1)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(X1)
        | v1_funct_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) )
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f415,f136])).

fof(f415,plain,
    ( ! [X2,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X2,X1)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(X1)
        | v1_funct_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) )
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f414,f129])).

fof(f414,plain,
    ( ! [X2,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X2,X1)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(X1)
        | v1_funct_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) )
    | ~ spl11_7
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f364,f122])).

fof(f364,plain,
    ( ! [X2,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X2,X1)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(X1)
        | v1_funct_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))) )
    | ~ spl11_34 ),
    inference(resolution,[],[f237,f70])).

fof(f237,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f236])).

fof(f438,plain,
    ( spl11_58
    | spl11_60
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f398,f236,f436,f433])).

fof(f433,plain,
    ( spl11_58
  <=> v1_xboole_0(k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f436,plain,
    ( spl11_60
  <=> ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f398,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
        | v1_xboole_0(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
        | ~ m1_subset_1(X0,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) )
    | ~ spl11_34 ),
    inference(resolution,[],[f366,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',t2_subset)).

fof(f366,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
        | m1_subset_1(X3,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) )
    | ~ spl11_34 ),
    inference(resolution,[],[f237,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',t4_subset)).

fof(f424,plain,
    ( spl11_56
    | ~ spl11_41
    | spl11_3
    | spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_32
    | ~ spl11_34
    | spl11_37
    | ~ spl11_38
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f413,f273,f248,f245,f236,f220,f135,f128,f121,f107,f257,f422])).

fof(f273,plain,
    ( spl11_44
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f413,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK3))
    | ~ spl11_3
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_37
    | ~ spl11_38
    | ~ spl11_44 ),
    inference(subsumption_resolution,[],[f412,f246])).

fof(f412,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK3))
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_3
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_44 ),
    inference(subsumption_resolution,[],[f411,f122])).

fof(f411,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | v2_struct_0(sK1)
    | m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK3))
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_3
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_44 ),
    inference(subsumption_resolution,[],[f410,f249])).

fof(f410,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK3))
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_3
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_44 ),
    inference(subsumption_resolution,[],[f409,f221])).

fof(f409,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK3))
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_3
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_34
    | ~ spl11_44 ),
    inference(subsumption_resolution,[],[f408,f274])).

fof(f274,plain,
    ( v2_pre_topc(sK3)
    | ~ spl11_44 ),
    inference(avatar_component_clause,[],[f273])).

fof(f408,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK3))
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_3
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f407,f108])).

fof(f407,plain,
    ( v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK3))
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f406,f136])).

fof(f406,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK3))
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_8
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f365,f129])).

fof(f365,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_subset_1(sK7(sK1,sK3,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)),u1_struct_0(sK3))
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ spl11_34 ),
    inference(resolution,[],[f237,f82])).

fof(f405,plain,
    ( ~ spl11_0
    | spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | spl11_41 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_41 ),
    inference(subsumption_resolution,[],[f403,f150])).

fof(f403,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_41 ),
    inference(subsumption_resolution,[],[f402,f143])).

fof(f402,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_41 ),
    inference(subsumption_resolution,[],[f401,f171])).

fof(f401,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_16
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_41 ),
    inference(subsumption_resolution,[],[f400,f178])).

fof(f400,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_16
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_41 ),
    inference(subsumption_resolution,[],[f399,f157])).

fof(f399,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_41 ),
    inference(resolution,[],[f299,f258])).

fof(f258,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | ~ spl11_41 ),
    inference(avatar_component_clause,[],[f257])).

fof(f299,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK4))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_26
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f298,f192])).

fof(f298,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK4)) )
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f297,f101])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK4)) )
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f296,f136])).

fof(f296,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK4)) )
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f295,f129])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK4)) )
    | ~ spl11_7
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f291,f122])).

fof(f291,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK4)) )
    | ~ spl11_28 ),
    inference(resolution,[],[f70,f199])).

fof(f397,plain,
    ( ~ spl11_53
    | spl11_54
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f367,f236,f395,f392])).

fof(f392,plain,
    ( spl11_53
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f395,plain,
    ( spl11_54
  <=> ! [X4] : ~ r2_hidden(X4,k3_tmap_1(sK0,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f367,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) )
    | ~ spl11_34 ),
    inference(resolution,[],[f237,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',t5_subset)).

fof(f386,plain,
    ( ~ spl11_49
    | spl11_50
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f223,f198,f384,f381])).

fof(f381,plain,
    ( spl11_49
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f384,plain,
    ( spl11_50
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) )
    | ~ spl11_28 ),
    inference(resolution,[],[f74,f199])).

fof(f376,plain,
    ( spl11_44
    | ~ spl11_47
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f230,f177,f163,f156,f277,f273])).

fof(f277,plain,
    ( spl11_47
  <=> ~ v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).

fof(f230,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK3)
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f225,f214])).

fof(f214,plain,
    ( l1_pre_topc(sK2)
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f210,f157])).

fof(f210,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl11_22 ),
    inference(resolution,[],[f93,f178])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK3)
    | ~ spl11_18 ),
    inference(resolution,[],[f91,f164])).

fof(f362,plain,
    ( spl11_32
    | ~ spl11_43
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f208,f163,f261,f220])).

fof(f261,plain,
    ( spl11_43
  <=> ~ l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).

fof(f208,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK3)
    | ~ spl11_18 ),
    inference(resolution,[],[f93,f164])).

fof(f351,plain,
    ( ~ spl11_0
    | spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | spl11_35 ),
    inference(avatar_contradiction_clause,[],[f350])).

fof(f350,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f349,f143])).

fof(f349,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f348,f199])).

fof(f348,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f347,f192])).

fof(f347,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f346,f101])).

fof(f346,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f345,f171])).

fof(f345,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_22
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f344,f178])).

fof(f344,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f343,f136])).

fof(f343,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f342,f129])).

fof(f342,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f341,f122])).

fof(f341,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f340,f157])).

fof(f340,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_14
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f331,f150])).

fof(f331,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_35 ),
    inference(resolution,[],[f72,f240])).

fof(f240,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl11_35 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl11_35
  <=> ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f330,plain,
    ( ~ spl11_0
    | spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | spl11_39 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f328,f143])).

fof(f328,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f327,f199])).

fof(f327,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f326,f192])).

fof(f326,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f325,f101])).

fof(f325,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f324,f171])).

fof(f324,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_22
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f323,f178])).

fof(f323,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f322,f136])).

fof(f322,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f321,f129])).

fof(f321,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_7
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f320,f122])).

fof(f320,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f319,f157])).

fof(f319,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_14
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f318,f150])).

fof(f318,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_39 ),
    inference(resolution,[],[f71,f252])).

fof(f252,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl11_39 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl11_39
  <=> ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).

fof(f282,plain,
    ( spl11_46
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f234,f177,f156,f149,f280])).

fof(f234,plain,
    ( v2_pre_topc(sK2)
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f233,f150])).

fof(f233,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f227,f157])).

fof(f227,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ spl11_22 ),
    inference(resolution,[],[f91,f178])).

fof(f275,plain,
    ( spl11_44
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f232,f170,f156,f149,f273])).

fof(f232,plain,
    ( v2_pre_topc(sK3)
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f231,f150])).

fof(f231,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f226,f157])).

fof(f226,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl11_20 ),
    inference(resolution,[],[f91,f171])).

fof(f266,plain,
    ( spl11_42
    | ~ spl11_16
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f214,f177,f156,f264])).

fof(f259,plain,
    ( ~ spl11_35
    | ~ spl11_37
    | ~ spl11_39
    | ~ spl11_41 ),
    inference(avatar_split_clause,[],[f54,f257,f251,f245,f239])).

fof(f54,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X3,X2)
                         => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',t89_tmap_1)).

fof(f222,plain,
    ( spl11_32
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f213,f170,f156,f220])).

fof(f213,plain,
    ( l1_pre_topc(sK3)
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f209,f157])).

fof(f209,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3)
    | ~ spl11_20 ),
    inference(resolution,[],[f93,f171])).

fof(f207,plain,(
    spl11_30 ),
    inference(avatar_split_clause,[],[f94,f205])).

fof(f205,plain,
    ( spl11_30
  <=> l1_pre_topc(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f94,plain,(
    l1_pre_topc(sK10) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t89_tmap_1.p',existence_l1_pre_topc)).

fof(f200,plain,(
    spl11_28 ),
    inference(avatar_split_clause,[],[f58,f198])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f193,plain,(
    spl11_26 ),
    inference(avatar_split_clause,[],[f56,f191])).

fof(f56,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f186,plain,(
    spl11_24 ),
    inference(avatar_split_clause,[],[f57,f184])).

fof(f57,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f179,plain,(
    spl11_22 ),
    inference(avatar_split_clause,[],[f63,f177])).

fof(f63,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f172,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f61,f170])).

fof(f61,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f165,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f59,f163])).

fof(f59,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f158,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f69,f156])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f151,plain,(
    spl11_14 ),
    inference(avatar_split_clause,[],[f68,f149])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f144,plain,(
    ~ spl11_13 ),
    inference(avatar_split_clause,[],[f67,f142])).

fof(f67,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f137,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f66,f135])).

fof(f66,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f130,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f65,f128])).

fof(f65,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f123,plain,(
    ~ spl11_7 ),
    inference(avatar_split_clause,[],[f64,f121])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f116,plain,(
    ~ spl11_5 ),
    inference(avatar_split_clause,[],[f62,f114])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f109,plain,(
    ~ spl11_3 ),
    inference(avatar_split_clause,[],[f60,f107])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f55,f100])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t90_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:21 EDT 2019

% Result     : Theorem 0.35s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  535 (1838 expanded)
%              Number of leaves         :   90 ( 687 expanded)
%              Depth                    :   86
%              Number of atoms          : 6054 (15587 expanded)
%              Number of equality atoms :  146 ( 287 expanded)
%              Maximal formula depth    :   29 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f119,f126,f133,f140,f147,f154,f161,f168,f175,f182,f189,f196,f203,f210,f217,f224,f231,f238,f245,f252,f277,f284,f299,f307,f315,f316,f317,f333,f342,f351,f353,f355,f371,f384,f393,f402,f420,f433,f455,f470,f479,f492,f501,f514,f556,f577,f610,f619,f632,f645,f654,f734,f937,f954,f1016,f1031,f1063,f1082,f1095,f1155])).

fof(f1155,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_12
    | spl11_15
    | ~ spl11_20
    | ~ spl11_24
    | spl11_27
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_34
    | spl11_45
    | ~ spl11_134 ),
    inference(avatar_contradiction_clause,[],[f1154])).

fof(f1154,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_20
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1153,f125])).

fof(f125,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl11_5
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f1153,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_20
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1152,f181])).

fof(f181,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl11_20
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f1152,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1151,f209])).

fof(f209,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl11_28
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f1151,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1150,f216])).

fof(f216,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl11_30
  <=> v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f1150,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1149,f223])).

fof(f223,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl11_32
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f1149,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_34
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1148,f230])).

fof(f230,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl11_34
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f1148,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1147,f195])).

fof(f195,plain,
    ( m1_pre_topc(sK4,sK0)
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl11_24
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f1147,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_27
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1146,f202])).

fof(f202,plain,
    ( ~ v2_struct_0(sK4)
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl11_27
  <=> ~ v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f1146,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1145,f153])).

fof(f153,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl11_12
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f1145,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_15
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1144,f160])).

fof(f160,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl11_15
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f1144,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1143,f132])).

fof(f132,plain,
    ( l1_pre_topc(sK1)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl11_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f1143,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1142,f139])).

fof(f139,plain,
    ( v2_pre_topc(sK1)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl11_8
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f1142,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_11
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1141,f146])).

fof(f146,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl11_11
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f1141,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1140,f111])).

fof(f111,plain,
    ( l1_pre_topc(sK0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl11_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f1140,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_2
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1139,f118])).

fof(f118,plain,
    ( v2_pre_topc(sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl11_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f1139,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_45
    | ~ spl11_134 ),
    inference(subsumption_resolution,[],[f1108,f264])).

fof(f264,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ spl11_45 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl11_45
  <=> ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f1108,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_134 ),
    inference(superposition,[],[f81,f1056])).

fof(f1056,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ spl11_134 ),
    inference(avatar_component_clause,[],[f1055])).

fof(f1055,plain,
    ( spl11_134
  <=> k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_134])])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
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
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
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
                      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',t89_tmap_1)).

fof(f1095,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | spl11_137 ),
    inference(avatar_contradiction_clause,[],[f1094])).

fof(f1094,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1093,f195])).

fof(f1093,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1092,f118])).

fof(f1092,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1091,f125])).

fof(f1091,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1090,f237])).

fof(f237,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl11_36 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl11_36
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f1090,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1089,f244])).

fof(f244,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl11_38
  <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f1089,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_40
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1088,f251])).

fof(f251,plain,
    ( v1_funct_1(sK5)
    | ~ spl11_40 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl11_40
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f1088,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1087,f153])).

fof(f1087,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1086,f167])).

fof(f167,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl11_16
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f1086,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1085,f132])).

fof(f1085,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl11_0
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1084,f139])).

fof(f1084,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl11_0
    | ~ spl11_11
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1083,f146])).

fof(f1083,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl11_0
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1076,f111])).

fof(f1076,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl11_137 ),
    inference(duplicate_literal_removal,[],[f1075])).

fof(f1075,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_137 ),
    inference(resolution,[],[f1062,f579])).

fof(f579,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X5,X1,X3,X6,k3_tmap_1(X0,X1,X2,X3,X4)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X3,X5)
      | ~ m1_pre_topc(X6,X5)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f578,f84])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',dt_k3_tmap_1)).

fof(f578,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X3,X5)
      | ~ m1_pre_topc(X6,X5)
      | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | v2_struct_0(X5)
      | v1_funct_1(k3_tmap_1(X5,X1,X3,X6,k3_tmap_1(X0,X1,X2,X3,X4))) ) ),
    inference(subsumption_resolution,[],[f565,f83])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f565,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X3,X5)
      | ~ m1_pre_topc(X6,X5)
      | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | v2_struct_0(X5)
      | v1_funct_1(k3_tmap_1(X5,X1,X3,X6,k3_tmap_1(X0,X1,X2,X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f558])).

fof(f558,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X3,X5)
      | ~ m1_pre_topc(X6,X5)
      | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | v2_struct_0(X5)
      | v1_funct_1(k3_tmap_1(X5,X1,X3,X6,k3_tmap_1(X0,X1,X2,X3,X4))) ) ),
    inference(resolution,[],[f85,f83])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f1062,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | ~ spl11_137 ),
    inference(avatar_component_clause,[],[f1061])).

fof(f1061,plain,
    ( spl11_137
  <=> ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_137])])).

fof(f1082,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_12
    | ~ spl11_24
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | spl11_137 ),
    inference(avatar_contradiction_clause,[],[f1081])).

fof(f1081,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_24
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1080,f118])).

fof(f1080,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_24
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1079,f125])).

fof(f1079,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_24
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1078,f195])).

fof(f1078,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1077,f153])).

fof(f1077,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_137 ),
    inference(subsumption_resolution,[],[f1074,f111])).

fof(f1074,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_137 ),
    inference(resolution,[],[f1062,f446])).

fof(f446,plain,
    ( ! [X6,X7] :
        ( v1_funct_1(k3_tmap_1(X6,sK1,sK2,X7,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK2,X6)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6) )
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f445,f223])).

fof(f445,plain,
    ( ! [X6,X7] :
        ( ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK2,X6)
        | ~ m1_pre_topc(X7,X6)
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(X6)
        | v1_funct_1(k3_tmap_1(X6,sK1,sK2,X7,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) )
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_28
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f444,f230])).

fof(f444,plain,
    ( ! [X6,X7] :
        ( ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ m1_pre_topc(sK2,X6)
        | ~ m1_pre_topc(X7,X6)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(X6)
        | v1_funct_1(k3_tmap_1(X6,sK1,sK2,X7,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) )
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f443,f132])).

fof(f443,plain,
    ( ! [X6,X7] :
        ( ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,X6)
        | ~ m1_pre_topc(X7,X6)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(X6)
        | v1_funct_1(k3_tmap_1(X6,sK1,sK2,X7,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) )
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f442,f139])).

fof(f442,plain,
    ( ! [X6,X7] :
        ( ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,X6)
        | ~ m1_pre_topc(X7,X6)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(X6)
        | v1_funct_1(k3_tmap_1(X6,sK1,sK2,X7,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) )
    | ~ spl11_11
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f436,f146])).

fof(f436,plain,
    ( ! [X6,X7] :
        ( ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,X6)
        | ~ m1_pre_topc(X7,X6)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(X6)
        | v1_funct_1(k3_tmap_1(X6,sK1,sK2,X7,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) )
    | ~ spl11_28 ),
    inference(resolution,[],[f83,f209])).

fof(f1063,plain,
    ( spl11_134
    | ~ spl11_137
    | ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_12
    | spl11_15
    | ~ spl11_16
    | spl11_19
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_24
    | spl11_27
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f1050,f272,f266,f254,f250,f243,f236,f229,f222,f208,f201,f194,f187,f180,f173,f166,f159,f152,f145,f138,f131,f124,f117,f110,f1061,f1055])).

fof(f173,plain,
    ( spl11_19
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f187,plain,
    ( spl11_22
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f254,plain,
    ( spl11_42
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f266,plain,
    ( spl11_46
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f272,plain,
    ( spl11_48
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f1050,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1049,f188])).

fof(f188,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f187])).

fof(f1049,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_20
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1048,f223])).

fof(f1048,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_20
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1047,f230])).

fof(f1047,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_20
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1046,f153])).

fof(f1046,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_20
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1045,f160])).

fof(f1045,plain,
    ( v2_struct_0(sK2)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_20
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1041,f181])).

fof(f1041,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(resolution,[],[f1040,f209])).

fof(f1040,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1039,f125])).

fof(f1039,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1038,f195])).

fof(f1038,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1037,f132])).

fof(f1037,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1036,f139])).

fof(f1036,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1035,f146])).

fof(f1035,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1034,f111])).

fof(f1034,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1033,f118])).

fof(f1033,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(duplicate_literal_removal,[],[f1032])).

fof(f1032,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(resolution,[],[f900,f84])).

fof(f900,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f899,f125])).

fof(f899,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f898,f195])).

fof(f898,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f897,f132])).

fof(f897,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f896,f139])).

fof(f896,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f895,f146])).

fof(f895,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f894,f111])).

fof(f894,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f893,f118])).

fof(f893,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(duplicate_literal_removal,[],[f892])).

fof(f892,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK4,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(resolution,[],[f882,f85])).

fof(f882,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | v2_struct_0(X3)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f881,f125])).

fof(f881,plain,
    ( ! [X3] :
        ( v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f880,f237])).

fof(f880,plain,
    ( ! [X3] :
        ( v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f879,f244])).

fof(f879,plain,
    ( ! [X3] :
        ( v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f878,f251])).

fof(f878,plain,
    ( ! [X3] :
        ( v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f877,f195])).

fof(f877,plain,
    ( ! [X3] :
        ( v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_27
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f876,f202])).

fof(f876,plain,
    ( ! [X3] :
        ( v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f875,f167])).

fof(f875,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_19
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f874,f174])).

fof(f174,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f173])).

fof(f874,plain,
    ( ! [X3] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f873,f132])).

fof(f873,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f872,f139])).

fof(f872,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_11
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f871,f146])).

fof(f871,plain,
    ( ! [X3] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f870,f111])).

fof(f870,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_2
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f830,f118])).

fof(f830,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK4,X3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X3,sK4,k3_tmap_1(sK0,sK1,sK3,X3,sK5)),u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(resolution,[],[f86,f601])).

fof(f601,plain,
    ( ! [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),X2,k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(X2)
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = X2
        | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK1)) )
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f600,f267])).

fof(f267,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f266])).

fof(f600,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = X2
        | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),X2,k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) )
    | ~ spl11_42
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f590,f273])).

fof(f273,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f272])).

fof(f590,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = X2
        | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),X2,k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) )
    | ~ spl11_42 ),
    inference(resolution,[],[f255,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2)
      | X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',redefinition_r2_funct_2)).

fof(f255,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f254])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X4,X3)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X4,X3)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X4,X3)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
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
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X3,X2) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',t79_tmap_1)).

fof(f1031,plain,
    ( ~ spl11_131
    | spl11_132
    | ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_12
    | spl11_15
    | ~ spl11_16
    | spl11_19
    | ~ spl11_22
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f1018,f250,f243,f236,f229,f222,f208,f187,f173,f166,f159,f152,f145,f138,f131,f124,f117,f110,f1029,f1023])).

fof(f1023,plain,
    ( spl11_131
  <=> ~ m1_pre_topc(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_131])])).

fof(f1029,plain,
    ( spl11_132
  <=> k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK3,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_132])])).

fof(f1018,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK3,sK3,sK5))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_22
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f1017,f174])).

fof(f1017,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK3,sK3,sK5))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_22
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f996,f167])).

fof(f996,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK3,sK3,sK5))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_22
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(resolution,[],[f994,f188])).

fof(f994,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f993,f118])).

fof(f993,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f992,f125])).

fof(f992,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f991,f167])).

fof(f991,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f990,f111])).

fof(f990,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(duplicate_literal_removal,[],[f989])).

fof(f989,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(resolution,[],[f986,f441])).

fof(f441,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f440,f244])).

fof(f440,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) )
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_36
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f439,f251])).

fof(f439,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) )
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_36 ),
    inference(subsumption_resolution,[],[f438,f132])).

fof(f438,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) )
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_36 ),
    inference(subsumption_resolution,[],[f437,f139])).

fof(f437,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) )
    | ~ spl11_11
    | ~ spl11_36 ),
    inference(subsumption_resolution,[],[f434,f146])).

fof(f434,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,sK5)) )
    | ~ spl11_36 ),
    inference(resolution,[],[f83,f237])).

fof(f986,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f985,f125])).

fof(f985,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f984,f237])).

fof(f984,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f983,f244])).

fof(f983,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f982,f251])).

fof(f982,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f981,f167])).

fof(f981,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f980,f132])).

fof(f980,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f979,f139])).

fof(f979,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f978,f146])).

fof(f978,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f977,f111])).

fof(f977,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f976,f118])).

fof(f976,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(duplicate_literal_removal,[],[f975])).

fof(f975,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(resolution,[],[f972,f84])).

fof(f972,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f971,f153])).

fof(f971,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f970,f118])).

fof(f970,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f969,f125])).

fof(f969,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f968,f237])).

fof(f968,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f967,f244])).

fof(f967,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f966,f251])).

fof(f966,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f965,f167])).

fof(f965,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f964,f132])).

fof(f964,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f963,f139])).

fof(f963,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f962,f146])).

fof(f962,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f959,f111])).

fof(f959,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(sK2,sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(duplicate_literal_removal,[],[f958])).

fof(f958,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(resolution,[],[f947,f579])).

fof(f947,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK2,X0)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f946,f125])).

fof(f946,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f945,f237])).

fof(f945,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f944,f244])).

fof(f944,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f943,f251])).

fof(f943,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f942,f167])).

fof(f942,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f941,f132])).

fof(f941,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f940,f139])).

fof(f940,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f939,f146])).

fof(f939,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f938,f111])).

fof(f938,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f913,f118])).

fof(f913,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(duplicate_literal_removal,[],[f912])).

fof(f912,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(resolution,[],[f909,f85])).

fof(f909,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f908,f125])).

fof(f908,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f907,f153])).

fof(f907,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f906,f132])).

fof(f906,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f905,f139])).

fof(f905,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f904,f146])).

fof(f904,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f903,f111])).

fof(f903,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f902,f118])).

fof(f902,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(duplicate_literal_removal,[],[f901])).

fof(f901,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(resolution,[],[f891,f84])).

fof(f891,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f890,f125])).

fof(f890,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f889,f153])).

fof(f889,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f888,f132])).

fof(f888,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f887,f139])).

fof(f887,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f886,f146])).

fof(f886,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f885,f111])).

fof(f885,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f884,f118])).

fof(f884,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(duplicate_literal_removal,[],[f883])).

fof(f883,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X0,sK2,k3_tmap_1(sK0,sK1,sK3,X0,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0,sK5),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(resolution,[],[f856,f85])).

fof(f856,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(X1)
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f855,f125])).

fof(f855,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f854,f237])).

fof(f854,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f853,f244])).

fof(f853,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f852,f251])).

fof(f852,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f851,f153])).

fof(f851,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f850,f160])).

fof(f850,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f849,f167])).

fof(f849,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f848,f174])).

fof(f848,plain,
    ( ! [X1] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f847,f132])).

fof(f847,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f846,f139])).

fof(f846,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_11
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f845,f146])).

fof(f845,plain,
    ( ! [X1] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f844,f111])).

fof(f844,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_2
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f828,f118])).

fof(f828,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)))
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,X1,sK2,k3_tmap_1(sK0,sK1,sK3,X1,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(resolution,[],[f86,f529])).

fof(f529,plain,
    ( ! [X4] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X4)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = X4
        | ~ v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f528,f223])).

fof(f528,plain,
    ( ! [X4] :
        ( ~ v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = X4
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) )
    | ~ spl11_28
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f525,f230])).

fof(f525,plain,
    ( ! [X4] :
        ( ~ v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
        | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = X4
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) )
    | ~ spl11_28 ),
    inference(resolution,[],[f93,f209])).

fof(f1016,plain,
    ( ~ spl11_125
    | spl11_126
    | ~ spl11_129
    | ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_12
    | spl11_15
    | ~ spl11_16
    | spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f997,f250,f243,f236,f229,f222,f208,f173,f166,f159,f152,f145,f138,f131,f124,f117,f110,f1014,f1008,f1002])).

fof(f1002,plain,
    ( spl11_125
  <=> ~ m1_pre_topc(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_125])])).

fof(f1008,plain,
    ( spl11_126
  <=> k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK0,sK2,k3_tmap_1(sK0,sK1,sK3,sK0,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_126])])).

fof(f1014,plain,
    ( spl11_129
  <=> ~ m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_129])])).

fof(f997,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK0,sK2,k3_tmap_1(sK0,sK1,sK3,sK0,sK5))
    | ~ m1_pre_topc(sK0,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f995,f125])).

fof(f995,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK0,sK2,k3_tmap_1(sK0,sK1,sK3,sK0,sK5))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(resolution,[],[f994,f153])).

fof(f954,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_12
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | spl11_121 ),
    inference(avatar_contradiction_clause,[],[f953])).

fof(f953,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_121 ),
    inference(subsumption_resolution,[],[f952,f118])).

fof(f952,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_121 ),
    inference(subsumption_resolution,[],[f951,f125])).

fof(f951,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_121 ),
    inference(subsumption_resolution,[],[f950,f153])).

fof(f950,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_121 ),
    inference(subsumption_resolution,[],[f949,f111])).

fof(f949,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_121 ),
    inference(duplicate_literal_removal,[],[f948])).

fof(f948,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_121 ),
    inference(resolution,[],[f930,f446])).

fof(f930,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | ~ spl11_121 ),
    inference(avatar_component_clause,[],[f929])).

fof(f929,plain,
    ( spl11_121
  <=> ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_121])])).

fof(f937,plain,
    ( spl11_118
    | ~ spl11_121
    | ~ spl11_123
    | ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_12
    | spl11_15
    | ~ spl11_16
    | spl11_19
    | ~ spl11_22
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f918,f250,f243,f236,f229,f222,f208,f187,f173,f166,f159,f152,f145,f138,f131,f124,f117,f110,f935,f929,f923])).

fof(f923,plain,
    ( spl11_118
  <=> k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_118])])).

fof(f935,plain,
    ( spl11_123
  <=> ~ m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_123])])).

fof(f918,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_22
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f917,f188])).

fof(f917,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f916,f223])).

fof(f916,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f915,f230])).

fof(f915,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f914,f153])).

fof(f914,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f910,f160])).

fof(f910,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK5) = k3_tmap_1(sK0,sK1,sK2,sK2,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(resolution,[],[f909,f209])).

fof(f734,plain,
    ( ~ spl11_115
    | ~ spl11_117
    | ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_16
    | spl11_19
    | ~ spl11_24
    | spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | spl11_45 ),
    inference(avatar_split_clause,[],[f721,f263,f250,f243,f236,f201,f194,f173,f166,f145,f138,f131,f124,f117,f110,f732,f726])).

fof(f726,plain,
    ( spl11_115
  <=> ~ m1_pre_topc(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_115])])).

fof(f732,plain,
    ( spl11_117
  <=> ~ v5_pre_topc(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_117])])).

fof(f721,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f720,f125])).

fof(f720,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f719,f237])).

fof(f719,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f718,f244])).

fof(f718,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_40
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f717,f251])).

fof(f717,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_24
    | ~ spl11_27
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f716,f195])).

fof(f716,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_27
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f715,f202])).

fof(f715,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f714,f167])).

fof(f714,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_19
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f713,f174])).

fof(f713,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f712,f132])).

fof(f712,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f711,f139])).

fof(f711,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_11
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f710,f146])).

fof(f710,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f709,f111])).

fof(f709,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_2
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f708,f118])).

fof(f708,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK0)
    | ~ spl11_45 ),
    inference(resolution,[],[f81,f264])).

fof(f654,plain,
    ( ~ spl11_113
    | ~ spl11_108 ),
    inference(avatar_split_clause,[],[f646,f637,f652])).

fof(f652,plain,
    ( spl11_113
  <=> ~ sP10(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_113])])).

fof(f637,plain,
    ( spl11_108
  <=> r2_hidden(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_108])])).

fof(f646,plain,
    ( ~ sP10(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl11_108 ),
    inference(resolution,[],[f638,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP10(X1) ) ),
    inference(general_splitting,[],[f97,f103_D])).

fof(f103,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP10(X1) ) ),
    inference(cnf_transformation,[],[f103_D])).

fof(f103_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP10(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',t5_subset)).

fof(f638,plain,
    ( r2_hidden(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl11_108 ),
    inference(avatar_component_clause,[],[f637])).

fof(f645,plain,
    ( spl11_108
    | spl11_110
    | ~ spl11_42 ),
    inference(avatar_split_clause,[],[f594,f254,f643,f637])).

fof(f643,plain,
    ( spl11_110
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_110])])).

fof(f594,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | r2_hidden(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl11_42 ),
    inference(resolution,[],[f255,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',t2_subset)).

fof(f632,plain,
    ( spl11_104
    | ~ spl11_107
    | ~ spl11_42 ),
    inference(avatar_split_clause,[],[f593,f254,f630,f624])).

fof(f624,plain,
    ( spl11_104
  <=> sP10(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_104])])).

fof(f630,plain,
    ( spl11_107
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_107])])).

fof(f593,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))
    | sP10(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ spl11_42 ),
    inference(resolution,[],[f255,f103])).

fof(f619,plain,
    ( ~ spl11_103
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f612,f272,f266,f254,f617])).

fof(f617,plain,
    ( spl11_103
  <=> ~ sP9(u1_struct_0(sK1),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_103])])).

fof(f612,plain,
    ( ~ sP9(u1_struct_0(sK1),u1_struct_0(sK4))
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f611,f273])).

fof(f611,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ sP9(u1_struct_0(sK1),u1_struct_0(sK4))
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f592,f267])).

fof(f592,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ sP9(u1_struct_0(sK1),u1_struct_0(sK4))
    | ~ spl11_42 ),
    inference(resolution,[],[f255,f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ sP9(X1,X0) ) ),
    inference(general_splitting,[],[f95,f101_D])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2)
      | sP9(X1,X0) ) ),
    inference(cnf_transformation,[],[f101_D])).

fof(f101_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_funct_1(X2)
          | ~ v1_funct_2(X2,X0,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_funct_2(X0,X1,X2,X2) )
    <=> ~ sP9(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',reflexivity_r2_funct_2)).

fof(f610,plain,
    ( spl11_100
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f603,f272,f266,f254,f608])).

fof(f608,plain,
    ( spl11_100
  <=> r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_100])])).

fof(f603,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f602,f273])).

fof(f602,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ spl11_42
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f591,f267])).

fof(f591,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ spl11_42 ),
    inference(resolution,[],[f255,f105])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f577,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | spl11_43 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f575,f125])).

fof(f575,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f574,f237])).

fof(f574,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f573,f244])).

fof(f573,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_40
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f572,f251])).

fof(f572,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f571,f195])).

fof(f571,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f570,f167])).

fof(f570,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f569,f132])).

fof(f569,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f568,f139])).

fof(f568,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_11
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f567,f146])).

fof(f567,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f566,f111])).

fof(f566,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_2
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f557,f118])).

fof(f557,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_43 ),
    inference(resolution,[],[f85,f258])).

fof(f258,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl11_43 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl11_43
  <=> ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).

fof(f556,plain,
    ( ~ spl11_93
    | spl11_94
    | ~ spl11_97
    | ~ spl11_99
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f531,f250,f243,f236,f554,f548,f542,f536])).

fof(f536,plain,
    ( spl11_93
  <=> ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_93])])).

fof(f542,plain,
    ( spl11_94
  <=> sK5 = sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_94])])).

fof(f548,plain,
    ( spl11_97
  <=> ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_97])])).

fof(f554,plain,
    ( spl11_99
  <=> ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_99])])).

fof(f531,plain,
    ( ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))))
    | sK5 = sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))),sK5)
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(resolution,[],[f527,f87])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',existence_m1_subset_1)).

fof(f527,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | sK5 = X0
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X0,sK5) )
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f526,f244])).

fof(f526,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | sK5 = X0
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X0,sK5) )
    | ~ spl11_36
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f523,f251])).

fof(f523,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | sK5 = X0
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X0,sK5) )
    | ~ spl11_36 ),
    inference(resolution,[],[f93,f237])).

fof(f514,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | spl11_47 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f512,f125])).

fof(f512,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f511,f237])).

fof(f511,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f510,f244])).

fof(f510,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_40
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f509,f251])).

fof(f509,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f508,f195])).

fof(f508,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f507,f167])).

fof(f507,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f506,f132])).

fof(f506,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f505,f139])).

fof(f505,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_11
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f504,f146])).

fof(f504,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f503,f111])).

fof(f503,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_2
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f502,f118])).

fof(f502,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl11_47 ),
    inference(resolution,[],[f84,f270])).

fof(f270,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl11_47 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl11_47
  <=> ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).

fof(f501,plain,
    ( spl11_90
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f494,f229,f222,f208,f499])).

fof(f499,plain,
    ( spl11_90
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).

fof(f494,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f493,f230])).

fof(f493,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ spl11_28
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f483,f223])).

fof(f483,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ spl11_28 ),
    inference(resolution,[],[f105,f209])).

fof(f492,plain,
    ( spl11_88
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f485,f250,f243,f236,f490])).

fof(f490,plain,
    ( spl11_88
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f485,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,sK5)
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f484,f251])).

fof(f484,plain,
    ( ~ v1_funct_1(sK5)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,sK5)
    | ~ spl11_36
    | ~ spl11_38 ),
    inference(subsumption_resolution,[],[f481,f244])).

fof(f481,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,sK5)
    | ~ spl11_36 ),
    inference(resolution,[],[f105,f237])).

fof(f479,plain,
    ( ~ spl11_87
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f472,f229,f222,f208,f477])).

fof(f477,plain,
    ( spl11_87
  <=> ~ sP9(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_87])])).

fof(f472,plain,
    ( ~ sP9(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f471,f230])).

fof(f471,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ sP9(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl11_28
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f461,f223])).

fof(f461,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ sP9(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl11_28 ),
    inference(resolution,[],[f102,f209])).

fof(f470,plain,
    ( ~ spl11_85
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f463,f250,f243,f236,f468])).

fof(f468,plain,
    ( spl11_85
  <=> ~ sP9(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_85])])).

fof(f463,plain,
    ( ~ sP9(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f462,f251])).

fof(f462,plain,
    ( ~ v1_funct_1(sK5)
    | ~ sP9(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl11_36
    | ~ spl11_38 ),
    inference(subsumption_resolution,[],[f459,f244])).

fof(f459,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ sP9(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl11_36 ),
    inference(resolution,[],[f102,f237])).

fof(f455,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | spl11_49 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f453,f118])).

fof(f453,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f452,f125])).

fof(f452,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_24
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f451,f195])).

fof(f451,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f450,f167])).

fof(f450,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f449,f111])).

fof(f449,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_11
    | ~ spl11_36
    | ~ spl11_38
    | ~ spl11_40
    | ~ spl11_49 ),
    inference(resolution,[],[f441,f276])).

fof(f276,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ spl11_49 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl11_49
  <=> ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f433,plain,
    ( spl11_80
    | ~ spl11_83
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f407,f208,f431,f425])).

fof(f425,plain,
    ( spl11_80
  <=> sP10(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_80])])).

fof(f431,plain,
    ( spl11_83
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_83])])).

fof(f407,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | sP10(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | ~ spl11_28 ),
    inference(resolution,[],[f103,f209])).

fof(f420,plain,
    ( spl11_76
    | ~ spl11_79
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f405,f236,f418,f412])).

fof(f412,plain,
    ( spl11_76
  <=> sP10(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_76])])).

fof(f418,plain,
    ( spl11_79
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_79])])).

fof(f405,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
    | sP10(sK5)
    | ~ spl11_36 ),
    inference(resolution,[],[f103,f237])).

fof(f402,plain,
    ( ~ spl11_75
    | ~ spl11_68 ),
    inference(avatar_split_clause,[],[f394,f376,f400])).

fof(f400,plain,
    ( spl11_75
  <=> ~ sP10(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_75])])).

fof(f376,plain,
    ( spl11_68
  <=> r2_hidden(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f394,plain,
    ( ~ sP10(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl11_68 ),
    inference(resolution,[],[f377,f104])).

fof(f377,plain,
    ( r2_hidden(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl11_68 ),
    inference(avatar_component_clause,[],[f376])).

fof(f393,plain,
    ( ~ spl11_73
    | ~ spl11_64 ),
    inference(avatar_split_clause,[],[f385,f363,f391])).

fof(f391,plain,
    ( spl11_73
  <=> ~ sP10(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_73])])).

fof(f363,plain,
    ( spl11_64
  <=> r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).

fof(f385,plain,
    ( ~ sP10(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl11_64 ),
    inference(resolution,[],[f364,f104])).

fof(f364,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl11_64 ),
    inference(avatar_component_clause,[],[f363])).

fof(f384,plain,
    ( spl11_68
    | spl11_70
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f358,f208,f382,f376])).

fof(f382,plain,
    ( spl11_70
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f358,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r2_hidden(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl11_28 ),
    inference(resolution,[],[f99,f209])).

fof(f371,plain,
    ( spl11_64
    | spl11_66
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f356,f236,f369,f363])).

fof(f369,plain,
    ( spl11_66
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f356,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | r2_hidden(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl11_36 ),
    inference(resolution,[],[f99,f237])).

fof(f355,plain,
    ( spl11_58
    | ~ spl11_61
    | ~ spl11_22
    | ~ spl11_54 ),
    inference(avatar_split_clause,[],[f354,f305,f187,f337,f331])).

fof(f331,plain,
    ( spl11_58
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f337,plain,
    ( spl11_61
  <=> ~ v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f305,plain,
    ( spl11_54
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f354,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_pre_topc(sK2)
    | ~ spl11_22
    | ~ spl11_54 ),
    inference(subsumption_resolution,[],[f323,f306])).

fof(f306,plain,
    ( l1_pre_topc(sK3)
    | ~ spl11_54 ),
    inference(avatar_component_clause,[],[f305])).

fof(f323,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_pre_topc(sK2)
    | ~ spl11_22 ),
    inference(resolution,[],[f91,f188])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',cc1_pre_topc)).

fof(f353,plain,
    ( spl11_62
    | ~ spl11_59
    | ~ spl11_20
    | ~ spl11_52 ),
    inference(avatar_split_clause,[],[f352,f297,f180,f328,f349])).

fof(f349,plain,
    ( spl11_62
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_62])])).

fof(f328,plain,
    ( spl11_59
  <=> ~ v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f297,plain,
    ( spl11_52
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f352,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK4)
    | ~ spl11_20
    | ~ spl11_52 ),
    inference(subsumption_resolution,[],[f322,f298])).

fof(f298,plain,
    ( l1_pre_topc(sK2)
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f297])).

fof(f322,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK4)
    | ~ spl11_20 ),
    inference(resolution,[],[f91,f181])).

fof(f351,plain,
    ( spl11_62
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f344,f194,f117,f110,f349])).

fof(f344,plain,
    ( v2_pre_topc(sK4)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f343,f118])).

fof(f343,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK4)
    | ~ spl11_0
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f321,f111])).

fof(f321,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK4)
    | ~ spl11_24 ),
    inference(resolution,[],[f91,f195])).

fof(f342,plain,
    ( spl11_60
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f335,f166,f117,f110,f340])).

fof(f340,plain,
    ( spl11_60
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f335,plain,
    ( v2_pre_topc(sK3)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f334,f118])).

fof(f334,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl11_0
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f320,f111])).

fof(f320,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl11_16 ),
    inference(resolution,[],[f91,f167])).

fof(f333,plain,
    ( spl11_58
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f326,f152,f117,f110,f331])).

fof(f326,plain,
    ( v2_pre_topc(sK2)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f325,f118])).

fof(f325,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f319,f111])).

fof(f319,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ spl11_12 ),
    inference(resolution,[],[f91,f153])).

fof(f317,plain,
    ( spl11_52
    | ~ spl11_55
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f290,f187,f302,f297])).

fof(f302,plain,
    ( spl11_55
  <=> ~ l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_55])])).

fof(f290,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK2)
    | ~ spl11_22 ),
    inference(resolution,[],[f89,f188])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',dt_m1_pre_topc)).

fof(f316,plain,
    ( spl11_56
    | ~ spl11_53
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f289,f180,f294,f313])).

fof(f313,plain,
    ( spl11_56
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f294,plain,
    ( spl11_53
  <=> ~ l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f289,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4)
    | ~ spl11_20 ),
    inference(resolution,[],[f89,f181])).

fof(f315,plain,
    ( spl11_56
    | ~ spl11_0
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f308,f194,f110,f313])).

fof(f308,plain,
    ( l1_pre_topc(sK4)
    | ~ spl11_0
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f288,f111])).

fof(f288,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK4)
    | ~ spl11_24 ),
    inference(resolution,[],[f89,f195])).

fof(f307,plain,
    ( spl11_54
    | ~ spl11_0
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f300,f166,f110,f305])).

fof(f300,plain,
    ( l1_pre_topc(sK3)
    | ~ spl11_0
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f287,f111])).

fof(f287,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3)
    | ~ spl11_16 ),
    inference(resolution,[],[f89,f167])).

fof(f299,plain,
    ( spl11_52
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f292,f152,f110,f297])).

fof(f292,plain,
    ( l1_pre_topc(sK2)
    | ~ spl11_0
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f286,f111])).

fof(f286,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl11_12 ),
    inference(resolution,[],[f89,f153])).

fof(f284,plain,(
    spl11_50 ),
    inference(avatar_split_clause,[],[f90,f282])).

fof(f282,plain,
    ( spl11_50
  <=> l1_pre_topc(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f90,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',existence_l1_pre_topc)).

fof(f277,plain,
    ( ~ spl11_43
    | ~ spl11_45
    | ~ spl11_47
    | ~ spl11_49 ),
    inference(avatar_split_clause,[],[f57,f275,f269,f263,f257])).

fof(f57,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X4,X2)
                            & m1_pre_topc(X2,X3) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ( m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                  & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                                  & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                                  & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) )
                               => ( m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                                  & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                                  & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                                  & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
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
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X2)
                          & m1_pre_topc(X2,X3) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                                & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) )
                             => ( m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                                & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                                & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                                & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',t90_tmap_1)).

fof(f252,plain,(
    spl11_40 ),
    inference(avatar_split_clause,[],[f58,f250])).

fof(f58,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f245,plain,(
    spl11_38 ),
    inference(avatar_split_clause,[],[f59,f243])).

fof(f59,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f238,plain,(
    spl11_36 ),
    inference(avatar_split_clause,[],[f60,f236])).

fof(f60,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f231,plain,(
    spl11_34 ),
    inference(avatar_split_clause,[],[f61,f229])).

fof(f61,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f224,plain,(
    spl11_32 ),
    inference(avatar_split_clause,[],[f62,f222])).

fof(f62,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f217,plain,(
    spl11_30 ),
    inference(avatar_split_clause,[],[f63,f215])).

fof(f63,plain,(
    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f210,plain,(
    spl11_28 ),
    inference(avatar_split_clause,[],[f64,f208])).

fof(f64,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f203,plain,(
    ~ spl11_27 ),
    inference(avatar_split_clause,[],[f65,f201])).

fof(f65,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f196,plain,(
    spl11_24 ),
    inference(avatar_split_clause,[],[f66,f194])).

fof(f66,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f189,plain,(
    spl11_22 ),
    inference(avatar_split_clause,[],[f67,f187])).

fof(f67,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f182,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f68,f180])).

fof(f68,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f175,plain,(
    ~ spl11_19 ),
    inference(avatar_split_clause,[],[f69,f173])).

fof(f69,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f168,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f70,f166])).

fof(f70,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f161,plain,(
    ~ spl11_15 ),
    inference(avatar_split_clause,[],[f71,f159])).

fof(f71,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f154,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f72,f152])).

fof(f72,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f147,plain,(
    ~ spl11_11 ),
    inference(avatar_split_clause,[],[f73,f145])).

fof(f73,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f140,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f74,f138])).

fof(f74,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f133,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f75,f131])).

fof(f75,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f126,plain,(
    ~ spl11_5 ),
    inference(avatar_split_clause,[],[f76,f124])).

fof(f76,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f119,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f77,f117])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f112,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f78,f110])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------

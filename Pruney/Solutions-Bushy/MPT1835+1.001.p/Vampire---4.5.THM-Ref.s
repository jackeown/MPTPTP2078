%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1835+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:42 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  578 (2047 expanded)
%              Number of leaves         :  159 (1142 expanded)
%              Depth                    :    9
%              Number of atoms          : 4955 (15561 expanded)
%              Number of equality atoms :  139 ( 553 expanded)
%              Maximal formula depth    :   35 (  10 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f178,f183,f188,f193,f198,f215,f222,f227,f234,f239,f246,f251,f257,f261,f268,f273,f282,f292,f309,f317,f319,f326,f330,f332,f344,f346,f359,f367,f373,f377,f391,f395,f415,f419,f434,f443,f447,f451,f456,f471,f485,f489,f493,f497,f501,f505,f525,f529,f533,f537,f541,f545,f549,f571,f575,f579,f583,f591,f595,f599,f601,f603,f616,f620,f624,f628,f632,f637,f641,f647,f651,f666,f670,f698,f702,f706,f714,f753,f757,f786,f791,f805,f857,f861,f862,f863,f866,f867,f879,f907,f912,f934,f938,f942,f950,f954,f958,f962,f967,f971,f997,f1004,f1005,f1020,f1057,f1062,f1087,f1091,f1095,f1103,f1107,f1111,f1115,f1120,f1124,f1154,f1185,f1212,f1272,f1276,f1288,f1297,f1306,f1337,f1340,f1349])).

fof(f1349,plain,
    ( ~ spl6_7
    | ~ spl6_146
    | ~ spl6_147
    | ~ spl6_15
    | spl6_8
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_14
    | ~ spl6_117
    | ~ spl6_139 ),
    inference(avatar_split_clause,[],[f1330,f1274,f986,f155,f302,f150,f125,f160,f1346,f1342,f120])).

fof(f120,plain,
    ( spl6_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1342,plain,
    ( spl6_146
  <=> sK0 = k1_tsep_1(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_146])])).

fof(f1346,plain,
    ( spl6_147
  <=> r4_tsep_1(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_147])])).

fof(f160,plain,
    ( spl6_15
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f125,plain,
    ( spl6_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f150,plain,
    ( spl6_13
  <=> v5_pre_topc(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f302,plain,
    ( spl6_40
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f155,plain,
    ( spl6_14
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f986,plain,
    ( spl6_117
  <=> sK4 = k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f1274,plain,
    ( spl6_139
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ l1_struct_0(X1)
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1),X1,sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1),u1_struct_0(X1),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1))
        | ~ r4_tsep_1(sK0,sK2,X1)
        | sK0 != k1_tsep_1(sK0,sK2,X1)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_139])])).

fof(f1330,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ r4_tsep_1(sK0,sK2,sK2)
    | sK0 != k1_tsep_1(sK0,sK2,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl6_117
    | ~ spl6_139 ),
    inference(superposition,[],[f1275,f988])).

fof(f988,plain,
    ( sK4 = k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_117 ),
    inference(avatar_component_clause,[],[f986])).

fof(f1275,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1),u1_struct_0(X1),u1_struct_0(sK1))
        | ~ l1_struct_0(X1)
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1),X1,sK1)
        | v2_struct_0(X1)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1))
        | ~ r4_tsep_1(sK0,sK2,X1)
        | sK0 != k1_tsep_1(sK0,sK2,X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl6_139 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f1340,plain,
    ( ~ spl6_10
    | ~ spl6_16
    | ~ spl6_22
    | spl6_11
    | ~ spl6_20
    | ~ spl6_43
    | ~ spl6_21
    | ~ spl6_9
    | ~ spl6_99
    | ~ spl6_139 ),
    inference(avatar_split_clause,[],[f1339,f1274,f794,f130,f190,f314,f185,f140,f195,f165,f135])).

fof(f135,plain,
    ( spl6_10
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f165,plain,
    ( spl6_16
  <=> r4_tsep_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f195,plain,
    ( spl6_22
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f140,plain,
    ( spl6_11
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f185,plain,
    ( spl6_20
  <=> v5_pre_topc(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f314,plain,
    ( spl6_43
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f190,plain,
    ( spl6_21
  <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f130,plain,
    ( spl6_9
  <=> sK0 = k1_tsep_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f794,plain,
    ( spl6_99
  <=> sK5 = k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f1339,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK3)
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl6_9
    | ~ spl6_99
    | ~ spl6_139 ),
    inference(trivial_inequality_removal,[],[f1338])).

fof(f1338,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK3)
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl6_9
    | ~ spl6_99
    | ~ spl6_139 ),
    inference(forward_demodulation,[],[f1329,f132])).

fof(f132,plain,
    ( sK0 = k1_tsep_1(sK0,sK2,sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1329,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK3)
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK5)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | sK0 != k1_tsep_1(sK0,sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl6_99
    | ~ spl6_139 ),
    inference(superposition,[],[f1275,f796])).

fof(f796,plain,
    ( sK5 = k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_99 ),
    inference(avatar_component_clause,[],[f794])).

fof(f1337,plain,
    ( ~ spl6_76
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_41
    | spl6_145
    | ~ spl6_139 ),
    inference(avatar_split_clause,[],[f1331,f1274,f1335,f306,f212,f208,f200,f585])).

fof(f585,plain,
    ( spl6_76
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f200,plain,
    ( spl6_23
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f208,plain,
    ( spl6_25
  <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f212,plain,
    ( spl6_26
  <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f306,plain,
    ( spl6_41
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f1335,plain,
    ( spl6_145
  <=> ! [X4] :
        ( ~ l1_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | sK0 != k1_tsep_1(sK0,sK2,X4)
        | ~ r4_tsep_1(sK0,sK2,X4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X4))
        | v2_struct_0(X4)
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X4),X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_145])])).

fof(f1331,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(X4)
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X4),X4,sK1)
        | v2_struct_0(X4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X4))
        | ~ r4_tsep_1(sK0,sK2,X4)
        | sK0 != k1_tsep_1(sK0,sK2,X4)
        | ~ m1_pre_topc(X4,sK0)
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ l1_struct_0(sK0) )
    | ~ spl6_139 ),
    inference(duplicate_literal_removal,[],[f1328])).

fof(f1328,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(X4)
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X4),X4,sK1)
        | v2_struct_0(X4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X4))
        | ~ r4_tsep_1(sK0,sK2,X4)
        | sK0 != k1_tsep_1(sK0,sK2,X4)
        | ~ m1_pre_topc(X4,sK0)
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ l1_struct_0(X4)
        | ~ l1_struct_0(sK0) )
    | ~ spl6_139 ),
    inference(resolution,[],[f1275,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f1306,plain,
    ( ~ spl6_7
    | ~ spl6_143
    | ~ spl6_144
    | ~ spl6_15
    | spl6_8
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_14
    | ~ spl6_117
    | ~ spl6_138 ),
    inference(avatar_split_clause,[],[f1281,f1270,f986,f155,f302,f150,f125,f160,f1303,f1299,f120])).

fof(f1299,plain,
    ( spl6_143
  <=> sK0 = k1_tsep_1(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_143])])).

fof(f1303,plain,
    ( spl6_144
  <=> r4_tsep_1(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_144])])).

fof(f1270,plain,
    ( spl6_138
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),X0,sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0))
        | ~ r4_tsep_1(sK0,sK3,X0)
        | sK0 != k1_tsep_1(sK0,sK3,X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_138])])).

fof(f1281,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_struct_0(sK2)
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(sK4)
    | ~ r4_tsep_1(sK0,sK3,sK2)
    | sK0 != k1_tsep_1(sK0,sK3,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl6_117
    | ~ spl6_138 ),
    inference(superposition,[],[f1271,f988])).

fof(f1271,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ l1_struct_0(X0)
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),X0,sK1)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0))
        | ~ r4_tsep_1(sK0,sK3,X0)
        | sK0 != k1_tsep_1(sK0,sK3,X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl6_138 ),
    inference(avatar_component_clause,[],[f1270])).

fof(f1297,plain,
    ( ~ spl6_10
    | ~ spl6_141
    | ~ spl6_142
    | ~ spl6_22
    | spl6_11
    | ~ spl6_20
    | ~ spl6_43
    | ~ spl6_21
    | ~ spl6_99
    | ~ spl6_138 ),
    inference(avatar_split_clause,[],[f1280,f1270,f794,f190,f314,f185,f140,f195,f1294,f1290,f135])).

fof(f1290,plain,
    ( spl6_141
  <=> sK0 = k1_tsep_1(sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_141])])).

fof(f1294,plain,
    ( spl6_142
  <=> r4_tsep_1(sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_142])])).

fof(f1280,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK3)
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK5)
    | ~ r4_tsep_1(sK0,sK3,sK3)
    | sK0 != k1_tsep_1(sK0,sK3,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl6_99
    | ~ spl6_138 ),
    inference(superposition,[],[f1271,f796])).

fof(f1288,plain,
    ( ~ spl6_76
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_41
    | spl6_140
    | ~ spl6_138 ),
    inference(avatar_split_clause,[],[f1282,f1270,f1286,f306,f212,f208,f200,f585])).

fof(f1286,plain,
    ( spl6_140
  <=> ! [X4] :
        ( ~ l1_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | sK0 != k1_tsep_1(sK0,sK3,X4)
        | ~ r4_tsep_1(sK0,sK3,X4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X4))
        | v2_struct_0(X4)
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X4),X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_140])])).

fof(f1282,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(X4)
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X4),X4,sK1)
        | v2_struct_0(X4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X4))
        | ~ r4_tsep_1(sK0,sK3,X4)
        | sK0 != k1_tsep_1(sK0,sK3,X4)
        | ~ m1_pre_topc(X4,sK0)
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ l1_struct_0(sK0) )
    | ~ spl6_138 ),
    inference(duplicate_literal_removal,[],[f1279])).

fof(f1279,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(X4)
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X4),X4,sK1)
        | v2_struct_0(X4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X4))
        | ~ r4_tsep_1(sK0,sK3,X4)
        | sK0 != k1_tsep_1(sK0,sK3,X4)
        | ~ m1_pre_topc(X4,sK0)
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ l1_struct_0(X4)
        | ~ l1_struct_0(sK0) )
    | ~ spl6_138 ),
    inference(resolution,[],[f1271,f78])).

fof(f1276,plain,
    ( ~ spl6_76
    | ~ spl6_41
    | spl6_24
    | spl6_3
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_139
    | ~ spl6_7
    | spl6_8
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_12
    | ~ spl6_117 ),
    inference(avatar_split_clause,[],[f1264,f986,f145,f90,f115,f110,f105,f212,f208,f200,f125,f120,f1274,f160,f155,f150,f95,f100,f204,f306,f585])).

fof(f204,plain,
    ( spl6_24
  <=> v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f100,plain,
    ( spl6_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f95,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f105,plain,
    ( spl6_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f110,plain,
    ( spl6_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f115,plain,
    ( spl6_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f90,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f145,plain,
    ( spl6_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f1264,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | sK0 != k1_tsep_1(sK0,sK2,X1)
        | ~ r4_tsep_1(sK0,sK2,X1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK4,sK2,sK1)
        | ~ v2_pre_topc(sK0)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1),u1_struct_0(X1),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1),X1,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(sK0) )
    | ~ spl6_117 ),
    inference(superposition,[],[f509,f988])).

fof(f509,plain,(
    ! [X14,X12,X15,X13,X16] :
      ( ~ m1_subset_1(k2_tmap_1(X12,X13,X14,X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
      | ~ l1_pre_topc(X12)
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
      | v2_struct_0(X15)
      | ~ m1_pre_topc(X15,X12)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X12)
      | k1_tsep_1(X12,X15,X16) != X12
      | ~ r4_tsep_1(X12,X15,X16)
      | ~ v1_funct_1(k2_tmap_1(X12,X13,X14,X15))
      | ~ v1_funct_2(k2_tmap_1(X12,X13,X14,X15),u1_struct_0(X15),u1_struct_0(X13))
      | ~ v5_pre_topc(k2_tmap_1(X12,X13,X14,X15),X15,X13)
      | ~ v2_pre_topc(X12)
      | ~ v1_funct_1(k2_tmap_1(X12,X13,X14,X16))
      | ~ v1_funct_2(k2_tmap_1(X12,X13,X14,X16),u1_struct_0(X16),u1_struct_0(X13))
      | ~ v5_pre_topc(k2_tmap_1(X12,X13,X14,X16),X16,X13)
      | v2_struct_0(X12)
      | v5_pre_topc(X14,X12,X13)
      | ~ l1_struct_0(X13)
      | ~ l1_struct_0(X16)
      | ~ l1_struct_0(X12) ) ),
    inference(duplicate_literal_removal,[],[f508])).

fof(f508,plain,(
    ! [X14,X12,X15,X13,X16] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
      | v2_struct_0(X15)
      | ~ m1_pre_topc(X15,X12)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X12)
      | k1_tsep_1(X12,X15,X16) != X12
      | ~ r4_tsep_1(X12,X15,X16)
      | ~ v1_funct_1(k2_tmap_1(X12,X13,X14,X15))
      | ~ v1_funct_2(k2_tmap_1(X12,X13,X14,X15),u1_struct_0(X15),u1_struct_0(X13))
      | ~ v5_pre_topc(k2_tmap_1(X12,X13,X14,X15),X15,X13)
      | ~ m1_subset_1(k2_tmap_1(X12,X13,X14,X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
      | ~ v1_funct_1(k2_tmap_1(X12,X13,X14,X16))
      | ~ v1_funct_2(k2_tmap_1(X12,X13,X14,X16),u1_struct_0(X16),u1_struct_0(X13))
      | ~ v5_pre_topc(k2_tmap_1(X12,X13,X14,X16),X16,X13)
      | v2_struct_0(X12)
      | v5_pre_topc(X14,X12,X13)
      | ~ l1_struct_0(X13)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
      | ~ l1_struct_0(X16)
      | ~ l1_struct_0(X12) ) ),
    inference(resolution,[],[f60,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
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
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( r4_tsep_1(X0,X3,X4)
                          & k1_tsep_1(X0,X3,X4) = X0 )
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).

fof(f1272,plain,
    ( ~ spl6_76
    | ~ spl6_41
    | spl6_24
    | spl6_3
    | ~ spl6_2
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_22
    | spl6_138
    | ~ spl6_10
    | spl6_11
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_19
    | ~ spl6_99 ),
    inference(avatar_split_clause,[],[f1263,f794,f180,f90,f115,f110,f105,f212,f208,f200,f140,f135,f1270,f195,f190,f185,f95,f100,f204,f306,f585])).

fof(f180,plain,
    ( spl6_19
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f1263,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | sK0 != k1_tsep_1(sK0,sK3,X0)
        | ~ r4_tsep_1(sK0,sK3,X0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK5,sK3,sK1)
        | ~ v2_pre_topc(sK0)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),X0,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(sK0) )
    | ~ spl6_99 ),
    inference(superposition,[],[f509,f796])).

fof(f1212,plain,
    ( spl6_3
    | ~ spl6_1
    | ~ spl6_2
    | spl6_137
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f1207,f469,f1210,f95,f90,f100])).

fof(f1210,plain,
    ( spl6_137
  <=> ! [X5,X7,X8,X6] :
        ( v1_funct_1(k2_tmap_1(sK0,X5,k10_tmap_1(sK0,X5,sK2,sK3,X6,X7),X8))
        | ~ m1_pre_topc(X8,sK0)
        | ~ m1_subset_1(k10_tmap_1(sK0,X5,sK2,sK3,X6,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
        | ~ v1_funct_2(k10_tmap_1(sK0,X5,sK2,sK3,X6,X7),u1_struct_0(sK0),u1_struct_0(X5))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5))))
        | ~ v1_funct_1(k10_tmap_1(sK0,X5,sK2,sK3,X6,X7))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(sK2),u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X5))))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_137])])).

fof(f469,plain,
    ( spl6_60
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f1207,plain,
    ( ! [X6,X8,X7,X5] :
        ( v1_funct_1(k2_tmap_1(sK0,X5,k10_tmap_1(sK0,X5,sK2,sK3,X6,X7),X8))
        | ~ v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5))
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X5))))
        | ~ v1_funct_2(X6,u1_struct_0(sK2),u1_struct_0(X5))
        | ~ v1_funct_1(X6)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5)
        | ~ v1_funct_1(k10_tmap_1(sK0,X5,sK2,sK3,X6,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5))))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_2(k10_tmap_1(sK0,X5,sK2,sK3,X6,X7),u1_struct_0(sK0),u1_struct_0(X5))
        | ~ m1_subset_1(k10_tmap_1(sK0,X5,sK2,sK3,X6,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
        | ~ m1_pre_topc(X8,sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_60 ),
    inference(duplicate_literal_removal,[],[f1206])).

fof(f1206,plain,
    ( ! [X6,X8,X7,X5] :
        ( v1_funct_1(k2_tmap_1(sK0,X5,k10_tmap_1(sK0,X5,sK2,sK3,X6,X7),X8))
        | ~ v1_funct_2(X7,u1_struct_0(sK3),u1_struct_0(X5))
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X5))))
        | ~ v1_funct_2(X6,u1_struct_0(sK2),u1_struct_0(X5))
        | ~ v1_funct_1(X6)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5)
        | ~ v1_funct_1(k10_tmap_1(sK0,X5,sK2,sK3,X6,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X5))))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ v1_funct_1(k10_tmap_1(sK0,X5,sK2,sK3,X6,X7))
        | ~ v1_funct_2(k10_tmap_1(sK0,X5,sK2,sK3,X6,X7),u1_struct_0(sK0),u1_struct_0(X5))
        | ~ m1_subset_1(k10_tmap_1(sK0,X5,sK2,sK3,X6,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X5))))
        | ~ m1_pre_topc(X8,sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_60 ),
    inference(superposition,[],[f567,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
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
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f567,plain,
    ( ! [X35,X33,X36,X34] :
        ( v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(X34),k10_tmap_1(sK0,X34,sK2,sK3,X35,X33),X36))
        | ~ v1_funct_2(X33,u1_struct_0(sK3),u1_struct_0(X34))
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X34))))
        | ~ v1_funct_2(X35,u1_struct_0(sK2),u1_struct_0(X34))
        | ~ v1_funct_1(X35)
        | ~ l1_pre_topc(X34)
        | ~ v2_pre_topc(X34)
        | v2_struct_0(X34)
        | ~ v1_funct_1(k10_tmap_1(sK0,X34,sK2,sK3,X35,X33))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X34)))) )
    | ~ spl6_60 ),
    inference(resolution,[],[f470,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f470,plain,
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
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f469])).

fof(f1185,plain,
    ( ~ spl6_7
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_135
    | spl6_136
    | ~ spl6_103 ),
    inference(avatar_split_clause,[],[f1173,f859,f1182,f1179,f115,f110,f105,f212,f208,f200,f120])).

fof(f1179,plain,
    ( spl6_135
  <=> ! [X5] :
        ( v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(sK0,X5)
        | ~ m1_pre_topc(sK2,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_135])])).

fof(f1182,plain,
    ( spl6_136
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_136])])).

fof(f859,plain,
    ( spl6_103
  <=> ! [X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f1173,plain,
    ( ! [X5] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK2)),sK4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK2,X5)
        | ~ m1_pre_topc(sK0,X5)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK0) )
    | ~ spl6_103 ),
    inference(duplicate_literal_removal,[],[f1172])).

fof(f1172,plain,
    ( ! [X5] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK2)),sK4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK2,X5)
        | ~ m1_pre_topc(sK0,X5)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,X5)
        | ~ m1_pre_topc(sK2,X5)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(X5) )
    | ~ spl6_103 ),
    inference(superposition,[],[f860,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
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
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f860,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl6_103 ),
    inference(avatar_component_clause,[],[f859])).

fof(f1154,plain,
    ( ~ spl6_10
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_133
    | spl6_134
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f1142,f855,f1151,f1148,f115,f110,f105,f212,f208,f200,f135])).

fof(f1148,plain,
    ( spl6_133
  <=> ! [X5] :
        ( v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(sK0,X5)
        | ~ m1_pre_topc(sK3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_133])])).

fof(f1151,plain,
    ( spl6_134
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK3)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_134])])).

fof(f855,plain,
    ( spl6_102
  <=> ! [X0] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f1142,plain,
    ( ! [X5] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK3)),sK5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK3,X5)
        | ~ m1_pre_topc(sK0,X5)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl6_102 ),
    inference(duplicate_literal_removal,[],[f1141])).

fof(f1141,plain,
    ( ! [X5] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK3)),sK5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(sK3,X5)
        | ~ m1_pre_topc(sK0,X5)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,X5)
        | ~ m1_pre_topc(sK3,X5)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X5) )
    | ~ spl6_102 ),
    inference(superposition,[],[f856,f71])).

fof(f856,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl6_102 ),
    inference(avatar_component_clause,[],[f855])).

fof(f1124,plain,
    ( spl6_132
    | ~ spl6_15
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1079,f1059,f160,f1122])).

fof(f1122,plain,
    ( spl6_132
  <=> ! [X11] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_132])])).

fof(f1059,plain,
    ( spl6_121
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f1079,plain,
    ( ! [X11] :
        ( ~ v1_funct_1(sK4)
        | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X11)) )
    | ~ spl6_121 ),
    inference(resolution,[],[f1061,f75])).

fof(f1061,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_121 ),
    inference(avatar_component_clause,[],[f1059])).

fof(f1120,plain,
    ( spl6_131
    | ~ spl6_15
    | ~ spl6_122
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1078,f1059,f1081,f160,f1117])).

fof(f1117,plain,
    ( spl6_131
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).

fof(f1081,plain,
    ( spl6_122
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).

fof(f1078,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | ~ spl6_121 ),
    inference(resolution,[],[f1061,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f1115,plain,
    ( ~ spl6_122
    | ~ spl6_15
    | spl6_130
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1077,f1059,f1113,f160,f1081])).

fof(f1113,plain,
    ( spl6_130
  <=> ! [X10] :
        ( ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X10,sK4)
        | sK4 = X10
        | ~ v1_funct_1(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_130])])).

fof(f1077,plain,
    ( ! [X10] :
        ( ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X10)
        | sK4 = X10
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X10,sK4) )
    | ~ spl6_121 ),
    inference(resolution,[],[f1061,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2)
      | X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1111,plain,
    ( spl6_129
    | ~ spl6_76
    | ~ spl6_122
    | ~ spl6_15
    | ~ spl6_41
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1076,f1059,f306,f160,f1081,f585,f1109])).

fof(f1109,plain,
    ( spl6_129
  <=> ! [X9] :
        ( ~ l1_struct_0(X9)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).

fof(f1076,plain,
    ( ! [X9] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X9)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X9)) )
    | ~ spl6_121 ),
    inference(resolution,[],[f1061,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1107,plain,
    ( spl6_3
    | ~ spl6_126
    | ~ spl6_122
    | ~ spl6_15
    | spl6_128
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1075,f1059,f95,f90,f115,f110,f105,f1105,f160,f1081,f1097,f100])).

fof(f1097,plain,
    ( spl6_126
  <=> v5_pre_topc(sK4,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_126])])).

fof(f1105,plain,
    ( spl6_128
  <=> ! [X7,X8] :
        ( v2_struct_0(X7)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X7))
        | ~ r4_tsep_1(sK0,X7,X8)
        | sK0 != k1_tsep_1(sK0,X7,X8)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,sK0)
        | ~ m1_pre_topc(X7,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).

fof(f1075,plain,
    ( ! [X8,X7] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,sK0)
        | sK0 != k1_tsep_1(sK0,X7,X8)
        | ~ r4_tsep_1(sK0,X7,X8)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X7))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK4,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl6_121 ),
    inference(resolution,[],[f1061,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1103,plain,
    ( spl6_3
    | ~ spl6_126
    | ~ spl6_122
    | ~ spl6_15
    | spl6_127
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1074,f1059,f95,f90,f115,f110,f105,f1101,f160,f1081,f1097,f100])).

fof(f1101,plain,
    ( spl6_127
  <=> ! [X5,X6] :
        ( v2_struct_0(X5)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X6))
        | ~ r4_tsep_1(sK0,X5,X6)
        | sK0 != k1_tsep_1(sK0,X5,X6)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | ~ m1_pre_topc(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_127])])).

fof(f1074,plain,
    ( ! [X6,X5] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | sK0 != k1_tsep_1(sK0,X5,X6)
        | ~ r4_tsep_1(sK0,X5,X6)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X6))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK4,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl6_121 ),
    inference(resolution,[],[f1061,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1095,plain,
    ( ~ spl6_122
    | ~ spl6_15
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_125
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1073,f1059,f1093,f115,f110,f105,f100,f160,f1081])).

fof(f1093,plain,
    ( spl6_125
  <=> ! [X3,X2,X4] :
        ( ~ v2_pre_topc(X2)
        | v1_funct_1(k10_tmap_1(X2,sK1,X3,sK0,X4,sK4))
        | v2_struct_0(X2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK0,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).

fof(f1073,plain,
    ( ! [X4,X2,X3] :
        ( ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X2)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(X2)
        | v1_funct_1(k10_tmap_1(X2,sK1,X3,sK0,X4,sK4)) )
    | ~ spl6_121 ),
    inference(resolution,[],[f1061,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | v2_struct_0(X0)
      | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f1091,plain,
    ( spl6_3
    | ~ spl6_122
    | ~ spl6_15
    | spl6_124
    | ~ spl6_51
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1072,f1059,f389,f1089,f160,f1081,f100])).

fof(f1089,plain,
    ( spl6_124
  <=> ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK1,sK0,sK2,sK4,sK4))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).

fof(f389,plain,
    ( spl6_51
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | v1_funct_1(k10_tmap_1(X0,sK1,X1,sK2,X2,sK4))
        | v2_struct_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f1072,plain,
    ( ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK1,sK0,sK2,sK4,sK4))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl6_51
    | ~ spl6_121 ),
    inference(resolution,[],[f1061,f390])).

fof(f390,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | v1_funct_1(k10_tmap_1(X0,sK1,X1,sK2,X2,sK4))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f389])).

fof(f1087,plain,
    ( spl6_3
    | ~ spl6_122
    | ~ spl6_15
    | spl6_123
    | ~ spl6_52
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1071,f1059,f393,f1085,f160,f1081,f100])).

fof(f1085,plain,
    ( spl6_123
  <=> ! [X0] :
        ( v1_funct_1(k10_tmap_1(X0,sK1,sK0,sK3,sK4,sK5))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).

fof(f393,plain,
    ( spl6_52
  <=> ! [X3,X5,X4] :
        ( ~ v2_pre_topc(X3)
        | v1_funct_1(k10_tmap_1(X3,sK1,X4,sK3,X5,sK5))
        | v2_struct_0(X3)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ l1_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f1071,plain,
    ( ! [X0] :
        ( v1_funct_1(k10_tmap_1(X0,sK1,sK0,sK3,sK4,sK5))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_52
    | ~ spl6_121 ),
    inference(resolution,[],[f1061,f394])).

fof(f394,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | v1_funct_1(k10_tmap_1(X3,sK1,X4,sK3,X5,sK5))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f393])).

fof(f1062,plain,
    ( spl6_3
    | ~ spl6_7
    | ~ spl6_25
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_26
    | ~ spl6_23
    | spl6_121
    | ~ spl6_117 ),
    inference(avatar_split_clause,[],[f1047,f986,f1059,f200,f212,f95,f90,f115,f110,f105,f208,f120,f100])).

fof(f1047,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_117 ),
    inference(superposition,[],[f340,f988])).

fof(f340,plain,(
    ! [X4,X2,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X3)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X4,X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,(
    ! [X4,X2,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X3)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ m1_pre_topc(X4,X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f76,f80])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1057,plain,
    ( spl6_24
    | spl6_3
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_7
    | spl6_8
    | spl6_120
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_117 ),
    inference(avatar_split_clause,[],[f1034,f986,f145,f95,f90,f115,f110,f105,f212,f208,f200,f1055,f125,f120,f160,f155,f150,f100,f204])).

fof(f1055,plain,
    ( spl6_120
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),X0,sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0))
        | ~ r4_tsep_1(sK0,X0,sK2)
        | sK0 != k1_tsep_1(sK0,X0,sK2)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f1034,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | sK0 != k1_tsep_1(sK0,X0,sK2)
        | ~ r4_tsep_1(sK0,X0,sK2)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK4,sK2,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) )
    | ~ spl6_117 ),
    inference(superposition,[],[f60,f988])).

fof(f1020,plain,
    ( ~ spl6_76
    | ~ spl6_40
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_41
    | spl6_119 ),
    inference(avatar_split_clause,[],[f1019,f994,f306,f212,f208,f200,f302,f585])).

fof(f994,plain,
    ( spl6_119
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).

fof(f1019,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | spl6_119 ),
    inference(resolution,[],[f996,f78])).

fof(f996,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_119 ),
    inference(avatar_component_clause,[],[f994])).

fof(f1005,plain,
    ( ~ spl6_40
    | ~ spl6_83
    | spl6_118 ),
    inference(avatar_split_clause,[],[f1003,f990,f626,f302])).

fof(f626,plain,
    ( spl6_83
  <=> ! [X9] :
        ( ~ l1_struct_0(X9)
        | v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f990,plain,
    ( spl6_118
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f1003,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl6_83
    | spl6_118 ),
    inference(resolution,[],[f992,f627])).

fof(f627,plain,
    ( ! [X9] :
        ( v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X9))
        | ~ l1_struct_0(X9) )
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f626])).

fof(f992,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | spl6_118 ),
    inference(avatar_component_clause,[],[f990])).

fof(f1004,plain,
    ( ~ spl6_7
    | ~ spl6_88
    | spl6_118 ),
    inference(avatar_split_clause,[],[f1002,f990,f649,f120])).

fof(f649,plain,
    ( spl6_88
  <=> ! [X2] :
        ( v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X2))
        | ~ m1_pre_topc(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f1002,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ spl6_88
    | spl6_118 ),
    inference(resolution,[],[f992,f650])).

fof(f650,plain,
    ( ! [X2] :
        ( v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X2))
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f649])).

fof(f997,plain,
    ( spl6_117
    | ~ spl6_118
    | ~ spl6_119
    | ~ spl6_26
    | ~ spl6_25
    | ~ spl6_23
    | ~ spl6_76
    | ~ spl6_54
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f984,f788,f417,f585,f200,f208,f212,f994,f990,f986])).

fof(f417,plain,
    ( spl6_54
  <=> ! [X3,X4] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK2),sK4)
        | ~ l1_struct_0(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK2))
        | sK4 = k2_tmap_1(X3,sK1,X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f788,plain,
    ( spl6_98
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f984,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | sK4 = k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_54
    | ~ spl6_98 ),
    inference(resolution,[],[f790,f418])).

fof(f418,plain,
    ( ! [X4,X3] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK2),sK4)
        | ~ l1_struct_0(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK2))
        | sK4 = k2_tmap_1(X3,sK1,X4,sK2) )
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f417])).

fof(f790,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f788])).

fof(f971,plain,
    ( spl6_116
    | ~ spl6_22
    | ~ spl6_105 ),
    inference(avatar_split_clause,[],[f926,f909,f195,f969])).

fof(f969,plain,
    ( spl6_116
  <=> ! [X11] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

fof(f909,plain,
    ( spl6_105
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).

fof(f926,plain,
    ( ! [X11] :
        ( ~ v1_funct_1(sK5)
        | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,X11)) )
    | ~ spl6_105 ),
    inference(resolution,[],[f911,f75])).

fof(f911,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_105 ),
    inference(avatar_component_clause,[],[f909])).

fof(f967,plain,
    ( spl6_115
    | ~ spl6_22
    | ~ spl6_106
    | ~ spl6_105 ),
    inference(avatar_split_clause,[],[f925,f909,f928,f195,f964])).

fof(f964,plain,
    ( spl6_115
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).

fof(f928,plain,
    ( spl6_106
  <=> v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).

fof(f925,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK5)
    | ~ spl6_105 ),
    inference(resolution,[],[f911,f88])).

fof(f962,plain,
    ( ~ spl6_106
    | ~ spl6_22
    | spl6_114
    | ~ spl6_105 ),
    inference(avatar_split_clause,[],[f924,f909,f960,f195,f928])).

fof(f960,plain,
    ( spl6_114
  <=> ! [X10] :
        ( ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X10,sK5)
        | sK5 = X10
        | ~ v1_funct_1(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).

fof(f924,plain,
    ( ! [X10] :
        ( ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X10)
        | sK5 = X10
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X10,sK5) )
    | ~ spl6_105 ),
    inference(resolution,[],[f911,f70])).

fof(f958,plain,
    ( spl6_113
    | ~ spl6_76
    | ~ spl6_106
    | ~ spl6_22
    | ~ spl6_41
    | ~ spl6_105 ),
    inference(avatar_split_clause,[],[f923,f909,f306,f195,f928,f585,f956])).

fof(f956,plain,
    ( spl6_113
  <=> ! [X9] :
        ( ~ l1_struct_0(X9)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_113])])).

fof(f923,plain,
    ( ! [X9] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X9)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X9)) )
    | ~ spl6_105 ),
    inference(resolution,[],[f911,f77])).

fof(f954,plain,
    ( spl6_3
    | ~ spl6_110
    | ~ spl6_106
    | ~ spl6_22
    | spl6_112
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_105 ),
    inference(avatar_split_clause,[],[f922,f909,f95,f90,f115,f110,f105,f952,f195,f928,f944,f100])).

fof(f944,plain,
    ( spl6_110
  <=> v5_pre_topc(sK5,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f952,plain,
    ( spl6_112
  <=> ! [X7,X8] :
        ( v2_struct_0(X7)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X7))
        | ~ r4_tsep_1(sK0,X7,X8)
        | sK0 != k1_tsep_1(sK0,X7,X8)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,sK0)
        | ~ m1_pre_topc(X7,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).

fof(f922,plain,
    ( ! [X8,X7] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,sK0)
        | sK0 != k1_tsep_1(sK0,X7,X8)
        | ~ r4_tsep_1(sK0,X7,X8)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X7))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK5,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl6_105 ),
    inference(resolution,[],[f911,f61])).

fof(f950,plain,
    ( spl6_3
    | ~ spl6_110
    | ~ spl6_106
    | ~ spl6_22
    | spl6_111
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_105 ),
    inference(avatar_split_clause,[],[f921,f909,f95,f90,f115,f110,f105,f948,f195,f928,f944,f100])).

fof(f948,plain,
    ( spl6_111
  <=> ! [X5,X6] :
        ( v2_struct_0(X5)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X6))
        | ~ r4_tsep_1(sK0,X5,X6)
        | sK0 != k1_tsep_1(sK0,X5,X6)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | ~ m1_pre_topc(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f921,plain,
    ( ! [X6,X5] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | sK0 != k1_tsep_1(sK0,X5,X6)
        | ~ r4_tsep_1(sK0,X5,X6)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X6))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK5,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl6_105 ),
    inference(resolution,[],[f911,f65])).

fof(f942,plain,
    ( ~ spl6_106
    | ~ spl6_22
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_109
    | ~ spl6_105 ),
    inference(avatar_split_clause,[],[f920,f909,f940,f115,f110,f105,f100,f195,f928])).

fof(f940,plain,
    ( spl6_109
  <=> ! [X3,X2,X4] :
        ( ~ v2_pre_topc(X2)
        | v1_funct_1(k10_tmap_1(X2,sK1,X3,sK0,X4,sK5))
        | v2_struct_0(X2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK0,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).

fof(f920,plain,
    ( ! [X4,X2,X3] :
        ( ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X2)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(X2)
        | v1_funct_1(k10_tmap_1(X2,sK1,X3,sK0,X4,sK5)) )
    | ~ spl6_105 ),
    inference(resolution,[],[f911,f72])).

fof(f938,plain,
    ( spl6_3
    | ~ spl6_106
    | ~ spl6_22
    | spl6_108
    | ~ spl6_51
    | ~ spl6_105 ),
    inference(avatar_split_clause,[],[f919,f909,f389,f936,f195,f928,f100])).

fof(f936,plain,
    ( spl6_108
  <=> ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK1,sK0,sK2,sK5,sK4))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f919,plain,
    ( ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK1,sK0,sK2,sK5,sK4))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl6_51
    | ~ spl6_105 ),
    inference(resolution,[],[f911,f390])).

fof(f934,plain,
    ( spl6_3
    | ~ spl6_106
    | ~ spl6_22
    | spl6_107
    | ~ spl6_52
    | ~ spl6_105 ),
    inference(avatar_split_clause,[],[f918,f909,f393,f932,f195,f928,f100])).

fof(f932,plain,
    ( spl6_107
  <=> ! [X0] :
        ( v1_funct_1(k10_tmap_1(X0,sK1,sK0,sK3,sK5,sK5))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f918,plain,
    ( ! [X0] :
        ( v1_funct_1(k10_tmap_1(X0,sK1,sK0,sK3,sK5,sK5))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_52
    | ~ spl6_105 ),
    inference(resolution,[],[f911,f394])).

fof(f912,plain,
    ( spl6_3
    | ~ spl6_10
    | ~ spl6_25
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_26
    | ~ spl6_23
    | spl6_105
    | ~ spl6_99 ),
    inference(avatar_split_clause,[],[f901,f794,f909,f200,f212,f95,f90,f115,f110,f105,f208,f135,f100])).

fof(f901,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_99 ),
    inference(superposition,[],[f340,f796])).

fof(f907,plain,
    ( spl6_24
    | spl6_3
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_10
    | spl6_11
    | spl6_104
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_19
    | ~ spl6_99 ),
    inference(avatar_split_clause,[],[f888,f794,f180,f95,f90,f115,f110,f105,f212,f208,f200,f905,f140,f135,f195,f190,f185,f100,f204])).

fof(f905,plain,
    ( spl6_104
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),X0,sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0))
        | ~ r4_tsep_1(sK0,X0,sK3)
        | sK0 != k1_tsep_1(sK0,X0,sK3)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f888,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | sK0 != k1_tsep_1(sK0,X0,sK3)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK5,sK3,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) )
    | ~ spl6_99 ),
    inference(superposition,[],[f60,f796])).

fof(f879,plain,
    ( ~ spl6_76
    | ~ spl6_43
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_41
    | spl6_101 ),
    inference(avatar_split_clause,[],[f878,f802,f306,f212,f208,f200,f314,f585])).

fof(f802,plain,
    ( spl6_101
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f878,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl6_101 ),
    inference(resolution,[],[f804,f78])).

fof(f804,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl6_101 ),
    inference(avatar_component_clause,[],[f802])).

fof(f867,plain,
    ( ~ spl6_43
    | ~ spl6_83
    | spl6_100 ),
    inference(avatar_split_clause,[],[f865,f798,f626,f314])).

fof(f798,plain,
    ( spl6_100
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f865,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl6_83
    | spl6_100 ),
    inference(resolution,[],[f800,f627])).

fof(f800,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | spl6_100 ),
    inference(avatar_component_clause,[],[f798])).

fof(f866,plain,
    ( ~ spl6_10
    | ~ spl6_88
    | spl6_100 ),
    inference(avatar_split_clause,[],[f864,f798,f649,f135])).

fof(f864,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ spl6_88
    | spl6_100 ),
    inference(resolution,[],[f800,f650])).

fof(f863,plain,
    ( spl6_3
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_7
    | ~ spl6_38
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | spl6_103
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f836,f224,f859,f95,f90,f115,f110,f105,f289,f120,f212,f208,f200,f100])).

fof(f289,plain,
    ( spl6_38
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f224,plain,
    ( spl6_28
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f836,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(X1) )
    | ~ spl6_28 ),
    inference(duplicate_literal_removal,[],[f823])).

fof(f823,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(X1) )
    | ~ spl6_28 ),
    inference(superposition,[],[f226,f355])).

fof(f355,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X5)
      | ~ m1_pre_topc(X3,X5)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X0,X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f347])).

fof(f347,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X5)
      | ~ m1_pre_topc(X3,X5)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X5)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X4)
      | ~ m1_pre_topc(X3,X4)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4) ) ),
    inference(superposition,[],[f71,f71])).

fof(f226,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f224])).

fof(f862,plain,
    ( spl6_3
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_10
    | ~ spl6_38
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | spl6_102
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f837,f219,f855,f95,f90,f115,f110,f105,f289,f135,f212,f208,f200,f100])).

fof(f219,plain,
    ( spl6_27
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f837,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | ~ spl6_27 ),
    inference(duplicate_literal_removal,[],[f822])).

fof(f822,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0) )
    | ~ spl6_27 ),
    inference(superposition,[],[f221,f355])).

fof(f221,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f219])).

fof(f861,plain,
    ( spl6_3
    | ~ spl6_38
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_103
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f844,f224,f859,f115,f110,f105,f212,f208,f200,f120,f95,f90,f289,f100])).

fof(f844,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_28 ),
    inference(duplicate_literal_removal,[],[f815])).

fof(f815,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_28 ),
    inference(superposition,[],[f226,f355])).

fof(f857,plain,
    ( spl6_3
    | ~ spl6_38
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_102
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f845,f219,f855,f115,f110,f105,f212,f208,f200,f135,f95,f90,f289,f100])).

fof(f845,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_27 ),
    inference(duplicate_literal_removal,[],[f814])).

fof(f814,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_27 ),
    inference(superposition,[],[f221,f355])).

fof(f805,plain,
    ( spl6_99
    | ~ spl6_100
    | ~ spl6_101
    | ~ spl6_26
    | ~ spl6_25
    | ~ spl6_23
    | ~ spl6_76
    | ~ spl6_58
    | ~ spl6_97 ),
    inference(avatar_split_clause,[],[f792,f783,f449,f585,f200,f208,f212,f802,f798,f794])).

fof(f449,plain,
    ( spl6_58
  <=> ! [X7,X6] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(X6,sK1,X7,sK3),sK5)
        | ~ l1_struct_0(X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(sK1))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(k2_tmap_1(X6,sK1,X7,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X6,sK1,X7,sK3))
        | sK5 = k2_tmap_1(X6,sK1,X7,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f783,plain,
    ( spl6_97
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f792,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | sK5 = k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_58
    | ~ spl6_97 ),
    inference(resolution,[],[f785,f450])).

fof(f450,plain,
    ( ! [X6,X7] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(X6,sK1,X7,sK3),sK5)
        | ~ l1_struct_0(X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(sK1))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(k2_tmap_1(X6,sK1,X7,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X6,sK1,X7,sK3))
        | sK5 = k2_tmap_1(X6,sK1,X7,sK3) )
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f449])).

fof(f785,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ spl6_97 ),
    inference(avatar_component_clause,[],[f783])).

fof(f791,plain,
    ( spl6_3
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_7
    | ~ spl6_38
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | spl6_98
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f779,f224,f788,f95,f90,f115,f110,f105,f289,f120,f212,f208,f200,f100])).

fof(f779,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl6_28 ),
    inference(duplicate_literal_removal,[],[f768])).

fof(f768,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28 ),
    inference(superposition,[],[f226,f354])).

fof(f354,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X6,X10)
      | ~ m1_pre_topc(X9,X10)
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ m1_pre_topc(X9,X6)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(duplicate_literal_removal,[],[f348])).

fof(f348,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k3_tmap_1(X10,X7,X6,X9,X8)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X6,X10)
      | ~ m1_pre_topc(X9,X10)
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ m1_pre_topc(X9,X6)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ m1_pre_topc(X9,X6)
      | v2_struct_0(X6) ) ),
    inference(superposition,[],[f71,f80])).

fof(f786,plain,
    ( spl6_3
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_10
    | ~ spl6_38
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | spl6_97
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f780,f219,f783,f95,f90,f115,f110,f105,f289,f135,f212,f208,f200,f100])).

fof(f780,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl6_27 ),
    inference(duplicate_literal_removal,[],[f767])).

fof(f767,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_27 ),
    inference(superposition,[],[f221,f354])).

fof(f757,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_96
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f739,f389,f755,f115,f110,f105])).

fof(f755,plain,
    ( spl6_96
  <=> ! [X34,X36,X33,X35,X37] :
        ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(sK1))))
        | ~ l1_pre_topc(X37)
        | ~ m1_pre_topc(X34,X37)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(sK2,X37)
        | ~ v1_funct_2(k3_tmap_1(X35,sK1,X34,X36,X33),u1_struct_0(X34),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(X35,sK1,X34,X36,X33))
        | ~ v2_pre_topc(X37)
        | v2_struct_0(X37)
        | v1_funct_1(k10_tmap_1(X37,sK1,X34,sK2,k3_tmap_1(X35,sK1,X34,X36,X33),sK4))
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X36,X34)
        | ~ v1_funct_2(X33,u1_struct_0(X34),u1_struct_0(sK1))
        | ~ m1_pre_topc(X36,X35)
        | ~ m1_pre_topc(X34,X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ v1_funct_1(X33) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f739,plain,
    ( ! [X37,X35,X33,X36,X34] :
        ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(sK1))))
        | ~ v1_funct_1(X33)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X34,X35)
        | ~ m1_pre_topc(X36,X35)
        | ~ v1_funct_2(X33,u1_struct_0(X34),u1_struct_0(sK1))
        | ~ m1_pre_topc(X36,X34)
        | v2_struct_0(X35)
        | v1_funct_1(k10_tmap_1(X37,sK1,X34,sK2,k3_tmap_1(X35,sK1,X34,X36,X33),sK4))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ v1_funct_1(k3_tmap_1(X35,sK1,X34,X36,X33))
        | ~ v1_funct_2(k3_tmap_1(X35,sK1,X34,X36,X33),u1_struct_0(X34),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X37)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X37)
        | ~ l1_pre_topc(X37) )
    | ~ spl6_51 ),
    inference(resolution,[],[f352,f390])).

fof(f352,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( m1_subset_1(k3_tmap_1(X11,X8,X7,X10,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
      | ~ v1_funct_1(X9)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X8)
      | ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X7,X11)
      | ~ m1_pre_topc(X10,X11)
      | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
      | ~ m1_pre_topc(X10,X7)
      | v2_struct_0(X11) ) ),
    inference(duplicate_literal_removal,[],[f351])).

fof(f351,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( m1_subset_1(k3_tmap_1(X11,X8,X7,X10,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
      | ~ v1_funct_1(X9)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X8)
      | ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X7,X11)
      | ~ m1_pre_topc(X10,X11)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
      | ~ m1_pre_topc(X10,X7)
      | v2_struct_0(X11) ) ),
    inference(superposition,[],[f76,f71])).

fof(f753,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_95
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f738,f393,f751,f115,f110,f105])).

fof(f751,plain,
    ( spl6_95
  <=> ! [X32,X29,X31,X28,X30] :
        ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(sK1))))
        | ~ l1_pre_topc(X32)
        | ~ m1_pre_topc(X29,X32)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(sK3,X32)
        | ~ v1_funct_2(k3_tmap_1(X30,sK1,X29,X31,X28),u1_struct_0(X29),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(X30,sK1,X29,X31,X28))
        | ~ v2_pre_topc(X32)
        | v2_struct_0(X32)
        | v1_funct_1(k10_tmap_1(X32,sK1,X29,sK3,k3_tmap_1(X30,sK1,X29,X31,X28),sK5))
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X31,X29)
        | ~ v1_funct_2(X28,u1_struct_0(X29),u1_struct_0(sK1))
        | ~ m1_pre_topc(X31,X30)
        | ~ m1_pre_topc(X29,X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ v1_funct_1(X28) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f738,plain,
    ( ! [X30,X28,X31,X29,X32] :
        ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(sK1))))
        | ~ v1_funct_1(X28)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X29,X30)
        | ~ m1_pre_topc(X31,X30)
        | ~ v1_funct_2(X28,u1_struct_0(X29),u1_struct_0(sK1))
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | v1_funct_1(k10_tmap_1(X32,sK1,X29,sK3,k3_tmap_1(X30,sK1,X29,X31,X28),sK5))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ v1_funct_1(k3_tmap_1(X30,sK1,X29,X31,X28))
        | ~ v1_funct_2(k3_tmap_1(X30,sK1,X29,X31,X28),u1_struct_0(X29),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X32)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X32)
        | ~ l1_pre_topc(X32) )
    | ~ spl6_52 ),
    inference(resolution,[],[f352,f394])).

fof(f714,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_94
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f710,f328,f712,f115,f110,f105])).

fof(f712,plain,
    ( spl6_94
  <=> ! [X1,X0,X2] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X2,sK1,sK3,X1,X0),sK5)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X1,sK3)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(k3_tmap_1(X2,sK1,sK3,X1,X0),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(X2,sK1,sK3,X1,X0))
        | sK5 = k3_tmap_1(X2,sK1,sK3,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f328,plain,
    ( spl6_45
  <=> ! [X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X1,sK5)
        | sK5 = X1
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f710,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X2,sK1,sK3,X1,X0),sK5)
        | sK5 = k3_tmap_1(X2,sK1,sK3,X1,X0)
        | ~ v1_funct_1(k3_tmap_1(X2,sK1,sK3,X1,X0))
        | ~ v1_funct_2(k3_tmap_1(X2,sK1,sK3,X1,X0),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,X2)
        | ~ m1_pre_topc(X1,X2)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X2) )
    | ~ spl6_45 ),
    inference(duplicate_literal_removal,[],[f707])).

fof(f707,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X2,sK1,sK3,X1,X0),sK5)
        | sK5 = k3_tmap_1(X2,sK1,sK3,X1,X0)
        | ~ v1_funct_1(k3_tmap_1(X2,sK1,sK3,X1,X0))
        | ~ v1_funct_2(k3_tmap_1(X2,sK1,sK3,X1,X0),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,X2)
        | ~ m1_pre_topc(X1,X2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X2) )
    | ~ spl6_45 ),
    inference(superposition,[],[f439,f71])).

fof(f439,plain,
    ( ! [X8,X9] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X8,X9),sK5)
        | sK5 = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X8,X9)
        | ~ v1_funct_1(k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X8,X9))
        | ~ v1_funct_2(k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),X8,X9),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(X8) )
    | ~ spl6_45 ),
    inference(resolution,[],[f329,f76])).

fof(f329,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X1,sK5)
        | sK5 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f328])).

fof(f706,plain,
    ( spl6_11
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_30
    | ~ spl6_32
    | spl6_93
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f685,f328,f704,f248,f236,f115,f110,f105,f140])).

fof(f236,plain,
    ( spl6_30
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f248,plain,
    ( spl6_32
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f704,plain,
    ( spl6_93
  <=> ! [X38,X39] :
        ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(sK3,sK1,X38,X39),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK3,sK1,X38,X39))
        | sK5 = k2_tmap_1(sK3,sK1,X38,X39)
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,X38,X39),sK5)
        | ~ m1_pre_topc(X39,sK3)
        | ~ v1_funct_2(X38,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X38) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f685,plain,
    ( ! [X39,X38] :
        ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(X38)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X38,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X39,sK3)
        | v2_struct_0(sK3)
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,X38,X39),sK5)
        | sK5 = k2_tmap_1(sK3,sK1,X38,X39)
        | ~ v1_funct_1(k2_tmap_1(sK3,sK1,X38,X39))
        | ~ v1_funct_2(k2_tmap_1(sK3,sK1,X38,X39),u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl6_45 ),
    inference(resolution,[],[f340,f329])).

fof(f702,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_92
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f689,f389,f700,f115,f110,f105])).

fof(f700,plain,
    ( spl6_92
  <=> ! [X32,X34,X33,X35] :
        ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(sK1))))
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X33,X35)
        | ~ m1_pre_topc(sK2,X35)
        | ~ v1_funct_2(k2_tmap_1(X33,sK1,X32,X34),u1_struct_0(X33),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X33,sK1,X32,X34))
        | ~ v2_pre_topc(X35)
        | v2_struct_0(X35)
        | v1_funct_1(k10_tmap_1(X35,sK1,X33,sK2,k2_tmap_1(X33,sK1,X32,X34),sK4))
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ v1_funct_2(X32,u1_struct_0(X33),u1_struct_0(sK1))
        | ~ l1_pre_topc(X33)
        | ~ v2_pre_topc(X33)
        | ~ v1_funct_1(X32) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f689,plain,
    ( ! [X35,X33,X34,X32] :
        ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(sK1))))
        | ~ v1_funct_1(X32)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X32,u1_struct_0(X33),u1_struct_0(sK1))
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | v1_funct_1(k10_tmap_1(X35,sK1,X33,sK2,k2_tmap_1(X33,sK1,X32,X34),sK4))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ v1_funct_1(k2_tmap_1(X33,sK1,X32,X34))
        | ~ v1_funct_2(k2_tmap_1(X33,sK1,X32,X34),u1_struct_0(X33),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X35)
        | ~ m1_pre_topc(X33,X35)
        | ~ l1_pre_topc(X35) )
    | ~ spl6_51 ),
    inference(duplicate_literal_removal,[],[f683])).

fof(f683,plain,
    ( ! [X35,X33,X34,X32] :
        ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(sK1))))
        | ~ v1_funct_1(X32)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X32,u1_struct_0(X33),u1_struct_0(sK1))
        | ~ m1_pre_topc(X34,X33)
        | v2_struct_0(X33)
        | v1_funct_1(k10_tmap_1(X35,sK1,X33,sK2,k2_tmap_1(X33,sK1,X32,X34),sK4))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ v1_funct_1(k2_tmap_1(X33,sK1,X32,X34))
        | ~ v1_funct_2(k2_tmap_1(X33,sK1,X32,X34),u1_struct_0(X33),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X35)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X35)
        | ~ l1_pre_topc(X35) )
    | ~ spl6_51 ),
    inference(resolution,[],[f340,f390])).

fof(f698,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_91
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f690,f393,f696,f115,f110,f105])).

fof(f696,plain,
    ( spl6_91
  <=> ! [X29,X31,X28,X30] :
        ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(sK1))))
        | ~ l1_pre_topc(X31)
        | ~ m1_pre_topc(X29,X31)
        | ~ m1_pre_topc(sK3,X31)
        | ~ v1_funct_2(k2_tmap_1(X29,sK1,X28,X30),u1_struct_0(X29),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X29,sK1,X28,X30))
        | ~ v2_pre_topc(X31)
        | v2_struct_0(X31)
        | v1_funct_1(k10_tmap_1(X31,sK1,X29,sK3,k2_tmap_1(X29,sK1,X28,X30),sK5))
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X30,X29)
        | ~ v1_funct_2(X28,u1_struct_0(X29),u1_struct_0(sK1))
        | ~ l1_pre_topc(X29)
        | ~ v2_pre_topc(X29)
        | ~ v1_funct_1(X28) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f690,plain,
    ( ! [X30,X28,X31,X29] :
        ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(sK1))))
        | ~ v1_funct_1(X28)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X28,u1_struct_0(X29),u1_struct_0(sK1))
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | v1_funct_1(k10_tmap_1(X31,sK1,X29,sK3,k2_tmap_1(X29,sK1,X28,X30),sK5))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ v1_funct_1(k2_tmap_1(X29,sK1,X28,X30))
        | ~ v1_funct_2(k2_tmap_1(X29,sK1,X28,X30),u1_struct_0(X29),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X31)
        | ~ m1_pre_topc(X29,X31)
        | ~ l1_pre_topc(X31) )
    | ~ spl6_52 ),
    inference(duplicate_literal_removal,[],[f682])).

fof(f682,plain,
    ( ! [X30,X28,X31,X29] :
        ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(sK1))))
        | ~ v1_funct_1(X28)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X28,u1_struct_0(X29),u1_struct_0(sK1))
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | v1_funct_1(k10_tmap_1(X31,sK1,X29,sK3,k2_tmap_1(X29,sK1,X28,X30),sK5))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ v1_funct_1(k2_tmap_1(X29,sK1,X28,X30))
        | ~ v1_funct_2(k2_tmap_1(X29,sK1,X28,X30),u1_struct_0(X29),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X31)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X31)
        | ~ l1_pre_topc(X31) )
    | ~ spl6_52 ),
    inference(resolution,[],[f340,f394])).

fof(f670,plain,
    ( spl6_8
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_29
    | ~ spl6_31
    | spl6_90
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f661,f324,f668,f243,f231,f115,f110,f105,f125])).

fof(f231,plain,
    ( spl6_29
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f243,plain,
    ( spl6_31
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f668,plain,
    ( spl6_90
  <=> ! [X3,X4] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,X3,X4),sK4)
        | ~ m1_pre_topc(X4,sK2)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK1,X3,X4),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK1,X3,X4))
        | sK4 = k2_tmap_1(sK2,sK1,X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f324,plain,
    ( spl6_44
  <=> ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0,sK4)
        | sK4 = X0
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f661,plain,
    ( ! [X4,X3] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,X3,X4),sK4)
        | sK4 = k2_tmap_1(sK2,sK1,X3,X4)
        | ~ v1_funct_1(k2_tmap_1(sK2,sK1,X3,X4))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK1,X3,X4),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X3)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X4,sK2)
        | v2_struct_0(sK2) )
    | ~ spl6_44 ),
    inference(duplicate_literal_removal,[],[f660])).

fof(f660,plain,
    ( ! [X4,X3] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,X3,X4),sK4)
        | sK4 = k2_tmap_1(sK2,sK1,X3,X4)
        | ~ v1_funct_1(k2_tmap_1(sK2,sK1,X3,X4))
        | ~ v1_funct_2(k2_tmap_1(sK2,sK1,X3,X4),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X3)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X4,sK2)
        | v2_struct_0(sK2) )
    | ~ spl6_44 ),
    inference(superposition,[],[f411,f80])).

fof(f411,plain,
    ( ! [X6,X5] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X5,X6),sK4)
        | sK4 = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X5,X6)
        | ~ v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X5,X6))
        | ~ v1_funct_2(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X5,X6),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X5) )
    | ~ spl6_44 ),
    inference(resolution,[],[f325,f76])).

fof(f325,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0,sK4)
        | sK4 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f324])).

fof(f666,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_89
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f662,f324,f664,f115,f110,f105])).

fof(f664,plain,
    ( spl6_89
  <=> ! [X1,X0,X2] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X2,sK1,sK2,X1,X0),sK4)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X1,sK2)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(sK2,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(k3_tmap_1(X2,sK1,sK2,X1,X0),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(k3_tmap_1(X2,sK1,sK2,X1,X0))
        | sK4 = k3_tmap_1(X2,sK1,sK2,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f662,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X2,sK1,sK2,X1,X0),sK4)
        | sK4 = k3_tmap_1(X2,sK1,sK2,X1,X0)
        | ~ v1_funct_1(k3_tmap_1(X2,sK1,sK2,X1,X0))
        | ~ v1_funct_2(k3_tmap_1(X2,sK1,sK2,X1,X0),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,X2)
        | ~ m1_pre_topc(X1,X2)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK2)
        | v2_struct_0(X2) )
    | ~ spl6_44 ),
    inference(duplicate_literal_removal,[],[f659])).

fof(f659,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X2,sK1,sK2,X1,X0),sK4)
        | sK4 = k3_tmap_1(X2,sK1,sK2,X1,X0)
        | ~ v1_funct_1(k3_tmap_1(X2,sK1,sK2,X1,X0))
        | ~ v1_funct_2(k3_tmap_1(X2,sK1,sK2,X1,X0),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,X2)
        | ~ m1_pre_topc(X1,X2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK2)
        | v2_struct_0(X2) )
    | ~ spl6_44 ),
    inference(superposition,[],[f411,f71])).

fof(f651,plain,
    ( spl6_3
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_1
    | ~ spl6_2
    | spl6_88
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f643,f639,f649,f95,f90,f115,f110,f105,f212,f208,f200,f100])).

fof(f639,plain,
    ( spl6_86
  <=> ! [X11] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f643,plain,
    ( ! [X2] :
        ( v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X2))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_86 ),
    inference(superposition,[],[f640,f80])).

fof(f640,plain,
    ( ! [X11] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X11))
    | ~ spl6_86 ),
    inference(avatar_component_clause,[],[f639])).

fof(f647,plain,
    ( ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_87
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f642,f639,f645,f115,f110,f105,f212,f208,f200])).

fof(f645,plain,
    ( spl6_87
  <=> ! [X1,X0] :
        ( v1_funct_1(k3_tmap_1(X1,sK1,sK0,X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f642,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X1,sK1,sK0,X0,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ m1_pre_topc(X0,X1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1) )
    | ~ spl6_86 ),
    inference(superposition,[],[f640,f71])).

fof(f641,plain,
    ( spl6_86
    | ~ spl6_26
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f612,f200,f212,f639])).

fof(f612,plain,
    ( ! [X11] :
        ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X11)) )
    | ~ spl6_23 ),
    inference(resolution,[],[f201,f75])).

fof(f201,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f200])).

fof(f637,plain,
    ( spl6_85
    | ~ spl6_26
    | ~ spl6_25
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f611,f200,f208,f212,f634])).

fof(f634,plain,
    ( spl6_85
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f611,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_23 ),
    inference(resolution,[],[f201,f88])).

fof(f632,plain,
    ( ~ spl6_25
    | ~ spl6_26
    | spl6_84
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f610,f200,f630,f212,f208])).

fof(f630,plain,
    ( spl6_84
  <=> ! [X10] :
        ( ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X10,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = X10
        | ~ v1_funct_1(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f610,plain,
    ( ! [X10] :
        ( ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X10)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = X10
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X10,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    | ~ spl6_23 ),
    inference(resolution,[],[f201,f70])).

fof(f628,plain,
    ( spl6_83
    | ~ spl6_76
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_41
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f609,f200,f306,f212,f208,f585,f626])).

fof(f609,plain,
    ( ! [X9] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X9)
        | v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X9)) )
    | ~ spl6_23 ),
    inference(resolution,[],[f201,f77])).

fof(f624,plain,
    ( ~ spl6_25
    | ~ spl6_26
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_82
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f606,f200,f622,f115,f110,f105,f100,f212,f208])).

fof(f622,plain,
    ( spl6_82
  <=> ! [X3,X2,X4] :
        ( ~ v2_pre_topc(X2)
        | v1_funct_1(k10_tmap_1(X2,sK1,X3,sK0,X4,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | v2_struct_0(X2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK0,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f606,plain,
    ( ! [X4,X2,X3] :
        ( ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X2)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(X2)
        | v1_funct_1(k10_tmap_1(X2,sK1,X3,sK0,X4,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | ~ spl6_23 ),
    inference(resolution,[],[f201,f72])).

fof(f620,plain,
    ( spl6_3
    | ~ spl6_25
    | ~ spl6_26
    | spl6_81
    | ~ spl6_23
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f605,f389,f200,f618,f212,f208,f100])).

fof(f618,plain,
    ( spl6_81
  <=> ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK4))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f605,plain,
    ( ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK4))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl6_23
    | ~ spl6_51 ),
    inference(resolution,[],[f201,f390])).

fof(f616,plain,
    ( spl6_3
    | ~ spl6_25
    | ~ spl6_26
    | spl6_80
    | ~ spl6_23
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f604,f393,f200,f614,f212,f208,f100])).

fof(f614,plain,
    ( spl6_80
  <=> ! [X0] :
        ( v1_funct_1(k10_tmap_1(X0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f604,plain,
    ( ! [X0] :
        ( v1_funct_1(k10_tmap_1(X0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_23
    | ~ spl6_52 ),
    inference(resolution,[],[f201,f394])).

fof(f603,plain,
    ( spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_15
    | ~ spl6_14
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_21
    | ~ spl6_19
    | spl6_25
    | ~ spl6_59 ),
    inference(avatar_split_clause,[],[f602,f454,f208,f180,f190,f195,f145,f155,f160,f105,f110,f115])).

fof(f454,plain,
    ( spl6_59
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f602,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl6_25
    | ~ spl6_59 ),
    inference(resolution,[],[f210,f455])).

fof(f455,plain,
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
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f454])).

fof(f210,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f208])).

fof(f601,plain,
    ( ~ spl6_1
    | spl6_76 ),
    inference(avatar_split_clause,[],[f600,f585,f90])).

fof(f600,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_76 ),
    inference(resolution,[],[f587,f86])).

fof(f86,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f587,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_76 ),
    inference(avatar_component_clause,[],[f585])).

fof(f599,plain,
    ( spl6_3
    | spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | spl6_79
    | ~ spl6_51
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f564,f469,f389,f597,f105,f110,f115,f100])).

fof(f597,plain,
    ( spl6_79
  <=> ! [X25,X23,X24] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ l1_pre_topc(X25)
        | ~ m1_pre_topc(sK0,X25)
        | ~ m1_pre_topc(sK2,X25)
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X24,X23),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X24,X23))
        | ~ v2_pre_topc(X25)
        | v2_struct_0(X25)
        | v1_funct_1(k10_tmap_1(X25,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X24,X23),sK4))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f564,plain,
    ( ! [X24,X23,X25] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X23,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X24,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X24)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v1_funct_1(k10_tmap_1(X25,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X24,X23),sK4))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X24,X23))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X24,X23),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X25)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X25)
        | ~ l1_pre_topc(X25) )
    | ~ spl6_51
    | ~ spl6_60 ),
    inference(resolution,[],[f470,f390])).

fof(f595,plain,
    ( spl6_3
    | spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | spl6_78
    | ~ spl6_52
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f563,f469,f393,f593,f105,f110,f115,f100])).

fof(f593,plain,
    ( spl6_78
  <=> ! [X20,X22,X21] :
        ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(sK0,X22)
        | ~ m1_pre_topc(sK3,X22)
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X21,X20),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X21,X20))
        | ~ v2_pre_topc(X22)
        | v2_struct_0(X22)
        | v1_funct_1(k10_tmap_1(X22,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X21,X20),sK5))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f563,plain,
    ( ! [X21,X22,X20] :
        ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X20,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X21,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X21)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v1_funct_1(k10_tmap_1(X22,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X21,X20),sK5))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X21,X20))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X21,X20),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X22)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X22)
        | ~ l1_pre_topc(X22) )
    | ~ spl6_52
    | ~ spl6_60 ),
    inference(resolution,[],[f470,f394])).

fof(f591,plain,
    ( ~ spl6_76
    | spl6_77
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f562,f469,f589,f585])).

fof(f589,plain,
    ( spl6_77
  <=> ! [X16,X18,X17,X19] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X17))))
        | v1_funct_1(k2_tmap_1(sK0,X17,k10_tmap_1(sK0,X17,sK2,sK3,X18,X16),X19))
        | ~ l1_struct_0(X19)
        | ~ v1_funct_2(k10_tmap_1(sK0,X17,sK2,sK3,X18,X16),u1_struct_0(sK0),u1_struct_0(X17))
        | ~ v1_funct_1(k10_tmap_1(sK0,X17,sK2,sK3,X18,X16))
        | ~ l1_struct_0(X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(sK2),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X17))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(sK3),u1_struct_0(X17)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f562,plain,
    ( ! [X19,X17,X18,X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X17))))
        | ~ v1_funct_2(X16,u1_struct_0(sK3),u1_struct_0(X17))
        | ~ v1_funct_1(X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X17))))
        | ~ v1_funct_2(X18,u1_struct_0(sK2),u1_struct_0(X17))
        | ~ v1_funct_1(X18)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17)
        | ~ v1_funct_1(k10_tmap_1(sK0,X17,sK2,sK3,X18,X16))
        | ~ v1_funct_2(k10_tmap_1(sK0,X17,sK2,sK3,X18,X16),u1_struct_0(sK0),u1_struct_0(X17))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X19)
        | v1_funct_1(k2_tmap_1(sK0,X17,k10_tmap_1(sK0,X17,sK2,sK3,X18,X16),X19)) )
    | ~ spl6_60 ),
    inference(resolution,[],[f470,f77])).

fof(f583,plain,
    ( spl6_3
    | ~ spl6_1
    | ~ spl6_2
    | spl6_75
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f568,f469,f581,f95,f90,f100])).

fof(f581,plain,
    ( spl6_75
  <=> ! [X11,X13,X15,X12,X14] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X12))))
        | ~ v5_pre_topc(k10_tmap_1(sK0,X12,sK2,sK3,X13,X11),sK0,X12)
        | ~ v1_funct_2(k10_tmap_1(sK0,X12,sK2,sK3,X13,X11),u1_struct_0(sK0),u1_struct_0(X12))
        | ~ v1_funct_1(k10_tmap_1(sK0,X12,sK2,sK3,X13,X11))
        | v1_funct_1(k2_tmap_1(sK0,X12,k10_tmap_1(sK0,X12,sK2,sK3,X13,X11),X14))
        | v2_struct_0(X14)
        | ~ r4_tsep_1(sK0,X14,X15)
        | sK0 != k1_tsep_1(sK0,X14,X15)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,sK0)
        | ~ m1_pre_topc(X14,sK0)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,u1_struct_0(sK2),u1_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X12))))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X12)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f568,plain,
    ( ! [X14,X12,X15,X13,X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X12))))
        | ~ v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X12))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X12))))
        | ~ v1_funct_2(X13,u1_struct_0(sK2),u1_struct_0(X12))
        | ~ v1_funct_1(X13)
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,sK0)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,sK0)
        | sK0 != k1_tsep_1(sK0,X14,X15)
        | ~ r4_tsep_1(sK0,X14,X15)
        | v1_funct_1(k2_tmap_1(sK0,X12,k10_tmap_1(sK0,X12,sK2,sK3,X13,X11),X14))
        | ~ v1_funct_1(k10_tmap_1(sK0,X12,sK2,sK3,X13,X11))
        | ~ v1_funct_2(k10_tmap_1(sK0,X12,sK2,sK3,X13,X11),u1_struct_0(sK0),u1_struct_0(X12))
        | ~ v5_pre_topc(k10_tmap_1(sK0,X12,sK2,sK3,X13,X11),sK0,X12)
        | v2_struct_0(sK0) )
    | ~ spl6_60 ),
    inference(duplicate_literal_removal,[],[f561])).

fof(f561,plain,
    ( ! [X14,X12,X15,X13,X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X12))))
        | ~ v1_funct_2(X11,u1_struct_0(sK3),u1_struct_0(X12))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X12))))
        | ~ v1_funct_2(X13,u1_struct_0(sK2),u1_struct_0(X12))
        | ~ v1_funct_1(X13)
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,sK0)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,sK0)
        | sK0 != k1_tsep_1(sK0,X14,X15)
        | ~ r4_tsep_1(sK0,X14,X15)
        | v1_funct_1(k2_tmap_1(sK0,X12,k10_tmap_1(sK0,X12,sK2,sK3,X13,X11),X14))
        | ~ v1_funct_1(k10_tmap_1(sK0,X12,sK2,sK3,X13,X11))
        | ~ v1_funct_2(k10_tmap_1(sK0,X12,sK2,sK3,X13,X11),u1_struct_0(sK0),u1_struct_0(X12))
        | ~ v5_pre_topc(k10_tmap_1(sK0,X12,sK2,sK3,X13,X11),sK0,X12)
        | v2_struct_0(sK0) )
    | ~ spl6_60 ),
    inference(resolution,[],[f470,f61])).

fof(f579,plain,
    ( spl6_3
    | ~ spl6_1
    | ~ spl6_2
    | spl6_74
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f569,f469,f577,f95,f90,f100])).

fof(f577,plain,
    ( spl6_74
  <=> ! [X9,X7,X8,X10,X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X7))))
        | ~ v5_pre_topc(k10_tmap_1(sK0,X7,sK2,sK3,X8,X6),sK0,X7)
        | ~ v1_funct_2(k10_tmap_1(sK0,X7,sK2,sK3,X8,X6),u1_struct_0(sK0),u1_struct_0(X7))
        | ~ v1_funct_1(k10_tmap_1(sK0,X7,sK2,sK3,X8,X6))
        | v1_funct_1(k2_tmap_1(sK0,X7,k10_tmap_1(sK0,X7,sK2,sK3,X8,X6),X10))
        | v2_struct_0(X9)
        | ~ r4_tsep_1(sK0,X9,X10)
        | sK0 != k1_tsep_1(sK0,X9,X10)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,sK0)
        | ~ m1_pre_topc(X9,sK0)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X7))))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f569,plain,
    ( ! [X6,X10,X8,X7,X9] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X7))))
        | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X7))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X7))))
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X7))
        | ~ v1_funct_1(X8)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,sK0)
        | sK0 != k1_tsep_1(sK0,X9,X10)
        | ~ r4_tsep_1(sK0,X9,X10)
        | v1_funct_1(k2_tmap_1(sK0,X7,k10_tmap_1(sK0,X7,sK2,sK3,X8,X6),X10))
        | ~ v1_funct_1(k10_tmap_1(sK0,X7,sK2,sK3,X8,X6))
        | ~ v1_funct_2(k10_tmap_1(sK0,X7,sK2,sK3,X8,X6),u1_struct_0(sK0),u1_struct_0(X7))
        | ~ v5_pre_topc(k10_tmap_1(sK0,X7,sK2,sK3,X8,X6),sK0,X7)
        | v2_struct_0(sK0) )
    | ~ spl6_60 ),
    inference(duplicate_literal_removal,[],[f560])).

fof(f560,plain,
    ( ! [X6,X10,X8,X7,X9] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X7))))
        | ~ v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X7))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X7))))
        | ~ v1_funct_2(X8,u1_struct_0(sK2),u1_struct_0(X7))
        | ~ v1_funct_1(X8)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,sK0)
        | sK0 != k1_tsep_1(sK0,X9,X10)
        | ~ r4_tsep_1(sK0,X9,X10)
        | v1_funct_1(k2_tmap_1(sK0,X7,k10_tmap_1(sK0,X7,sK2,sK3,X8,X6),X10))
        | ~ v1_funct_1(k10_tmap_1(sK0,X7,sK2,sK3,X8,X6))
        | ~ v1_funct_2(k10_tmap_1(sK0,X7,sK2,sK3,X8,X6),u1_struct_0(sK0),u1_struct_0(X7))
        | ~ v5_pre_topc(k10_tmap_1(sK0,X7,sK2,sK3,X8,X6),sK0,X7)
        | v2_struct_0(sK0) )
    | ~ spl6_60 ),
    inference(resolution,[],[f470,f65])).

fof(f575,plain,
    ( spl6_3
    | spl6_73
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f570,f469,f573,f100])).

fof(f573,plain,
    ( spl6_73
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | v1_funct_1(k10_tmap_1(X3,X1,X4,sK0,X5,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0)))
        | v2_struct_0(X3)
        | ~ v1_funct_2(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v1_funct_1(X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | ~ v2_pre_topc(X3)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
        | ~ m1_pre_topc(sK0,X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f570,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X3)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v1_funct_1(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0))
        | ~ v1_funct_2(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),u1_struct_0(sK0),u1_struct_0(X1))
        | v2_struct_0(X3)
        | v1_funct_1(k10_tmap_1(X3,X1,X4,sK0,X5,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0))) )
    | ~ spl6_60 ),
    inference(duplicate_literal_removal,[],[f559])).

fof(f559,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,X3)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v1_funct_1(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0))
        | ~ v1_funct_2(k10_tmap_1(sK0,X1,sK2,sK3,X2,X0),u1_struct_0(sK0),u1_struct_0(X1))
        | v2_struct_0(X3)
        | v1_funct_1(k10_tmap_1(X3,X1,X4,sK0,X5,k10_tmap_1(sK0,X1,sK2,sK3,X2,X0))) )
    | ~ spl6_60 ),
    inference(resolution,[],[f470,f72])).

fof(f571,plain,
    ( spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_15
    | ~ spl6_14
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_21
    | ~ spl6_19
    | spl6_23
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f558,f469,f200,f180,f190,f195,f145,f155,f160,f105,f110,f115])).

fof(f558,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl6_23
    | ~ spl6_60 ),
    inference(resolution,[],[f470,f202])).

fof(f202,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f200])).

fof(f549,plain,
    ( spl6_3
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_7
    | ~ spl6_1
    | spl6_26
    | ~ spl6_67 ),
    inference(avatar_split_clause,[],[f548,f523,f212,f90,f120,f135,f95,f100])).

fof(f523,plain,
    ( spl6_67
  <=> ! [X0] :
        ( v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f548,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_26
    | ~ spl6_67 ),
    inference(resolution,[],[f524,f214])).

fof(f214,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f212])).

fof(f524,plain,
    ( ! [X0] :
        ( v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f523])).

fof(f545,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_72
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f517,f393,f543,f115,f110,f105])).

fof(f543,plain,
    ( spl6_72
  <=> ! [X16,X18,X20,X17,X19,X21] :
        ( v1_funct_1(k10_tmap_1(X16,sK1,k1_tsep_1(X17,X18,X19),sK3,k10_tmap_1(X17,sK1,X18,X19,X20,X21),sK5))
        | v2_struct_0(X17)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK1))))
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(sK1))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(sK1))))
        | ~ v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(sK1))
        | ~ v1_funct_1(X20)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(k1_tsep_1(X17,X18,X19),X16)
        | v2_struct_0(k1_tsep_1(X17,X18,X19))
        | ~ m1_pre_topc(sK3,X16)
        | ~ v1_funct_2(k10_tmap_1(X17,sK1,X18,X19,X20,X21),u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(sK1))
        | ~ v1_funct_1(k10_tmap_1(X17,sK1,X18,X19,X20,X21))
        | ~ v2_pre_topc(X16)
        | v2_struct_0(X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f517,plain,
    ( ! [X21,X19,X17,X20,X18,X16] :
        ( v1_funct_1(k10_tmap_1(X16,sK1,k1_tsep_1(X17,X18,X19),sK3,k10_tmap_1(X17,sK1,X18,X19,X20,X21),sK5))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ v1_funct_1(k10_tmap_1(X17,sK1,X18,X19,X20,X21))
        | ~ v1_funct_2(k10_tmap_1(X17,sK1,X18,X19,X20,X21),u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X16)
        | v2_struct_0(k1_tsep_1(X17,X18,X19))
        | ~ m1_pre_topc(k1_tsep_1(X17,X18,X19),X16)
        | ~ l1_pre_topc(X16)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(sK1))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(sK1))))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(sK1))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK1))))
        | v2_struct_0(X17) )
    | ~ spl6_52 ),
    inference(resolution,[],[f394,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
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
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f541,plain,
    ( ~ spl6_41
    | spl6_71
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f516,f393,f539,f306])).

fof(f539,plain,
    ( spl6_71
  <=> ! [X13,X15,X12,X14] :
        ( v1_funct_1(k10_tmap_1(X12,sK1,X13,sK3,k2_tmap_1(X14,sK1,X15,X13),sK5))
        | ~ l1_struct_0(X14)
        | ~ l1_struct_0(X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK1))))
        | ~ v1_funct_2(X15,u1_struct_0(X14),u1_struct_0(sK1))
        | ~ v1_funct_1(X15)
        | ~ l1_pre_topc(X12)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(sK3,X12)
        | ~ v1_funct_2(k2_tmap_1(X14,sK1,X15,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X14,sK1,X15,X13))
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f516,plain,
    ( ! [X14,X12,X15,X13] :
        ( v1_funct_1(k10_tmap_1(X12,sK1,X13,sK3,k2_tmap_1(X14,sK1,X15,X13),sK5))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ v1_funct_1(k2_tmap_1(X14,sK1,X15,X13))
        | ~ v1_funct_2(k2_tmap_1(X14,sK1,X15,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12)
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X14),u1_struct_0(sK1))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK1))))
        | ~ l1_struct_0(X13)
        | ~ l1_struct_0(X14) )
    | ~ spl6_52 ),
    inference(resolution,[],[f394,f79])).

fof(f537,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_70
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f519,f393,f535,f115,f110,f105])).

fof(f535,plain,
    ( spl6_70
  <=> ! [X9,X11,X7,X8,X10] :
        ( v1_funct_1(k10_tmap_1(X7,sK1,X8,sK3,k2_tmap_1(X9,sK1,X10,X8),sK5))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X10,X9,sK1)
        | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(sK1))
        | ~ v1_funct_1(X10)
        | v2_struct_0(X9)
        | ~ r4_tsep_1(X9,X8,X11)
        | k1_tsep_1(X9,X8,X11) != X9
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9)
        | ~ m1_pre_topc(X8,X9)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(X8,X7)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(sK3,X7)
        | ~ v1_funct_2(k2_tmap_1(X9,sK1,X10,X8),u1_struct_0(X8),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X9,sK1,X10,X8))
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f519,plain,
    ( ! [X10,X8,X7,X11,X9] :
        ( v1_funct_1(k10_tmap_1(X7,sK1,X8,sK3,k2_tmap_1(X9,sK1,X10,X8),sK5))
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ v1_funct_1(k2_tmap_1(X9,sK1,X10,X8))
        | ~ v1_funct_2(k2_tmap_1(X9,sK1,X10,X8),u1_struct_0(X8),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X7)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X8,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9)
        | k1_tsep_1(X9,X8,X11) != X9
        | ~ r4_tsep_1(X9,X8,X11)
        | v2_struct_0(X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(sK1))
        | ~ v5_pre_topc(X10,X9,sK1)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1)))) )
    | ~ spl6_52 ),
    inference(duplicate_literal_removal,[],[f515])).

fof(f515,plain,
    ( ! [X10,X8,X7,X11,X9] :
        ( v1_funct_1(k10_tmap_1(X7,sK1,X8,sK3,k2_tmap_1(X9,sK1,X10,X8),sK5))
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ v1_funct_1(k2_tmap_1(X9,sK1,X10,X8))
        | ~ v1_funct_2(k2_tmap_1(X9,sK1,X10,X8),u1_struct_0(X8),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X7)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9)
        | k1_tsep_1(X9,X8,X11) != X9
        | ~ r4_tsep_1(X9,X8,X11)
        | v2_struct_0(X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(sK1))
        | ~ v5_pre_topc(X10,X9,sK1)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1)))) )
    | ~ spl6_52 ),
    inference(resolution,[],[f394,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f533,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_69
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f520,f393,f531,f115,f110,f105])).

fof(f531,plain,
    ( spl6_69
  <=> ! [X3,X5,X2,X4,X6] :
        ( v1_funct_1(k10_tmap_1(X2,sK1,X3,sK3,k2_tmap_1(X4,sK1,X5,X3),sK5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X5,X4,sK1)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(X5)
        | v2_struct_0(X4)
        | ~ r4_tsep_1(X4,X6,X3)
        | k1_tsep_1(X4,X6,X3) != X4
        | ~ m1_pre_topc(X3,X4)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X4)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK3,X2)
        | ~ v1_funct_2(k2_tmap_1(X4,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X4,sK1,X5,X3))
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f520,plain,
    ( ! [X6,X4,X2,X5,X3] :
        ( v1_funct_1(k10_tmap_1(X2,sK1,X3,sK3,k2_tmap_1(X4,sK1,X5,X3),sK5))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ v1_funct_1(k2_tmap_1(X4,sK1,X5,X3))
        | ~ v1_funct_2(k2_tmap_1(X4,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X4)
        | ~ m1_pre_topc(X3,X4)
        | k1_tsep_1(X4,X6,X3) != X4
        | ~ r4_tsep_1(X4,X6,X3)
        | v2_struct_0(X4)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v5_pre_topc(X5,X4,sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) )
    | ~ spl6_52 ),
    inference(duplicate_literal_removal,[],[f514])).

fof(f514,plain,
    ( ! [X6,X4,X2,X5,X3] :
        ( v1_funct_1(k10_tmap_1(X2,sK1,X3,sK3,k2_tmap_1(X4,sK1,X5,X3),sK5))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ v1_funct_1(k2_tmap_1(X4,sK1,X5,X3))
        | ~ v1_funct_2(k2_tmap_1(X4,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X4)
        | k1_tsep_1(X4,X6,X3) != X4
        | ~ r4_tsep_1(X4,X6,X3)
        | v2_struct_0(X4)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v5_pre_topc(X5,X4,sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) )
    | ~ spl6_52 ),
    inference(resolution,[],[f394,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f529,plain,
    ( spl6_11
    | ~ spl6_21
    | ~ spl6_22
    | spl6_68
    | ~ spl6_19
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f521,f393,f180,f527,f195,f190,f140])).

fof(f527,plain,
    ( spl6_68
  <=> ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK1,sK3,sK3,sK5,sK5))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f521,plain,
    ( ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK1,sK3,sK3,sK5,sK5))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1) )
    | ~ spl6_19
    | ~ spl6_52 ),
    inference(duplicate_literal_removal,[],[f513])).

fof(f513,plain,
    ( ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK1,sK3,sK3,sK5,sK5))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl6_19
    | ~ spl6_52 ),
    inference(resolution,[],[f394,f182])).

fof(f182,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f180])).

fof(f525,plain,
    ( spl6_8
    | ~ spl6_14
    | ~ spl6_15
    | spl6_67
    | ~ spl6_12
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f512,f393,f145,f523,f160,f155,f125])).

fof(f512,plain,
    ( ! [X0] :
        ( v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_12
    | ~ spl6_52 ),
    inference(resolution,[],[f394,f147])).

fof(f147,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f145])).

fof(f505,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_66
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f477,f389,f503,f115,f110,f105])).

fof(f503,plain,
    ( spl6_66
  <=> ! [X16,X18,X20,X17,X19,X21] :
        ( v1_funct_1(k10_tmap_1(X16,sK1,k1_tsep_1(X17,X18,X19),sK2,k10_tmap_1(X17,sK1,X18,X19,X20,X21),sK4))
        | v2_struct_0(X17)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK1))))
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(sK1))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(sK1))))
        | ~ v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(sK1))
        | ~ v1_funct_1(X20)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(k1_tsep_1(X17,X18,X19),X16)
        | v2_struct_0(k1_tsep_1(X17,X18,X19))
        | ~ m1_pre_topc(sK2,X16)
        | ~ v1_funct_2(k10_tmap_1(X17,sK1,X18,X19,X20,X21),u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(sK1))
        | ~ v1_funct_1(k10_tmap_1(X17,sK1,X18,X19,X20,X21))
        | ~ v2_pre_topc(X16)
        | v2_struct_0(X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f477,plain,
    ( ! [X21,X19,X17,X20,X18,X16] :
        ( v1_funct_1(k10_tmap_1(X16,sK1,k1_tsep_1(X17,X18,X19),sK2,k10_tmap_1(X17,sK1,X18,X19,X20,X21),sK4))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ v1_funct_1(k10_tmap_1(X17,sK1,X18,X19,X20,X21))
        | ~ v1_funct_2(k10_tmap_1(X17,sK1,X18,X19,X20,X21),u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X16)
        | v2_struct_0(k1_tsep_1(X17,X18,X19))
        | ~ m1_pre_topc(k1_tsep_1(X17,X18,X19),X16)
        | ~ l1_pre_topc(X16)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(sK1))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(sK1))))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(sK1))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK1))))
        | v2_struct_0(X17) )
    | ~ spl6_51 ),
    inference(resolution,[],[f390,f74])).

fof(f501,plain,
    ( ~ spl6_41
    | spl6_65
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f476,f389,f499,f306])).

fof(f499,plain,
    ( spl6_65
  <=> ! [X13,X15,X12,X14] :
        ( v1_funct_1(k10_tmap_1(X12,sK1,X13,sK2,k2_tmap_1(X14,sK1,X15,X13),sK4))
        | ~ l1_struct_0(X14)
        | ~ l1_struct_0(X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK1))))
        | ~ v1_funct_2(X15,u1_struct_0(X14),u1_struct_0(sK1))
        | ~ v1_funct_1(X15)
        | ~ l1_pre_topc(X12)
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(sK2,X12)
        | ~ v1_funct_2(k2_tmap_1(X14,sK1,X15,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X14,sK1,X15,X13))
        | ~ v2_pre_topc(X12)
        | v2_struct_0(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f476,plain,
    ( ! [X14,X12,X15,X13] :
        ( v1_funct_1(k10_tmap_1(X12,sK1,X13,sK2,k2_tmap_1(X14,sK1,X15,X13),sK4))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ v1_funct_1(k2_tmap_1(X14,sK1,X15,X13))
        | ~ v1_funct_2(k2_tmap_1(X14,sK1,X15,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X12)
        | ~ l1_pre_topc(X12)
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X14),u1_struct_0(sK1))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK1))))
        | ~ l1_struct_0(X13)
        | ~ l1_struct_0(X14) )
    | ~ spl6_51 ),
    inference(resolution,[],[f390,f79])).

fof(f497,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_64
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f479,f389,f495,f115,f110,f105])).

fof(f495,plain,
    ( spl6_64
  <=> ! [X9,X11,X7,X8,X10] :
        ( v1_funct_1(k10_tmap_1(X7,sK1,X8,sK2,k2_tmap_1(X9,sK1,X10,X8),sK4))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X10,X9,sK1)
        | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(sK1))
        | ~ v1_funct_1(X10)
        | v2_struct_0(X9)
        | ~ r4_tsep_1(X9,X8,X11)
        | k1_tsep_1(X9,X8,X11) != X9
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9)
        | ~ m1_pre_topc(X8,X9)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(X8,X7)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(sK2,X7)
        | ~ v1_funct_2(k2_tmap_1(X9,sK1,X10,X8),u1_struct_0(X8),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X9,sK1,X10,X8))
        | ~ v2_pre_topc(X7)
        | v2_struct_0(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f479,plain,
    ( ! [X10,X8,X7,X11,X9] :
        ( v1_funct_1(k10_tmap_1(X7,sK1,X8,sK2,k2_tmap_1(X9,sK1,X10,X8),sK4))
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ v1_funct_1(k2_tmap_1(X9,sK1,X10,X8))
        | ~ v1_funct_2(k2_tmap_1(X9,sK1,X10,X8),u1_struct_0(X8),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X7)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X8,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9)
        | k1_tsep_1(X9,X8,X11) != X9
        | ~ r4_tsep_1(X9,X8,X11)
        | v2_struct_0(X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(sK1))
        | ~ v5_pre_topc(X10,X9,sK1)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1)))) )
    | ~ spl6_51 ),
    inference(duplicate_literal_removal,[],[f475])).

fof(f475,plain,
    ( ! [X10,X8,X7,X11,X9] :
        ( v1_funct_1(k10_tmap_1(X7,sK1,X8,sK2,k2_tmap_1(X9,sK1,X10,X8),sK4))
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ v1_funct_1(k2_tmap_1(X9,sK1,X10,X8))
        | ~ v1_funct_2(k2_tmap_1(X9,sK1,X10,X8),u1_struct_0(X8),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X7)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9)
        | k1_tsep_1(X9,X8,X11) != X9
        | ~ r4_tsep_1(X9,X8,X11)
        | v2_struct_0(X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(sK1))
        | ~ v5_pre_topc(X10,X9,sK1)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1)))) )
    | ~ spl6_51 ),
    inference(resolution,[],[f390,f64])).

fof(f493,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_63
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f480,f389,f491,f115,f110,f105])).

fof(f491,plain,
    ( spl6_63
  <=> ! [X3,X5,X2,X4,X6] :
        ( v1_funct_1(k10_tmap_1(X2,sK1,X3,sK2,k2_tmap_1(X4,sK1,X5,X3),sK4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X5,X4,sK1)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(X5)
        | v2_struct_0(X4)
        | ~ r4_tsep_1(X4,X6,X3)
        | k1_tsep_1(X4,X6,X3) != X4
        | ~ m1_pre_topc(X3,X4)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X4)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK2,X2)
        | ~ v1_funct_2(k2_tmap_1(X4,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X4,sK1,X5,X3))
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f480,plain,
    ( ! [X6,X4,X2,X5,X3] :
        ( v1_funct_1(k10_tmap_1(X2,sK1,X3,sK2,k2_tmap_1(X4,sK1,X5,X3),sK4))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ v1_funct_1(k2_tmap_1(X4,sK1,X5,X3))
        | ~ v1_funct_2(k2_tmap_1(X4,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X4)
        | ~ m1_pre_topc(X3,X4)
        | k1_tsep_1(X4,X6,X3) != X4
        | ~ r4_tsep_1(X4,X6,X3)
        | v2_struct_0(X4)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v5_pre_topc(X5,X4,sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) )
    | ~ spl6_51 ),
    inference(duplicate_literal_removal,[],[f474])).

fof(f474,plain,
    ( ! [X6,X4,X2,X5,X3] :
        ( v1_funct_1(k10_tmap_1(X2,sK1,X3,sK2,k2_tmap_1(X4,sK1,X5,X3),sK4))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ v1_funct_1(k2_tmap_1(X4,sK1,X5,X3))
        | ~ v1_funct_2(k2_tmap_1(X4,sK1,X5,X3),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X4)
        | k1_tsep_1(X4,X6,X3) != X4
        | ~ r4_tsep_1(X4,X6,X3)
        | v2_struct_0(X4)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v5_pre_topc(X5,X4,sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) )
    | ~ spl6_51 ),
    inference(resolution,[],[f390,f68])).

fof(f489,plain,
    ( spl6_11
    | ~ spl6_21
    | ~ spl6_22
    | spl6_62
    | ~ spl6_19
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f473,f389,f180,f487,f195,f190,f140])).

fof(f487,plain,
    ( spl6_62
  <=> ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK1,sK3,sK2,sK5,sK4))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f473,plain,
    ( ! [X1] :
        ( v1_funct_1(k10_tmap_1(X1,sK1,sK3,sK2,sK5,sK4))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl6_19
    | ~ spl6_51 ),
    inference(resolution,[],[f390,f182])).

fof(f485,plain,
    ( spl6_8
    | ~ spl6_14
    | ~ spl6_15
    | spl6_61
    | ~ spl6_12
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f481,f389,f145,f483,f160,f155,f125])).

fof(f483,plain,
    ( spl6_61
  <=> ! [X0] :
        ( v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK2,sK4,sK4))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f481,plain,
    ( ! [X0] :
        ( v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK2,sK4,sK4))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_12
    | ~ spl6_51 ),
    inference(duplicate_literal_removal,[],[f472])).

fof(f472,plain,
    ( ! [X0] :
        ( v1_funct_1(k10_tmap_1(X0,sK1,sK2,sK2,sK4,sK4))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_12
    | ~ spl6_51 ),
    inference(resolution,[],[f390,f147])).

fof(f471,plain,
    ( spl6_3
    | ~ spl6_10
    | spl6_11
    | ~ spl6_7
    | spl6_8
    | ~ spl6_1
    | ~ spl6_2
    | spl6_60
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f464,f130,f469,f95,f90,f125,f120,f140,f135,f100])).

fof(f464,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | v2_struct_0(sK0) )
    | ~ spl6_9 ),
    inference(superposition,[],[f74,f132])).

fof(f456,plain,
    ( spl6_3
    | ~ spl6_10
    | spl6_11
    | ~ spl6_7
    | spl6_8
    | ~ spl6_1
    | ~ spl6_2
    | spl6_59
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f452,f130,f454,f95,f90,f125,f120,f140,f135,f100])).

fof(f452,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | v2_struct_0(sK0) )
    | ~ spl6_9 ),
    inference(superposition,[],[f73,f132])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f451,plain,
    ( ~ spl6_43
    | ~ spl6_41
    | spl6_58
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f438,f328,f449,f306,f314])).

fof(f438,plain,
    ( ! [X6,X7] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(X6,sK1,X7,sK3),sK5)
        | sK5 = k2_tmap_1(X6,sK1,X7,sK3)
        | ~ v1_funct_1(k2_tmap_1(X6,sK1,X7,sK3))
        | ~ v1_funct_2(k2_tmap_1(X6,sK1,X7,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
        | ~ l1_struct_0(sK3)
        | ~ l1_struct_0(X6) )
    | ~ spl6_45 ),
    inference(resolution,[],[f329,f79])).

fof(f447,plain,
    ( spl6_11
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_57
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f437,f328,f445,f115,f110,f105,f140])).

fof(f445,plain,
    ( spl6_57
  <=> ! [X3,X5,X4] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK3),sK5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X4,X3,sK1)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | v2_struct_0(X3)
        | ~ r4_tsep_1(X3,sK3,X5)
        | k1_tsep_1(X3,sK3,X5) != X3
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK3))
        | sK5 = k2_tmap_1(X3,sK1,X4,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f437,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK3),sK5)
        | sK5 = k2_tmap_1(X3,sK1,X4,sK3)
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK3))
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X3)
        | k1_tsep_1(X3,sK3,X5) != X3
        | ~ r4_tsep_1(X3,sK3,X5)
        | v2_struct_0(X3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v5_pre_topc(X4,X3,sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) )
    | ~ spl6_45 ),
    inference(resolution,[],[f329,f64])).

fof(f443,plain,
    ( spl6_11
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_56
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f436,f328,f441,f115,f110,f105,f140])).

fof(f441,plain,
    ( spl6_56
  <=> ! [X1,X0,X2] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X1,sK3),sK5)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X1,X0,sK1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | v2_struct_0(X0)
        | ~ r4_tsep_1(X0,X2,sK3)
        | k1_tsep_1(X0,X2,sK3) != X0
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,sK3))
        | sK5 = k2_tmap_1(X0,sK1,X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f436,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X1,sK3),sK5)
        | sK5 = k2_tmap_1(X0,sK1,X1,sK3)
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,sK3))
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X0)
        | k1_tsep_1(X0,X2,sK3) != X0
        | ~ r4_tsep_1(X0,X2,sK3)
        | v2_struct_0(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) )
    | ~ spl6_45 ),
    inference(resolution,[],[f329,f68])).

fof(f434,plain,
    ( spl6_8
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_55
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f424,f324,f432,f115,f110,f105,f125])).

fof(f432,plain,
    ( spl6_55
  <=> ! [X29,X28,X30] :
        ( ~ v2_pre_topc(X28)
        | ~ v1_funct_2(k2_tmap_1(X28,sK1,X30,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X28,sK1,X30,sK2))
        | sK4 = k2_tmap_1(X28,sK1,X30,sK2)
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X28,sK1,X30,sK2),sK4)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X30,X28,sK1)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(sK1))
        | v2_struct_0(X28)
        | ~ r4_tsep_1(X28,X29,sK2)
        | k1_tsep_1(X28,X29,sK2) != X28
        | ~ m1_pre_topc(sK2,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X28) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f424,plain,
    ( ! [X30,X28,X29] :
        ( ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X28)
        | k1_tsep_1(X28,X29,sK2) != X28
        | ~ r4_tsep_1(X28,X29,sK2)
        | v2_struct_0(X28)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(sK1))
        | ~ v5_pre_topc(X30,X28,sK1)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(sK1))))
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X28,sK1,X30,sK2),sK4)
        | sK4 = k2_tmap_1(X28,sK1,X30,sK2)
        | ~ v1_funct_1(k2_tmap_1(X28,sK1,X30,sK2))
        | ~ v1_funct_2(k2_tmap_1(X28,sK1,X30,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl6_44 ),
    inference(resolution,[],[f68,f325])).

fof(f419,plain,
    ( ~ spl6_40
    | ~ spl6_41
    | spl6_54
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f410,f324,f417,f306,f302])).

fof(f410,plain,
    ( ! [X4,X3] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK2),sK4)
        | sK4 = k2_tmap_1(X3,sK1,X4,sK2)
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK2))
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ l1_struct_0(sK2)
        | ~ l1_struct_0(X3) )
    | ~ spl6_44 ),
    inference(resolution,[],[f325,f79])).

fof(f415,plain,
    ( spl6_8
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_53
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f409,f324,f413,f115,f110,f105,f125])).

fof(f413,plain,
    ( spl6_53
  <=> ! [X1,X0,X2] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X1,sK2),sK4)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X1,X0,sK1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | v2_struct_0(X0)
        | ~ r4_tsep_1(X0,sK2,X2)
        | k1_tsep_1(X0,sK2,X2) != X0
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,sK2))
        | sK4 = k2_tmap_1(X0,sK1,X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f409,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X1,sK2),sK4)
        | sK4 = k2_tmap_1(X0,sK1,X1,sK2)
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,sK2))
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | k1_tsep_1(X0,sK2,X2) != X0
        | ~ r4_tsep_1(X0,sK2,X2)
        | v2_struct_0(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) )
    | ~ spl6_44 ),
    inference(resolution,[],[f325,f64])).

fof(f395,plain,
    ( ~ spl6_21
    | ~ spl6_22
    | spl6_11
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_52
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f385,f180,f393,f115,f110,f105,f140,f195,f190])).

fof(f385,plain,
    ( ! [X4,X5,X3] :
        ( ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X3)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(X3)
        | v1_funct_1(k10_tmap_1(X3,sK1,X4,sK3,X5,sK5)) )
    | ~ spl6_19 ),
    inference(resolution,[],[f72,f182])).

fof(f391,plain,
    ( ~ spl6_14
    | ~ spl6_15
    | spl6_8
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_51
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f384,f145,f389,f115,f110,f105,f125,f160,f155])).

fof(f384,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | v1_funct_1(k10_tmap_1(X0,sK1,X1,sK2,X2,sK4)) )
    | ~ spl6_12 ),
    inference(resolution,[],[f72,f147])).

fof(f377,plain,
    ( spl6_11
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_30
    | ~ spl6_32
    | spl6_50
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f369,f259,f375,f248,f236,f115,f110,f105,f195,f190,f180,f140])).

fof(f375,plain,
    ( spl6_50
  <=> ! [X2] :
        ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,X2))
        | ~ m1_pre_topc(X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f259,plain,
    ( spl6_34
  <=> ! [X1] : v1_funct_1(k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f369,plain,
    ( ! [X2] :
        ( v1_funct_1(k2_tmap_1(sK3,sK1,sK5,X2))
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X2,sK3)
        | v2_struct_0(sK3) )
    | ~ spl6_34 ),
    inference(superposition,[],[f260,f80])).

fof(f260,plain,
    ( ! [X1] : v1_funct_1(k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,X1))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f259])).

fof(f373,plain,
    ( ~ spl6_19
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_49
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f368,f259,f371,f115,f110,f105,f195,f190,f180])).

fof(f371,plain,
    ( spl6_49
  <=> ! [X1,X0] :
        ( v1_funct_1(k3_tmap_1(X1,sK1,sK3,X0,sK5))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f368,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X1,sK1,sK3,X0,sK5))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X0,X1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X1) )
    | ~ spl6_34 ),
    inference(superposition,[],[f260,f71])).

fof(f367,plain,
    ( spl6_11
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_22
    | spl6_48
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f361,f180,f248,f236,f115,f110,f105,f365,f195,f190,f185,f140])).

fof(f365,plain,
    ( spl6_48
  <=> ! [X3,X2] :
        ( v2_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,X2))
        | ~ r4_tsep_1(sK3,X2,X3)
        | sK3 != k1_tsep_1(sK3,X2,X3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f361,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK3)
        | sK3 != k1_tsep_1(sK3,X2,X3)
        | ~ r4_tsep_1(sK3,X2,X3)
        | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,X2))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK5,sK3,sK1)
        | v2_struct_0(sK3) )
    | ~ spl6_19 ),
    inference(resolution,[],[f61,f182])).

fof(f359,plain,
    ( ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | spl6_47
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f349,f255,f357,f115,f110,f105,f160,f155,f145])).

fof(f357,plain,
    ( spl6_47
  <=> ! [X1,X0] :
        ( v1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f255,plain,
    ( spl6_33
  <=> ! [X0] : v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f349,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK4))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,X1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X1) )
    | ~ spl6_33 ),
    inference(superposition,[],[f256,f71])).

fof(f256,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f255])).

fof(f346,plain,
    ( ~ spl6_30
    | spl6_43 ),
    inference(avatar_split_clause,[],[f345,f314,f236])).

fof(f345,plain,
    ( ~ l1_pre_topc(sK3)
    | spl6_43 ),
    inference(resolution,[],[f316,f86])).

fof(f316,plain,
    ( ~ l1_struct_0(sK3)
    | spl6_43 ),
    inference(avatar_component_clause,[],[f314])).

fof(f344,plain,
    ( spl6_8
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_29
    | ~ spl6_31
    | spl6_46
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f338,f255,f342,f243,f231,f115,f110,f105,f160,f155,f145,f125])).

fof(f342,plain,
    ( spl6_46
  <=> ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,X0))
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f338,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK2,sK1,sK4,X0))
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(sK2) )
    | ~ spl6_33 ),
    inference(superposition,[],[f256,f80])).

fof(f332,plain,
    ( ~ spl6_29
    | spl6_40 ),
    inference(avatar_split_clause,[],[f331,f302,f231])).

fof(f331,plain,
    ( ~ l1_pre_topc(sK2)
    | spl6_40 ),
    inference(resolution,[],[f304,f86])).

fof(f304,plain,
    ( ~ l1_struct_0(sK2)
    | spl6_40 ),
    inference(avatar_component_clause,[],[f302])).

fof(f330,plain,
    ( ~ spl6_21
    | ~ spl6_22
    | spl6_45
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f321,f180,f328,f195,f190])).

fof(f321,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | sK5 = X1
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X1,sK5) )
    | ~ spl6_19 ),
    inference(resolution,[],[f70,f182])).

fof(f326,plain,
    ( ~ spl6_14
    | ~ spl6_15
    | spl6_44
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f320,f145,f324,f160,f155])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | sK4 = X0
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0,sK4) )
    | ~ spl6_12 ),
    inference(resolution,[],[f70,f147])).

fof(f319,plain,
    ( ~ spl6_4
    | spl6_41 ),
    inference(avatar_split_clause,[],[f318,f306,f105])).

fof(f318,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_41 ),
    inference(resolution,[],[f308,f86])).

fof(f308,plain,
    ( ~ l1_struct_0(sK1)
    | spl6_41 ),
    inference(avatar_component_clause,[],[f306])).

fof(f317,plain,
    ( spl6_42
    | ~ spl6_43
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_41
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f296,f180,f306,f195,f190,f314,f311])).

fof(f311,plain,
    ( spl6_42
  <=> ! [X1] :
        ( ~ l1_struct_0(X1)
        | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f296,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ l1_struct_0(sK3)
        | ~ l1_struct_0(X1)
        | v1_funct_1(k2_tmap_1(sK3,sK1,sK5,X1)) )
    | ~ spl6_19 ),
    inference(resolution,[],[f77,f182])).

fof(f309,plain,
    ( spl6_39
    | ~ spl6_40
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_41
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f295,f145,f306,f160,f155,f302,f299])).

fof(f299,plain,
    ( spl6_39
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ l1_struct_0(sK2)
        | ~ l1_struct_0(X0)
        | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,X0)) )
    | ~ spl6_12 ),
    inference(resolution,[],[f77,f147])).

fof(f292,plain,
    ( spl6_3
    | ~ spl6_10
    | spl6_11
    | ~ spl6_7
    | spl6_8
    | ~ spl6_1
    | spl6_38
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f285,f130,f289,f90,f125,f120,f140,f135,f100])).

fof(f285,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9 ),
    inference(superposition,[],[f83,f132])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f282,plain,
    ( spl6_3
    | ~ spl6_10
    | spl6_11
    | ~ spl6_7
    | spl6_8
    | ~ spl6_1
    | spl6_37
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f277,f130,f279,f90,f125,f120,f140,f135,f100])).

fof(f279,plain,
    ( spl6_37
  <=> v1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f277,plain,
    ( v1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_9 ),
    inference(superposition,[],[f82,f132])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f273,plain,
    ( spl6_36
    | ~ spl6_22
    | ~ spl6_21
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f263,f180,f190,f195,f270])).

fof(f270,plain,
    ( spl6_36
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f263,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK5,sK5)
    | ~ spl6_19 ),
    inference(resolution,[],[f88,f182])).

fof(f268,plain,
    ( spl6_35
    | ~ spl6_15
    | ~ spl6_14
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f262,f145,f155,f160,f265])).

fof(f265,plain,
    ( spl6_35
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f262,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK4)
    | ~ spl6_12 ),
    inference(resolution,[],[f88,f147])).

fof(f261,plain,
    ( spl6_34
    | ~ spl6_22
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f253,f180,f195,f259])).

fof(f253,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | v1_funct_1(k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK5,X1)) )
    | ~ spl6_19 ),
    inference(resolution,[],[f75,f182])).

fof(f257,plain,
    ( spl6_33
    | ~ spl6_15
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f252,f145,f160,f255])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0)) )
    | ~ spl6_12 ),
    inference(resolution,[],[f75,f147])).

fof(f251,plain,
    ( spl6_32
    | ~ spl6_2
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f241,f135,f90,f95,f248])).

fof(f241,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f84,f137])).

fof(f137,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
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

fof(f246,plain,
    ( spl6_31
    | ~ spl6_2
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f240,f120,f90,f95,f243])).

fof(f240,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f84,f122])).

fof(f122,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f239,plain,
    ( spl6_30
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f229,f135,f90,f236])).

fof(f229,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3)
    | ~ spl6_10 ),
    inference(resolution,[],[f85,f137])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f234,plain,
    ( spl6_29
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f228,f120,f90,f231])).

fof(f228,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f85,f122])).

fof(f227,plain,
    ( spl6_28
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f217,f175,f130,f224])).

fof(f175,plain,
    ( spl6_18
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f217,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f177,f132])).

fof(f177,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f222,plain,
    ( spl6_27
    | ~ spl6_9
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f216,f170,f130,f219])).

fof(f170,plain,
    ( spl6_17
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f216,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl6_9
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f172,f132])).

fof(f172,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f215,plain,
    ( ~ spl6_23
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f37,f212,f208,f204,f200])).

fof(f37,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
                                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
                                & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_tmap_1)).

fof(f198,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f38,f195])).

fof(f38,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f16])).

fof(f193,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f39,f190])).

fof(f39,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f188,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f40,f185])).

fof(f40,plain,(
    v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f183,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f41,f180])).

fof(f41,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f178,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f42,f175])).

fof(f42,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f173,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f43,f170])).

fof(f43,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(cnf_transformation,[],[f16])).

fof(f168,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f44,f165])).

fof(f44,plain,(
    r4_tsep_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f163,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f45,f160])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f158,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f46,f155])).

fof(f46,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f153,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f47,f150])).

fof(f47,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f148,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f48,f145])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f143,plain,(
    ~ spl6_11 ),
    inference(avatar_split_clause,[],[f49,f140])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f138,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f50,f135])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f133,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f51,f130])).

fof(f51,plain,(
    sK0 = k1_tsep_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f128,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f52,f125])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f123,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f53,f120])).

fof(f53,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f118,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f54,f115])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f113,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f55,f110])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f108,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f56,f105])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f57,f100])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f98,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f58,f95])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f59,f90])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------

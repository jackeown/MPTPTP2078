%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t21_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:11 EDT 2019

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  847 (5192 expanded)
%              Number of leaves         :  237 (2833 expanded)
%              Depth                    :   10
%              Number of atoms          : 3859 (19954 expanded)
%              Number of equality atoms :  119 ( 844 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f166,f170,f174,f178,f182,f186,f190,f194,f198,f202,f206,f210,f214,f220,f224,f229,f243,f244,f248,f249,f253,f254,f258,f262,f284,f288,f289,f293,f297,f301,f302,f306,f310,f314,f315,f319,f323,f324,f328,f332,f337,f342,f349,f353,f357,f363,f367,f372,f380,f384,f388,f392,f402,f406,f410,f414,f418,f424,f428,f434,f438,f468,f472,f476,f480,f484,f485,f489,f493,f497,f501,f505,f506,f510,f514,f518,f522,f526,f527,f531,f535,f536,f537,f541,f545,f583,f587,f591,f595,f599,f603,f604,f608,f612,f616,f620,f624,f628,f632,f633,f637,f641,f645,f649,f653,f657,f661,f662,f666,f670,f674,f678,f679,f680,f681,f685,f689,f735,f739,f743,f747,f751,f755,f759,f763,f764,f768,f772,f776,f780,f784,f788,f792,f796,f800,f801,f805,f809,f813,f817,f821,f825,f829,f833,f837,f838,f842,f846,f850,f854,f858,f859,f860,f861,f862,f866,f870,f924,f928,f932,f936,f940,f944,f948,f952,f953,f957,f961,f965,f969,f973,f977,f981,f985,f989,f993,f997,f998,f1002,f1006,f1010,f1014,f1018,f1022,f1026,f1030,f1034,f1038,f1042,f1043,f1047,f1051,f1055,f1059,f1063,f1067,f1071,f1075,f1076,f1077,f1078,f1079,f1080,f1084,f1088,f1094,f1098,f1105,f1109,f1113,f1125,f1129,f1133,f1137,f1138,f1143,f1149,f1153,f1159,f1165,f1169,f1174,f1179,f1185,f1189,f1197,f1201,f1205,f1209,f1217,f1221,f1225,f1229,f1231,f1233,f1243,f1247,f1251,f1255,f1259,f1263])).

fof(f1263,plain,
    ( spl14_406
    | ~ spl14_342 ),
    inference(avatar_split_clause,[],[f1234,f1086,f1261])).

fof(f1261,plain,
    ( spl14_406
  <=> m1_subset_1(u1_pre_topc(k1_tsep_1(sK0,sK1,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_406])])).

fof(f1086,plain,
    ( spl14_342
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_342])])).

fof(f1234,plain,
    ( m1_subset_1(u1_pre_topc(k1_tsep_1(sK0,sK1,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))))
    | ~ spl14_342 ),
    inference(unit_resulting_resolution,[],[f1087,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',dt_u1_pre_topc)).

fof(f1087,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_342 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f1259,plain,
    ( spl14_404
    | ~ spl14_52
    | ~ spl14_342 ),
    inference(avatar_split_clause,[],[f1235,f1086,f304,f1257])).

fof(f1257,plain,
    ( spl14_404
  <=> k1_tsep_1(sK0,sK1,sK2) = g1_pre_topc(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_pre_topc(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_404])])).

fof(f304,plain,
    ( spl14_52
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_52])])).

fof(f1235,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = g1_pre_topc(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_pre_topc(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_52
    | ~ spl14_342 ),
    inference(unit_resulting_resolution,[],[f305,f1087,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',abstractness_v1_pre_topc)).

fof(f305,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_52 ),
    inference(avatar_component_clause,[],[f304])).

fof(f1255,plain,
    ( spl14_402
    | ~ spl14_342 ),
    inference(avatar_split_clause,[],[f1236,f1086,f1253])).

fof(f1253,plain,
    ( spl14_402
  <=> m1_pre_topc(sK8(k1_tsep_1(sK0,sK1,sK2)),k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_402])])).

fof(f1236,plain,
    ( m1_pre_topc(sK8(k1_tsep_1(sK0,sK1,sK2)),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_342 ),
    inference(unit_resulting_resolution,[],[f1087,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(sK8(X0),X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( m1_pre_topc(sK8(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f50,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
     => m1_pre_topc(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',existence_m1_pre_topc)).

fof(f1251,plain,
    ( spl14_366
    | spl14_59
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_86
    | ~ spl14_88
    | ~ spl14_340
    | ~ spl14_342 ),
    inference(avatar_split_clause,[],[f1237,f1086,f1082,f390,f386,f382,f370,f317,f1249])).

fof(f1249,plain,
    ( spl14_366
  <=> m1_connsp_2(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k1_tsep_1(sK0,sK1,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_366])])).

fof(f317,plain,
    ( spl14_59
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_59])])).

fof(f370,plain,
    ( spl14_80
  <=> m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_80])])).

fof(f382,plain,
    ( spl14_84
  <=> r2_hidden(sK4,sK9(sK0,sK1,sK2,sK4,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_84])])).

fof(f386,plain,
    ( spl14_86
  <=> v3_pre_topc(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_86])])).

fof(f390,plain,
    ( spl14_88
  <=> m1_subset_1(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_88])])).

fof(f1082,plain,
    ( spl14_340
  <=> v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_340])])).

fof(f1237,plain,
    ( m1_connsp_2(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k1_tsep_1(sK0,sK1,sK2),sK4)
    | ~ spl14_59
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_86
    | ~ spl14_88
    | ~ spl14_340
    | ~ spl14_342 ),
    inference(unit_resulting_resolution,[],[f318,f1083,f371,f383,f387,f391,f1087,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',t5_connsp_2)).

fof(f391,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
    | ~ spl14_88 ),
    inference(avatar_component_clause,[],[f390])).

fof(f387,plain,
    ( v3_pre_topc(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_86 ),
    inference(avatar_component_clause,[],[f386])).

fof(f383,plain,
    ( r2_hidden(sK4,sK9(sK0,sK1,sK2,sK4,sK6,sK7))
    | ~ spl14_84 ),
    inference(avatar_component_clause,[],[f382])).

fof(f371,plain,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_80 ),
    inference(avatar_component_clause,[],[f370])).

fof(f1083,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_340 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f318,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_59 ),
    inference(avatar_component_clause,[],[f317])).

fof(f1247,plain,
    ( spl14_400
    | spl14_59
    | ~ spl14_80
    | ~ spl14_340
    | ~ spl14_342 ),
    inference(avatar_split_clause,[],[f1238,f1086,f1082,f370,f317,f1245])).

fof(f1245,plain,
    ( spl14_400
  <=> m1_connsp_2(sK11(k1_tsep_1(sK0,sK1,sK2),sK4),k1_tsep_1(sK0,sK1,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_400])])).

fof(f1238,plain,
    ( m1_connsp_2(sK11(k1_tsep_1(sK0,sK1,sK2),sK4),k1_tsep_1(sK0,sK1,sK2),sK4)
    | ~ spl14_59
    | ~ spl14_80
    | ~ spl14_340
    | ~ spl14_342 ),
    inference(unit_resulting_resolution,[],[f318,f1083,f371,f1087,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(sK11(X0,X1),X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK11(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f66,f91])).

fof(f91,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK11(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',existence_m1_connsp_2)).

fof(f1243,plain,
    ( spl14_398
    | spl14_59
    | ~ spl14_340
    | ~ spl14_342 ),
    inference(avatar_split_clause,[],[f1239,f1086,f1082,f317,f1241])).

fof(f1241,plain,
    ( spl14_398
  <=> m1_connsp_2(sK11(k1_tsep_1(sK0,sK1,sK2),sK10(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),k1_tsep_1(sK0,sK1,sK2),sK10(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_398])])).

fof(f1239,plain,
    ( m1_connsp_2(sK11(k1_tsep_1(sK0,sK1,sK2),sK10(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),k1_tsep_1(sK0,sK1,sK2),sK10(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
    | ~ spl14_59
    | ~ spl14_340
    | ~ spl14_342 ),
    inference(unit_resulting_resolution,[],[f318,f1083,f125,f1087,f136])).

fof(f125,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f25,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',existence_m1_subset_1)).

fof(f1233,plain,
    ( spl14_342
    | ~ spl14_60
    | ~ spl14_262 ),
    inference(avatar_split_clause,[],[f1232,f868,f321,f1086])).

fof(f321,plain,
    ( spl14_60
  <=> k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_60])])).

fof(f868,plain,
    ( spl14_262
  <=> l1_pre_topc(k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_262])])).

fof(f1232,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_60
    | ~ spl14_262 ),
    inference(forward_demodulation,[],[f869,f322])).

fof(f322,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl14_60 ),
    inference(avatar_component_clause,[],[f321])).

fof(f869,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_262 ),
    inference(avatar_component_clause,[],[f868])).

fof(f1231,plain,
    ( spl14_340
    | ~ spl14_60
    | ~ spl14_260 ),
    inference(avatar_split_clause,[],[f1230,f864,f321,f1082])).

fof(f864,plain,
    ( spl14_260
  <=> v2_pre_topc(k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_260])])).

fof(f1230,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_60
    | ~ spl14_260 ),
    inference(forward_demodulation,[],[f865,f322])).

fof(f865,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_260 ),
    inference(avatar_component_clause,[],[f864])).

fof(f1229,plain,
    ( spl14_396
    | ~ spl14_196 ),
    inference(avatar_split_clause,[],[f1210,f687,f1227])).

fof(f1227,plain,
    ( spl14_396
  <=> m1_subset_1(u1_pre_topc(k1_tsep_1(sK0,sK1,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_396])])).

fof(f687,plain,
    ( spl14_196
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_196])])).

fof(f1210,plain,
    ( m1_subset_1(u1_pre_topc(k1_tsep_1(sK0,sK1,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK1)))))
    | ~ spl14_196 ),
    inference(unit_resulting_resolution,[],[f688,f115])).

fof(f688,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_196 ),
    inference(avatar_component_clause,[],[f687])).

fof(f1225,plain,
    ( spl14_394
    | ~ spl14_48
    | ~ spl14_196 ),
    inference(avatar_split_clause,[],[f1211,f687,f295,f1223])).

fof(f1223,plain,
    ( spl14_394
  <=> k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(k1_tsep_1(sK0,sK1,sK1)),u1_pre_topc(k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_394])])).

fof(f295,plain,
    ( spl14_48
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_48])])).

fof(f1211,plain,
    ( k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(k1_tsep_1(sK0,sK1,sK1)),u1_pre_topc(k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_48
    | ~ spl14_196 ),
    inference(unit_resulting_resolution,[],[f296,f688,f116])).

fof(f296,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_48 ),
    inference(avatar_component_clause,[],[f295])).

fof(f1221,plain,
    ( spl14_392
    | ~ spl14_196 ),
    inference(avatar_split_clause,[],[f1212,f687,f1219])).

fof(f1219,plain,
    ( spl14_392
  <=> m1_pre_topc(sK8(k1_tsep_1(sK0,sK1,sK1)),k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_392])])).

fof(f1212,plain,
    ( m1_pre_topc(sK8(k1_tsep_1(sK0,sK1,sK1)),k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_196 ),
    inference(unit_resulting_resolution,[],[f688,f118])).

fof(f1217,plain,
    ( spl14_390
    | spl14_55
    | ~ spl14_194
    | ~ spl14_196 ),
    inference(avatar_split_clause,[],[f1213,f687,f683,f308,f1215])).

fof(f1215,plain,
    ( spl14_390
  <=> m1_connsp_2(sK11(k1_tsep_1(sK0,sK1,sK1),sK10(u1_struct_0(k1_tsep_1(sK0,sK1,sK1)))),k1_tsep_1(sK0,sK1,sK1),sK10(u1_struct_0(k1_tsep_1(sK0,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_390])])).

fof(f308,plain,
    ( spl14_55
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_55])])).

fof(f683,plain,
    ( spl14_194
  <=> v2_pre_topc(k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_194])])).

fof(f1213,plain,
    ( m1_connsp_2(sK11(k1_tsep_1(sK0,sK1,sK1),sK10(u1_struct_0(k1_tsep_1(sK0,sK1,sK1)))),k1_tsep_1(sK0,sK1,sK1),sK10(u1_struct_0(k1_tsep_1(sK0,sK1,sK1))))
    | ~ spl14_55
    | ~ spl14_194
    | ~ spl14_196 ),
    inference(unit_resulting_resolution,[],[f309,f684,f125,f688,f136])).

fof(f684,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_194 ),
    inference(avatar_component_clause,[],[f683])).

fof(f309,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_55 ),
    inference(avatar_component_clause,[],[f308])).

fof(f1209,plain,
    ( spl14_388
    | ~ spl14_144 ),
    inference(avatar_split_clause,[],[f1190,f543,f1207])).

fof(f1207,plain,
    ( spl14_388
  <=> m1_subset_1(u1_pre_topc(k1_tsep_1(sK0,sK2,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_388])])).

fof(f543,plain,
    ( spl14_144
  <=> l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_144])])).

fof(f1190,plain,
    ( m1_subset_1(u1_pre_topc(k1_tsep_1(sK0,sK2,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK2)))))
    | ~ spl14_144 ),
    inference(unit_resulting_resolution,[],[f544,f115])).

fof(f544,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_144 ),
    inference(avatar_component_clause,[],[f543])).

fof(f1205,plain,
    ( spl14_386
    | ~ spl14_34
    | ~ spl14_144 ),
    inference(avatar_split_clause,[],[f1191,f543,f246,f1203])).

fof(f1203,plain,
    ( spl14_386
  <=> k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(k1_tsep_1(sK0,sK2,sK2)),u1_pre_topc(k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_386])])).

fof(f246,plain,
    ( spl14_34
  <=> v1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_34])])).

fof(f1191,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(k1_tsep_1(sK0,sK2,sK2)),u1_pre_topc(k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_34
    | ~ spl14_144 ),
    inference(unit_resulting_resolution,[],[f247,f544,f116])).

fof(f247,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_34 ),
    inference(avatar_component_clause,[],[f246])).

fof(f1201,plain,
    ( spl14_384
    | ~ spl14_144 ),
    inference(avatar_split_clause,[],[f1192,f543,f1199])).

fof(f1199,plain,
    ( spl14_384
  <=> m1_pre_topc(sK8(k1_tsep_1(sK0,sK2,sK2)),k1_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_384])])).

fof(f1192,plain,
    ( m1_pre_topc(sK8(k1_tsep_1(sK0,sK2,sK2)),k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_144 ),
    inference(unit_resulting_resolution,[],[f544,f118])).

fof(f1197,plain,
    ( spl14_382
    | spl14_37
    | ~ spl14_142
    | ~ spl14_144 ),
    inference(avatar_split_clause,[],[f1193,f543,f539,f251,f1195])).

fof(f1195,plain,
    ( spl14_382
  <=> m1_connsp_2(sK11(k1_tsep_1(sK0,sK2,sK2),sK10(u1_struct_0(k1_tsep_1(sK0,sK2,sK2)))),k1_tsep_1(sK0,sK2,sK2),sK10(u1_struct_0(k1_tsep_1(sK0,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_382])])).

fof(f251,plain,
    ( spl14_37
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_37])])).

fof(f539,plain,
    ( spl14_142
  <=> v2_pre_topc(k1_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_142])])).

fof(f1193,plain,
    ( m1_connsp_2(sK11(k1_tsep_1(sK0,sK2,sK2),sK10(u1_struct_0(k1_tsep_1(sK0,sK2,sK2)))),k1_tsep_1(sK0,sK2,sK2),sK10(u1_struct_0(k1_tsep_1(sK0,sK2,sK2))))
    | ~ spl14_37
    | ~ spl14_142
    | ~ spl14_144 ),
    inference(unit_resulting_resolution,[],[f252,f540,f125,f544,f136])).

fof(f540,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_142 ),
    inference(avatar_component_clause,[],[f539])).

fof(f252,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_37 ),
    inference(avatar_component_clause,[],[f251])).

fof(f1189,plain,
    ( spl14_380
    | ~ spl14_346 ),
    inference(avatar_split_clause,[],[f1180,f1096,f1187])).

fof(f1187,plain,
    ( spl14_380
  <=> m1_subset_1(u1_pre_topc(sK8(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_380])])).

fof(f1096,plain,
    ( spl14_346
  <=> l1_pre_topc(sK8(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_346])])).

fof(f1180,plain,
    ( m1_subset_1(u1_pre_topc(sK8(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8(sK2)))))
    | ~ spl14_346 ),
    inference(unit_resulting_resolution,[],[f1097,f115])).

fof(f1097,plain,
    ( l1_pre_topc(sK8(sK2))
    | ~ spl14_346 ),
    inference(avatar_component_clause,[],[f1096])).

fof(f1185,plain,
    ( spl14_378
    | ~ spl14_346 ),
    inference(avatar_split_clause,[],[f1181,f1096,f1183])).

fof(f1183,plain,
    ( spl14_378
  <=> m1_pre_topc(sK8(sK8(sK2)),sK8(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_378])])).

fof(f1181,plain,
    ( m1_pre_topc(sK8(sK8(sK2)),sK8(sK2))
    | ~ spl14_346 ),
    inference(unit_resulting_resolution,[],[f1097,f118])).

fof(f1179,plain,
    ( spl14_376
    | ~ spl14_94 ),
    inference(avatar_split_clause,[],[f1175,f408,f1177])).

fof(f1177,plain,
    ( spl14_376
  <=> r1_tarski(sK6,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_376])])).

fof(f408,plain,
    ( spl14_94
  <=> m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_94])])).

fof(f1175,plain,
    ( r1_tarski(sK6,u1_struct_0(sK1))
    | ~ spl14_94 ),
    inference(unit_resulting_resolution,[],[f409,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',t3_subset)).

fof(f409,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl14_94 ),
    inference(avatar_component_clause,[],[f408])).

fof(f1174,plain,
    ( spl14_374
    | ~ spl14_78 ),
    inference(avatar_split_clause,[],[f1170,f365,f1172])).

fof(f1172,plain,
    ( spl14_374
  <=> r1_tarski(sK7,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_374])])).

fof(f365,plain,
    ( spl14_78
  <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_78])])).

fof(f1170,plain,
    ( r1_tarski(sK7,u1_struct_0(sK2))
    | ~ spl14_78 ),
    inference(unit_resulting_resolution,[],[f366,f137])).

fof(f366,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl14_78 ),
    inference(avatar_component_clause,[],[f365])).

fof(f1169,plain,
    ( spl14_372
    | ~ spl14_64
    | ~ spl14_96 ),
    inference(avatar_split_clause,[],[f1160,f412,f330,f1167])).

fof(f1167,plain,
    ( spl14_372
  <=> l1_pre_topc(sK8(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_372])])).

fof(f330,plain,
    ( spl14_64
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_64])])).

fof(f412,plain,
    ( spl14_96
  <=> m1_pre_topc(sK8(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_96])])).

fof(f1160,plain,
    ( l1_pre_topc(sK8(sK1))
    | ~ spl14_64
    | ~ spl14_96 ),
    inference(unit_resulting_resolution,[],[f331,f413,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',dt_m1_pre_topc)).

fof(f413,plain,
    ( m1_pre_topc(sK8(sK1),sK1)
    | ~ spl14_96 ),
    inference(avatar_component_clause,[],[f412])).

fof(f331,plain,
    ( l1_pre_topc(sK1)
    | ~ spl14_64 ),
    inference(avatar_component_clause,[],[f330])).

fof(f1165,plain,
    ( spl14_370
    | ~ spl14_62
    | ~ spl14_64
    | ~ spl14_96 ),
    inference(avatar_split_clause,[],[f1161,f412,f330,f326,f1163])).

fof(f1163,plain,
    ( spl14_370
  <=> v2_pre_topc(sK8(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_370])])).

fof(f326,plain,
    ( spl14_62
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_62])])).

fof(f1161,plain,
    ( v2_pre_topc(sK8(sK1))
    | ~ spl14_62
    | ~ spl14_64
    | ~ spl14_96 ),
    inference(unit_resulting_resolution,[],[f327,f331,f413,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',cc1_pre_topc)).

fof(f327,plain,
    ( v2_pre_topc(sK1)
    | ~ spl14_62 ),
    inference(avatar_component_clause,[],[f326])).

fof(f1159,plain,
    ( spl14_368
    | ~ spl14_88 ),
    inference(avatar_split_clause,[],[f1155,f390,f1157])).

fof(f1157,plain,
    ( spl14_368
  <=> r1_tarski(sK9(sK0,sK1,sK2,sK4,sK6,sK7),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_368])])).

fof(f1155,plain,
    ( r1_tarski(sK9(sK0,sK1,sK2,sK4,sK6,sK7),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_88 ),
    inference(unit_resulting_resolution,[],[f391,f137])).

fof(f1153,plain,
    ( ~ spl14_367
    | ~ spl14_4
    | ~ spl14_82 ),
    inference(avatar_split_clause,[],[f1144,f378,f172,f1151])).

fof(f1151,plain,
    ( spl14_367
  <=> ~ m1_connsp_2(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k1_tsep_1(sK0,sK1,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_367])])).

fof(f172,plain,
    ( spl14_4
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f378,plain,
    ( spl14_82
  <=> r1_tarski(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k2_xboole_0(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_82])])).

fof(f1144,plain,
    ( ~ m1_connsp_2(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k1_tsep_1(sK0,sK1,sK2),sK4)
    | ~ spl14_4
    | ~ spl14_82 ),
    inference(unit_resulting_resolution,[],[f379,f393])).

fof(f393,plain,
    ( ! [X8] :
        ( ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK4)
        | ~ r1_tarski(X8,k2_xboole_0(sK6,sK7)) )
    | ~ spl14_4 ),
    inference(forward_demodulation,[],[f148,f173])).

fof(f173,plain,
    ( sK4 = sK5
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f172])).

fof(f148,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
      | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK5) ) ),
    inference(definition_unfolding,[],[f110,f107])).

fof(f107,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
        | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
    & m1_connsp_2(sK7,sK2,sK5)
    & m1_connsp_2(sK6,sK1,sK4)
    & sK3 = sK5
    & sK3 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f44,f83,f82,f81,f80,f79,f78,f77,f76])).

fof(f76,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ! [X8] :
                                        ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                        | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                    & m1_connsp_2(X7,X2,X5) )
                                & m1_connsp_2(X6,X1,X4) )
                            & X3 = X5
                            & X3 = X4
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
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
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(sK0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2))) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ! [X8] :
                                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                    | ~ m1_connsp_2(X8,k1_tsep_1(X0,sK1,X2),X3) )
                                & m1_connsp_2(X7,X2,X5) )
                            & m1_connsp_2(X6,sK1,X4) )
                        & X3 = X5
                        & X3 = X4
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK1,X2))) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ! [X8] :
                                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                  | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                              & m1_connsp_2(X7,X2,X5) )
                          & m1_connsp_2(X6,X1,X4) )
                      & X3 = X5
                      & X3 = X4
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ! [X8] :
                                ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,sK2),X3) )
                            & m1_connsp_2(X7,sK2,X5) )
                        & m1_connsp_2(X6,X1,X4) )
                    & X3 = X5
                    & X3 = X4
                    & m1_subset_1(X5,u1_struct_0(sK2)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK2))) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ! [X8] :
                              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                              | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                          & m1_connsp_2(X7,X2,X5) )
                      & m1_connsp_2(X6,X1,X4) )
                  & X3 = X5
                  & X3 = X4
                  & m1_subset_1(X5,u1_struct_0(X2)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ! [X8] :
                            ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                            | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),sK3) )
                        & m1_connsp_2(X7,X2,X5) )
                    & m1_connsp_2(X6,X1,X4) )
                & sK3 = X5
                & sK3 = X4
                & m1_subset_1(X5,u1_struct_0(X2)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                          | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                      & m1_connsp_2(X7,X2,X5) )
                  & m1_connsp_2(X6,X1,X4) )
              & X3 = X5
              & X3 = X4
              & m1_subset_1(X5,u1_struct_0(X2)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ! [X8] :
                        ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                        | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                    & m1_connsp_2(X7,X2,X5) )
                & m1_connsp_2(X6,X1,sK4) )
            & X3 = X5
            & sK4 = X3
            & m1_subset_1(X5,u1_struct_0(X2)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ! [X8] :
                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                      | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                  & m1_connsp_2(X7,X2,X5) )
              & m1_connsp_2(X6,X1,X4) )
          & X3 = X5
          & X3 = X4
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ! [X8] :
                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                    | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                & m1_connsp_2(X7,X2,sK5) )
            & m1_connsp_2(X6,X1,X4) )
        & sK5 = X3
        & X3 = X4
        & m1_subset_1(sK5,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ! [X8] :
                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                  | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
              & m1_connsp_2(X7,X2,X5) )
          & m1_connsp_2(X6,X1,X4) )
     => ( ? [X7] :
            ( ! [X8] :
                ( ~ r1_tarski(X8,k2_xboole_0(sK6,X7))
                | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
            & m1_connsp_2(X7,X2,X5) )
        & m1_connsp_2(sK6,X1,X4) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ! [X8] :
              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
              | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
          & m1_connsp_2(X7,X2,X5) )
     => ( ! [X8] :
            ( ~ r1_tarski(X8,k2_xboole_0(X6,sK7))
            | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
        & m1_connsp_2(sK7,X2,X5) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ( ( X3 = X5
                                & X3 = X4 )
                             => ! [X6] :
                                  ( m1_connsp_2(X6,X1,X4)
                                 => ! [X7] :
                                      ( m1_connsp_2(X7,X2,X5)
                                     => ? [X8] :
                                          ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                          & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( X3 = X5
                              & X3 = X4 )
                           => ! [X6] :
                                ( m1_connsp_2(X6,X1,X4)
                               => ! [X7] :
                                    ( m1_connsp_2(X7,X2,X5)
                                   => ? [X8] :
                                        ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                        & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',t21_tmap_1)).

fof(f110,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
      | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f379,plain,
    ( r1_tarski(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k2_xboole_0(sK6,sK7))
    | ~ spl14_82 ),
    inference(avatar_component_clause,[],[f378])).

fof(f1149,plain,
    ( spl14_364
    | ~ spl14_82 ),
    inference(avatar_split_clause,[],[f1145,f378,f1147])).

fof(f1147,plain,
    ( spl14_364
  <=> m1_subset_1(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k1_zfmisc_1(k2_xboole_0(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_364])])).

fof(f1145,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k1_zfmisc_1(k2_xboole_0(sK6,sK7)))
    | ~ spl14_82 ),
    inference(unit_resulting_resolution,[],[f379,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f1143,plain,
    ( spl14_362
    | ~ spl14_20
    | ~ spl14_22
    | spl14_25
    | ~ spl14_30 ),
    inference(avatar_split_clause,[],[f1139,f227,f212,f208,f204,f1141])).

fof(f1141,plain,
    ( spl14_362
  <=> m1_subset_1(sK11(sK0,sK10(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_362])])).

fof(f204,plain,
    ( spl14_20
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).

fof(f208,plain,
    ( spl14_22
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).

fof(f212,plain,
    ( spl14_25
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_25])])).

fof(f227,plain,
    ( spl14_30
  <=> m1_connsp_2(sK11(sK0,sK10(u1_struct_0(sK0))),sK0,sK10(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_30])])).

fof(f1139,plain,
    ( m1_subset_1(sK11(sK0,sK10(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_25
    | ~ spl14_30 ),
    inference(unit_resulting_resolution,[],[f213,f209,f205,f125,f228,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',dt_m1_connsp_2)).

fof(f228,plain,
    ( m1_connsp_2(sK11(sK0,sK10(u1_struct_0(sK0))),sK0,sK10(u1_struct_0(sK0)))
    | ~ spl14_30 ),
    inference(avatar_component_clause,[],[f227])).

fof(f205,plain,
    ( l1_pre_topc(sK0)
    | ~ spl14_20 ),
    inference(avatar_component_clause,[],[f204])).

fof(f209,plain,
    ( v2_pre_topc(sK0)
    | ~ spl14_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f213,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl14_25 ),
    inference(avatar_component_clause,[],[f212])).

fof(f1138,plain,
    ( ~ spl14_361
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f1117,f382,f1135])).

fof(f1135,plain,
    ( spl14_361
  <=> ~ r2_hidden(sK9(sK0,sK1,sK2,sK4,sK6,sK7),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_361])])).

fof(f1117,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK2,sK4,sK6,sK7),sK4)
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f383,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',antisymmetry_r2_hidden)).

fof(f1137,plain,
    ( ~ spl14_361
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f1118,f382,f1135])).

fof(f1118,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK2,sK4,sK6,sK7),sK4)
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f383,f128])).

fof(f1133,plain,
    ( spl14_358
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f1119,f382,f1131])).

fof(f1131,plain,
    ( spl14_358
  <=> m1_subset_1(sK4,sK9(sK0,sK1,sK2,sK4,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_358])])).

fof(f1119,plain,
    ( m1_subset_1(sK4,sK9(sK0,sK1,sK2,sK4,sK6,sK7))
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f383,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',t1_subset)).

fof(f1129,plain,
    ( ~ spl14_357
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f1120,f382,f1127])).

fof(f1127,plain,
    ( spl14_357
  <=> ~ v1_xboole_0(sK9(sK0,sK1,sK2,sK4,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_357])])).

fof(f1120,plain,
    ( ~ v1_xboole_0(sK9(sK0,sK1,sK2,sK4,sK6,sK7))
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f383,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',t7_boole)).

fof(f1125,plain,
    ( ~ spl14_355
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f1121,f382,f1123])).

fof(f1123,plain,
    ( spl14_355
  <=> ~ sP13(sK9(sK0,sK1,sK2,sK4,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_355])])).

fof(f1121,plain,
    ( ~ sP13(sK9(sK0,sK1,sK2,sK4,sK6,sK7))
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f383,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP13(X1) ) ),
    inference(general_splitting,[],[f146,f161_D])).

fof(f161,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP13(X1) ) ),
    inference(cnf_transformation,[],[f161_D])).

fof(f161_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP13(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP13])])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',t5_subset)).

fof(f1113,plain,
    ( spl14_352
    | ~ spl14_28 ),
    inference(avatar_split_clause,[],[f1099,f222,f1111])).

fof(f1111,plain,
    ( spl14_352
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_352])])).

fof(f222,plain,
    ( spl14_28
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).

fof(f1099,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f223,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',dt_g1_pre_topc)).

fof(f223,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl14_28 ),
    inference(avatar_component_clause,[],[f222])).

fof(f1109,plain,
    ( spl14_350
    | ~ spl14_28 ),
    inference(avatar_split_clause,[],[f1100,f222,f1107])).

fof(f1107,plain,
    ( spl14_350
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_350])])).

fof(f1100,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f223,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1105,plain,
    ( spl14_348
    | ~ spl14_28 ),
    inference(avatar_split_clause,[],[f1101,f222,f1103])).

fof(f1103,plain,
    ( spl14_348
  <=> r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_348])])).

fof(f1101,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f223,f137])).

fof(f1098,plain,
    ( spl14_346
    | ~ spl14_40
    | ~ spl14_72 ),
    inference(avatar_split_clause,[],[f1089,f351,f260,f1096])).

fof(f260,plain,
    ( spl14_40
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_40])])).

fof(f351,plain,
    ( spl14_72
  <=> m1_pre_topc(sK8(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_72])])).

fof(f1089,plain,
    ( l1_pre_topc(sK8(sK2))
    | ~ spl14_40
    | ~ spl14_72 ),
    inference(unit_resulting_resolution,[],[f261,f352,f117])).

fof(f352,plain,
    ( m1_pre_topc(sK8(sK2),sK2)
    | ~ spl14_72 ),
    inference(avatar_component_clause,[],[f351])).

fof(f261,plain,
    ( l1_pre_topc(sK2)
    | ~ spl14_40 ),
    inference(avatar_component_clause,[],[f260])).

fof(f1094,plain,
    ( spl14_344
    | ~ spl14_38
    | ~ spl14_40
    | ~ spl14_72 ),
    inference(avatar_split_clause,[],[f1090,f351,f260,f256,f1092])).

fof(f1092,plain,
    ( spl14_344
  <=> v2_pre_topc(sK8(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_344])])).

fof(f256,plain,
    ( spl14_38
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_38])])).

fof(f1090,plain,
    ( v2_pre_topc(sK8(sK2))
    | ~ spl14_38
    | ~ spl14_40
    | ~ spl14_72 ),
    inference(unit_resulting_resolution,[],[f257,f261,f352,f124])).

fof(f257,plain,
    ( v2_pre_topc(sK2)
    | ~ spl14_38 ),
    inference(avatar_component_clause,[],[f256])).

fof(f1088,plain,
    ( spl14_342
    | ~ spl14_20
    | ~ spl14_46 ),
    inference(avatar_split_clause,[],[f871,f291,f204,f1086])).

fof(f291,plain,
    ( spl14_46
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_46])])).

fof(f871,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_20
    | ~ spl14_46 ),
    inference(unit_resulting_resolution,[],[f205,f292,f117])).

fof(f292,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl14_46 ),
    inference(avatar_component_clause,[],[f291])).

fof(f1084,plain,
    ( spl14_340
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_46 ),
    inference(avatar_split_clause,[],[f872,f291,f208,f204,f1082])).

fof(f872,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_46 ),
    inference(unit_resulting_resolution,[],[f209,f205,f292,f124])).

fof(f1080,plain,
    ( spl14_338
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f873,f317,f291,f251,f241,f212,f204,f1073])).

fof(f1073,plain,
    ( spl14_338
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_338])])).

fof(f241,plain,
    ( spl14_32
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).

fof(f873,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f318,f292,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
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
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',commutativity_k1_tsep_1)).

fof(f242,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
    | ~ spl14_32 ),
    inference(avatar_component_clause,[],[f241])).

fof(f1079,plain,
    ( spl14_336
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | spl14_57
    | spl14_59 ),
    inference(avatar_split_clause,[],[f874,f317,f312,f291,f286,f212,f204,f1069])).

fof(f1069,plain,
    ( spl14_336
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK1)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_336])])).

fof(f286,plain,
    ( spl14_44
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_44])])).

fof(f312,plain,
    ( spl14_57
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_57])])).

fof(f874,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK1)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | ~ spl14_57
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f318,f292,f141])).

fof(f287,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK1),sK0)
    | ~ spl14_44 ),
    inference(avatar_component_clause,[],[f286])).

fof(f313,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_57 ),
    inference(avatar_component_clause,[],[f312])).

fof(f1078,plain,
    ( spl14_334
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | spl14_55
    | spl14_59 ),
    inference(avatar_split_clause,[],[f875,f317,f308,f291,f282,f212,f204,f1065])).

fof(f1065,plain,
    ( spl14_334
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_334])])).

fof(f282,plain,
    ( spl14_42
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_42])])).

fof(f875,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | ~ spl14_55
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f318,f292,f141])).

fof(f283,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),sK0)
    | ~ spl14_42 ),
    inference(avatar_component_clause,[],[f282])).

fof(f1077,plain,
    ( spl14_332
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f877,f317,f291,f212,f204,f200,f196,f1061])).

fof(f1061,plain,
    ( spl14_332
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_332])])).

fof(f196,plain,
    ( spl14_16
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).

fof(f200,plain,
    ( spl14_19
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f877,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f318,f292,f141])).

fof(f197,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl14_16 ),
    inference(avatar_component_clause,[],[f196])).

fof(f201,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl14_19 ),
    inference(avatar_component_clause,[],[f200])).

fof(f1076,plain,
    ( spl14_330
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f878,f317,f291,f212,f204,f192,f188,f1057])).

fof(f1057,plain,
    ( spl14_330
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_330])])).

fof(f188,plain,
    ( spl14_12
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f192,plain,
    ( spl14_15
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).

fof(f878,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f318,f292,f141])).

fof(f189,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f188])).

fof(f193,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl14_15 ),
    inference(avatar_component_clause,[],[f192])).

fof(f1075,plain,
    ( spl14_338
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f879,f317,f291,f251,f241,f212,f204,f1073])).

fof(f879,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f318,f292,f141])).

fof(f1071,plain,
    ( spl14_336
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | spl14_57
    | spl14_59 ),
    inference(avatar_split_clause,[],[f880,f317,f312,f291,f286,f212,f204,f1069])).

fof(f880,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK1)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | ~ spl14_57
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f318,f292,f141])).

fof(f1067,plain,
    ( spl14_334
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | spl14_55
    | spl14_59 ),
    inference(avatar_split_clause,[],[f881,f317,f308,f291,f282,f212,f204,f1065])).

fof(f881,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | ~ spl14_55
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f318,f292,f141])).

fof(f1063,plain,
    ( spl14_332
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f883,f317,f291,f212,f204,f200,f196,f1061])).

fof(f883,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f318,f292,f141])).

fof(f1059,plain,
    ( spl14_330
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f884,f317,f291,f212,f204,f192,f188,f1057])).

fof(f884,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f318,f292,f141])).

fof(f1055,plain,
    ( ~ spl14_329
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f885,f317,f291,f251,f241,f212,f204,f1053])).

fof(f1053,plain,
    ( spl14_329
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_329])])).

fof(f885,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f318,f292,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
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
    inference(flattening,[],[f71])).

fof(f71,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',dt_k1_tsep_1)).

fof(f1051,plain,
    ( ~ spl14_327
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | spl14_57
    | spl14_59 ),
    inference(avatar_split_clause,[],[f886,f317,f312,f291,f286,f212,f204,f1049])).

fof(f1049,plain,
    ( spl14_327
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_327])])).

fof(f886,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | ~ spl14_57
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f318,f292,f142])).

fof(f1047,plain,
    ( ~ spl14_325
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | spl14_55
    | spl14_59 ),
    inference(avatar_split_clause,[],[f887,f317,f308,f291,f282,f212,f204,f1045])).

fof(f1045,plain,
    ( spl14_325
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_325])])).

fof(f887,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | ~ spl14_55
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f318,f292,f142])).

fof(f1043,plain,
    ( ~ spl14_313
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f888,f317,f291,f212,f204,f1020])).

fof(f1020,plain,
    ( spl14_313
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_313])])).

fof(f888,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f318,f292,f318,f292,f142])).

fof(f1042,plain,
    ( ~ spl14_323
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f889,f317,f291,f212,f204,f200,f196,f1040])).

fof(f1040,plain,
    ( spl14_323
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_323])])).

fof(f889,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f318,f292,f142])).

fof(f1038,plain,
    ( ~ spl14_321
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f890,f317,f291,f212,f204,f192,f188,f1036])).

fof(f1036,plain,
    ( spl14_321
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_321])])).

fof(f890,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f318,f292,f142])).

fof(f1034,plain,
    ( ~ spl14_319
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f891,f317,f291,f251,f241,f212,f204,f1032])).

fof(f1032,plain,
    ( spl14_319
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_319])])).

fof(f891,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f318,f292,f142])).

fof(f1030,plain,
    ( ~ spl14_317
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | spl14_57
    | spl14_59 ),
    inference(avatar_split_clause,[],[f892,f317,f312,f291,f286,f212,f204,f1028])).

fof(f1028,plain,
    ( spl14_317
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_317])])).

fof(f892,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | ~ spl14_57
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f318,f292,f142])).

fof(f1026,plain,
    ( ~ spl14_315
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | spl14_55
    | spl14_59 ),
    inference(avatar_split_clause,[],[f893,f317,f308,f291,f282,f212,f204,f1024])).

fof(f1024,plain,
    ( spl14_315
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_315])])).

fof(f893,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | ~ spl14_55
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f318,f292,f142])).

fof(f1022,plain,
    ( ~ spl14_313
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f894,f317,f291,f212,f204,f1020])).

fof(f894,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f318,f292,f318,f292,f142])).

fof(f1018,plain,
    ( ~ spl14_311
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f895,f317,f291,f212,f204,f200,f196,f1016])).

fof(f1016,plain,
    ( spl14_311
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_311])])).

fof(f895,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f318,f292,f142])).

fof(f1014,plain,
    ( ~ spl14_309
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f896,f317,f291,f212,f204,f192,f188,f1012])).

fof(f1012,plain,
    ( spl14_309
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_309])])).

fof(f896,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f318,f292,f142])).

fof(f1010,plain,
    ( spl14_306
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f897,f317,f291,f251,f241,f212,f204,f1008])).

fof(f1008,plain,
    ( spl14_306
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_306])])).

fof(f897,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f318,f292,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f1006,plain,
    ( spl14_304
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | spl14_57
    | spl14_59 ),
    inference(avatar_split_clause,[],[f898,f317,f312,f291,f286,f212,f204,f1004])).

fof(f1004,plain,
    ( spl14_304
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_304])])).

fof(f898,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | ~ spl14_57
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f318,f292,f143])).

fof(f1002,plain,
    ( spl14_302
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | spl14_55
    | spl14_59 ),
    inference(avatar_split_clause,[],[f899,f317,f308,f291,f282,f212,f204,f1000])).

fof(f1000,plain,
    ( spl14_302
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_302])])).

fof(f899,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | ~ spl14_55
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f318,f292,f143])).

fof(f998,plain,
    ( spl14_290
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f900,f317,f291,f212,f204,f975])).

fof(f975,plain,
    ( spl14_290
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_290])])).

fof(f900,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f318,f292,f318,f292,f143])).

fof(f997,plain,
    ( spl14_300
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f901,f317,f291,f212,f204,f200,f196,f995])).

fof(f995,plain,
    ( spl14_300
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_300])])).

fof(f901,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f318,f292,f143])).

fof(f993,plain,
    ( spl14_298
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f902,f317,f291,f212,f204,f192,f188,f991])).

fof(f991,plain,
    ( spl14_298
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_298])])).

fof(f902,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f318,f292,f143])).

fof(f989,plain,
    ( spl14_296
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f903,f317,f291,f251,f241,f212,f204,f987])).

fof(f987,plain,
    ( spl14_296
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_296])])).

fof(f903,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f318,f292,f143])).

fof(f985,plain,
    ( spl14_294
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | spl14_57
    | spl14_59 ),
    inference(avatar_split_clause,[],[f904,f317,f312,f291,f286,f212,f204,f983])).

fof(f983,plain,
    ( spl14_294
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_294])])).

fof(f904,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | ~ spl14_57
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f318,f292,f143])).

fof(f981,plain,
    ( spl14_292
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | spl14_55
    | spl14_59 ),
    inference(avatar_split_clause,[],[f905,f317,f308,f291,f282,f212,f204,f979])).

fof(f979,plain,
    ( spl14_292
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_292])])).

fof(f905,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | ~ spl14_55
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f318,f292,f143])).

fof(f977,plain,
    ( spl14_290
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f906,f317,f291,f212,f204,f975])).

fof(f906,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f318,f292,f318,f292,f143])).

fof(f973,plain,
    ( spl14_288
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f907,f317,f291,f212,f204,f200,f196,f971])).

fof(f971,plain,
    ( spl14_288
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_288])])).

fof(f907,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f318,f292,f143])).

fof(f969,plain,
    ( spl14_286
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f908,f317,f291,f212,f204,f192,f188,f967])).

fof(f967,plain,
    ( spl14_286
  <=> v1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_286])])).

fof(f908,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f318,f292,f143])).

fof(f965,plain,
    ( spl14_284
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f909,f317,f291,f251,f241,f212,f204,f963])).

fof(f963,plain,
    ( spl14_284
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_284])])).

fof(f909,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f318,f292,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f961,plain,
    ( spl14_282
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | spl14_57
    | spl14_59 ),
    inference(avatar_split_clause,[],[f910,f317,f312,f291,f286,f212,f204,f959])).

fof(f959,plain,
    ( spl14_282
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_282])])).

fof(f910,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK1)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | ~ spl14_57
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f318,f292,f144])).

fof(f957,plain,
    ( spl14_280
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | spl14_55
    | spl14_59 ),
    inference(avatar_split_clause,[],[f911,f317,f308,f291,f282,f212,f204,f955])).

fof(f955,plain,
    ( spl14_280
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_280])])).

fof(f911,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK1)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | ~ spl14_55
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f318,f292,f144])).

fof(f953,plain,
    ( spl14_268
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f912,f317,f291,f212,f204,f930])).

fof(f930,plain,
    ( spl14_268
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_268])])).

fof(f912,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f318,f292,f318,f292,f144])).

fof(f952,plain,
    ( spl14_278
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f913,f317,f291,f212,f204,f200,f196,f950])).

fof(f950,plain,
    ( spl14_278
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_278])])).

fof(f913,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK1),sK0)
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f318,f292,f144])).

fof(f948,plain,
    ( spl14_276
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f914,f317,f291,f212,f204,f192,f188,f946])).

fof(f946,plain,
    ( spl14_276
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_276])])).

fof(f914,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),sK2),sK0)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f318,f292,f144])).

fof(f944,plain,
    ( spl14_274
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f915,f317,f291,f251,f241,f212,f204,f942])).

fof(f942,plain,
    ( spl14_274
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_274])])).

fof(f915,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK2)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f318,f292,f144])).

fof(f940,plain,
    ( spl14_272
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | spl14_57
    | spl14_59 ),
    inference(avatar_split_clause,[],[f916,f317,f312,f291,f286,f212,f204,f938])).

fof(f938,plain,
    ( spl14_272
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_272])])).

fof(f916,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK2)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_46
    | ~ spl14_57
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f318,f292,f144])).

fof(f936,plain,
    ( spl14_270
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | spl14_55
    | spl14_59 ),
    inference(avatar_split_clause,[],[f917,f317,f308,f291,f282,f212,f204,f934])).

fof(f934,plain,
    ( spl14_270
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_270])])).

fof(f917,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_46
    | ~ spl14_55
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f318,f292,f144])).

fof(f932,plain,
    ( spl14_268
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f918,f317,f291,f212,f204,f930])).

fof(f918,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f318,f292,f318,f292,f144])).

fof(f928,plain,
    ( spl14_266
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f919,f317,f291,f212,f204,f200,f196,f926])).

fof(f926,plain,
    ( spl14_266
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_266])])).

fof(f919,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK2)),sK0)
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f318,f292,f144])).

fof(f924,plain,
    ( spl14_264
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_46
    | spl14_59 ),
    inference(avatar_split_clause,[],[f920,f317,f291,f212,f204,f192,f188,f922])).

fof(f922,plain,
    ( spl14_264
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_264])])).

fof(f920,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK2)),sK0)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_46
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f318,f292,f144])).

fof(f870,plain,
    ( spl14_262
    | ~ spl14_20
    | ~ spl14_44 ),
    inference(avatar_split_clause,[],[f690,f286,f204,f868])).

fof(f690,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_20
    | ~ spl14_44 ),
    inference(unit_resulting_resolution,[],[f205,f287,f117])).

fof(f866,plain,
    ( spl14_260
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_44 ),
    inference(avatar_split_clause,[],[f691,f286,f208,f204,f864])).

fof(f691,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_44 ),
    inference(unit_resulting_resolution,[],[f209,f205,f287,f124])).

fof(f862,plain,
    ( spl14_258
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f692,f312,f286,f251,f241,f212,f204,f856])).

fof(f856,plain,
    ( spl14_258
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_258])])).

fof(f692,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f313,f287,f141])).

fof(f861,plain,
    ( spl14_256
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | spl14_55
    | spl14_57 ),
    inference(avatar_split_clause,[],[f694,f312,f308,f286,f282,f212,f204,f852])).

fof(f852,plain,
    ( spl14_256
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK1)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_256])])).

fof(f694,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK1)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | ~ spl14_55
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f313,f287,f141])).

fof(f860,plain,
    ( spl14_254
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f695,f312,f286,f212,f204,f200,f196,f848])).

fof(f848,plain,
    ( spl14_254
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_254])])).

fof(f695,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f313,f287,f141])).

fof(f859,plain,
    ( spl14_252
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f696,f312,f286,f212,f204,f192,f188,f844])).

fof(f844,plain,
    ( spl14_252
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_252])])).

fof(f696,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f313,f287,f141])).

fof(f858,plain,
    ( spl14_258
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f697,f312,f286,f251,f241,f212,f204,f856])).

fof(f697,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f313,f287,f141])).

fof(f854,plain,
    ( spl14_256
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | spl14_55
    | spl14_57 ),
    inference(avatar_split_clause,[],[f699,f312,f308,f286,f282,f212,f204,f852])).

fof(f699,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK1)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | ~ spl14_55
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f313,f287,f141])).

fof(f850,plain,
    ( spl14_254
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f700,f312,f286,f212,f204,f200,f196,f848])).

fof(f700,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f313,f287,f141])).

fof(f846,plain,
    ( spl14_252
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f701,f312,f286,f212,f204,f192,f188,f844])).

fof(f701,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f313,f287,f141])).

fof(f842,plain,
    ( ~ spl14_251
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f702,f312,f286,f251,f241,f212,f204,f840])).

fof(f840,plain,
    ( spl14_251
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_251])])).

fof(f702,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f313,f287,f142])).

fof(f838,plain,
    ( ~ spl14_241
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f703,f312,f286,f212,f204,f819])).

fof(f819,plain,
    ( spl14_241
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_241])])).

fof(f703,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f313,f287,f142])).

fof(f837,plain,
    ( ~ spl14_249
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | spl14_55
    | spl14_57 ),
    inference(avatar_split_clause,[],[f704,f312,f308,f286,f282,f212,f204,f835])).

fof(f835,plain,
    ( spl14_249
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_249])])).

fof(f704,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | ~ spl14_55
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f313,f287,f142])).

fof(f833,plain,
    ( ~ spl14_247
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f705,f312,f286,f212,f204,f200,f196,f831])).

fof(f831,plain,
    ( spl14_247
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_247])])).

fof(f705,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f313,f287,f142])).

fof(f829,plain,
    ( ~ spl14_245
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f706,f312,f286,f212,f204,f192,f188,f827])).

fof(f827,plain,
    ( spl14_245
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_245])])).

fof(f706,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f313,f287,f142])).

fof(f825,plain,
    ( ~ spl14_243
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f707,f312,f286,f251,f241,f212,f204,f823])).

fof(f823,plain,
    ( spl14_243
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_243])])).

fof(f707,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f313,f287,f142])).

fof(f821,plain,
    ( ~ spl14_241
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f708,f312,f286,f212,f204,f819])).

fof(f708,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f313,f287,f142])).

fof(f817,plain,
    ( ~ spl14_239
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | spl14_55
    | spl14_57 ),
    inference(avatar_split_clause,[],[f709,f312,f308,f286,f282,f212,f204,f815])).

fof(f815,plain,
    ( spl14_239
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_239])])).

fof(f709,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | ~ spl14_55
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f313,f287,f142])).

fof(f813,plain,
    ( ~ spl14_237
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f710,f312,f286,f212,f204,f200,f196,f811])).

fof(f811,plain,
    ( spl14_237
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_237])])).

fof(f710,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f313,f287,f142])).

fof(f809,plain,
    ( ~ spl14_235
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f711,f312,f286,f212,f204,f192,f188,f807])).

fof(f807,plain,
    ( spl14_235
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_235])])).

fof(f711,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f313,f287,f142])).

fof(f805,plain,
    ( spl14_232
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f712,f312,f286,f251,f241,f212,f204,f803])).

fof(f803,plain,
    ( spl14_232
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_232])])).

fof(f712,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f313,f287,f143])).

fof(f801,plain,
    ( spl14_222
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f713,f312,f286,f212,f204,f782])).

fof(f782,plain,
    ( spl14_222
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_222])])).

fof(f713,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f313,f287,f143])).

fof(f800,plain,
    ( spl14_230
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | spl14_55
    | spl14_57 ),
    inference(avatar_split_clause,[],[f714,f312,f308,f286,f282,f212,f204,f798])).

fof(f798,plain,
    ( spl14_230
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_230])])).

fof(f714,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | ~ spl14_55
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f313,f287,f143])).

fof(f796,plain,
    ( spl14_228
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f715,f312,f286,f212,f204,f200,f196,f794])).

fof(f794,plain,
    ( spl14_228
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_228])])).

fof(f715,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f313,f287,f143])).

fof(f792,plain,
    ( spl14_226
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f716,f312,f286,f212,f204,f192,f188,f790])).

fof(f790,plain,
    ( spl14_226
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_226])])).

fof(f716,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f313,f287,f143])).

fof(f788,plain,
    ( spl14_224
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f717,f312,f286,f251,f241,f212,f204,f786])).

fof(f786,plain,
    ( spl14_224
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_224])])).

fof(f717,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f313,f287,f143])).

fof(f784,plain,
    ( spl14_222
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f718,f312,f286,f212,f204,f782])).

fof(f718,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f313,f287,f143])).

fof(f780,plain,
    ( spl14_220
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | spl14_55
    | spl14_57 ),
    inference(avatar_split_clause,[],[f719,f312,f308,f286,f282,f212,f204,f778])).

fof(f778,plain,
    ( spl14_220
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_220])])).

fof(f719,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | ~ spl14_55
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f313,f287,f143])).

fof(f776,plain,
    ( spl14_218
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f720,f312,f286,f212,f204,f200,f196,f774])).

fof(f774,plain,
    ( spl14_218
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_218])])).

fof(f720,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f313,f287,f143])).

fof(f772,plain,
    ( spl14_216
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f721,f312,f286,f212,f204,f192,f188,f770])).

fof(f770,plain,
    ( spl14_216
  <=> v1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_216])])).

fof(f721,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK1)))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f313,f287,f143])).

fof(f768,plain,
    ( spl14_214
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f722,f312,f286,f251,f241,f212,f204,f766])).

fof(f766,plain,
    ( spl14_214
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_214])])).

fof(f722,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK2)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f313,f287,f144])).

fof(f764,plain,
    ( spl14_204
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f723,f312,f286,f212,f204,f745])).

fof(f745,plain,
    ( spl14_204
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_204])])).

fof(f723,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK1)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f313,f287,f144])).

fof(f763,plain,
    ( spl14_212
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | spl14_55
    | spl14_57 ),
    inference(avatar_split_clause,[],[f724,f312,f308,f286,f282,f212,f204,f761])).

fof(f761,plain,
    ( spl14_212
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_212])])).

fof(f724,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK1,sK1)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | ~ spl14_55
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f313,f287,f144])).

fof(f759,plain,
    ( spl14_210
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f725,f312,f286,f212,f204,f200,f196,f757])).

fof(f757,plain,
    ( spl14_210
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_210])])).

fof(f725,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK1),sK0)
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f313,f287,f144])).

fof(f755,plain,
    ( spl14_208
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f726,f312,f286,f212,f204,f192,f188,f753])).

fof(f753,plain,
    ( spl14_208
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_208])])).

fof(f726,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),sK2),sK0)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f313,f287,f144])).

fof(f751,plain,
    ( spl14_206
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f727,f312,f286,f251,f241,f212,f204,f749])).

fof(f749,plain,
    ( spl14_206
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_206])])).

fof(f727,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK1)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f313,f287,f144])).

fof(f747,plain,
    ( spl14_204
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f728,f312,f286,f212,f204,f745])).

fof(f728,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK1),k1_tsep_1(sK0,sK2,sK1)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f313,f287,f313,f287,f144])).

fof(f743,plain,
    ( spl14_202
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | spl14_55
    | spl14_57 ),
    inference(avatar_split_clause,[],[f729,f312,f308,f286,f282,f212,f204,f741])).

fof(f741,plain,
    ( spl14_202
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_202])])).

fof(f729,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK1)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_44
    | ~ spl14_55
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f313,f287,f144])).

fof(f739,plain,
    ( spl14_200
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f730,f312,f286,f212,f204,f200,f196,f737])).

fof(f737,plain,
    ( spl14_200
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_200])])).

fof(f730,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK1)),sK0)
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f313,f287,f144])).

fof(f735,plain,
    ( spl14_198
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_44
    | spl14_57 ),
    inference(avatar_split_clause,[],[f731,f312,f286,f212,f204,f192,f188,f733])).

fof(f733,plain,
    ( spl14_198
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_198])])).

fof(f731,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK1)),sK0)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_44
    | ~ spl14_57 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f313,f287,f144])).

fof(f689,plain,
    ( spl14_196
    | ~ spl14_20
    | ~ spl14_42 ),
    inference(avatar_split_clause,[],[f546,f282,f204,f687])).

fof(f546,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_20
    | ~ spl14_42 ),
    inference(unit_resulting_resolution,[],[f205,f283,f117])).

fof(f685,plain,
    ( spl14_194
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_42 ),
    inference(avatar_split_clause,[],[f547,f282,f208,f204,f683])).

fof(f547,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_42 ),
    inference(unit_resulting_resolution,[],[f209,f205,f283,f124])).

fof(f681,plain,
    ( spl14_192
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f548,f308,f282,f251,f241,f212,f204,f676])).

fof(f676,plain,
    ( spl14_192
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_192])])).

fof(f548,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f309,f283,f141])).

fof(f680,plain,
    ( spl14_190
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f550,f308,f282,f212,f204,f200,f196,f672])).

fof(f672,plain,
    ( spl14_190
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_190])])).

fof(f550,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f309,f283,f141])).

fof(f679,plain,
    ( spl14_188
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f551,f308,f282,f212,f204,f192,f188,f668])).

fof(f668,plain,
    ( spl14_188
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_188])])).

fof(f551,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f309,f283,f141])).

fof(f678,plain,
    ( spl14_192
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f552,f308,f282,f251,f241,f212,f204,f676])).

fof(f552,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK2)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f309,f283,f141])).

fof(f674,plain,
    ( spl14_190
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f554,f308,f282,f212,f204,f200,f196,f672])).

fof(f554,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f309,f283,f141])).

fof(f670,plain,
    ( spl14_188
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f555,f308,f282,f212,f204,f192,f188,f668])).

fof(f555,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f309,f283,f141])).

fof(f666,plain,
    ( ~ spl14_187
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f556,f308,f282,f251,f241,f212,f204,f664])).

fof(f664,plain,
    ( spl14_187
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_187])])).

fof(f556,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f309,f283,f142])).

fof(f662,plain,
    ( ~ spl14_179
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f557,f308,f282,f212,f204,f647])).

fof(f647,plain,
    ( spl14_179
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_179])])).

fof(f557,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f309,f283,f142])).

fof(f661,plain,
    ( ~ spl14_185
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f558,f308,f282,f212,f204,f200,f196,f659])).

fof(f659,plain,
    ( spl14_185
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_185])])).

fof(f558,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f309,f283,f142])).

fof(f657,plain,
    ( ~ spl14_183
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f559,f308,f282,f212,f204,f192,f188,f655])).

fof(f655,plain,
    ( spl14_183
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_183])])).

fof(f559,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f309,f283,f142])).

fof(f653,plain,
    ( ~ spl14_181
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f560,f308,f282,f251,f241,f212,f204,f651])).

fof(f651,plain,
    ( spl14_181
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_181])])).

fof(f560,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f309,f283,f142])).

fof(f649,plain,
    ( ~ spl14_179
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f561,f308,f282,f212,f204,f647])).

fof(f561,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f309,f283,f142])).

fof(f645,plain,
    ( ~ spl14_177
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f562,f308,f282,f212,f204,f200,f196,f643])).

fof(f643,plain,
    ( spl14_177
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_177])])).

fof(f562,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f309,f283,f142])).

fof(f641,plain,
    ( ~ spl14_175
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f563,f308,f282,f212,f204,f192,f188,f639])).

fof(f639,plain,
    ( spl14_175
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_175])])).

fof(f563,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f309,f283,f142])).

fof(f637,plain,
    ( spl14_172
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f564,f308,f282,f251,f241,f212,f204,f635])).

fof(f635,plain,
    ( spl14_172
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_172])])).

fof(f564,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f309,f283,f143])).

fof(f633,plain,
    ( spl14_164
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f565,f308,f282,f212,f204,f618])).

fof(f618,plain,
    ( spl14_164
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_164])])).

fof(f565,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f309,f283,f143])).

fof(f632,plain,
    ( spl14_170
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f566,f308,f282,f212,f204,f200,f196,f630])).

fof(f630,plain,
    ( spl14_170
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_170])])).

fof(f566,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f309,f283,f143])).

fof(f628,plain,
    ( spl14_168
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f567,f308,f282,f212,f204,f192,f188,f626])).

fof(f626,plain,
    ( spl14_168
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_168])])).

fof(f567,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f309,f283,f143])).

fof(f624,plain,
    ( spl14_166
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f568,f308,f282,f251,f241,f212,f204,f622])).

fof(f622,plain,
    ( spl14_166
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_166])])).

fof(f568,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f309,f283,f143])).

fof(f620,plain,
    ( spl14_164
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f569,f308,f282,f212,f204,f618])).

fof(f569,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f309,f283,f143])).

fof(f616,plain,
    ( spl14_162
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f570,f308,f282,f212,f204,f200,f196,f614])).

fof(f614,plain,
    ( spl14_162
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_162])])).

fof(f570,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f309,f283,f143])).

fof(f612,plain,
    ( spl14_160
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f571,f308,f282,f212,f204,f192,f188,f610])).

fof(f610,plain,
    ( spl14_160
  <=> v1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_160])])).

fof(f571,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK1)))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f309,f283,f143])).

fof(f608,plain,
    ( spl14_158
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f572,f308,f282,f251,f241,f212,f204,f606])).

fof(f606,plain,
    ( spl14_158
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_158])])).

fof(f572,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK2,sK2)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f309,f283,f144])).

fof(f604,plain,
    ( spl14_150
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f573,f308,f282,f212,f204,f589])).

fof(f589,plain,
    ( spl14_150
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_150])])).

fof(f573,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK1)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f309,f283,f144])).

fof(f603,plain,
    ( spl14_156
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f574,f308,f282,f212,f204,f200,f196,f601])).

fof(f601,plain,
    ( spl14_156
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_156])])).

fof(f574,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK1),sK0)
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f309,f283,f144])).

fof(f599,plain,
    ( spl14_154
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f575,f308,f282,f212,f204,f192,f188,f597])).

fof(f597,plain,
    ( spl14_154
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_154])])).

fof(f575,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),sK2),sK0)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f309,f283,f144])).

fof(f595,plain,
    ( spl14_152
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f576,f308,f282,f251,f241,f212,f204,f593])).

fof(f593,plain,
    ( spl14_152
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_152])])).

fof(f576,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK1)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f309,f283,f144])).

fof(f591,plain,
    ( spl14_150
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f577,f308,f282,f212,f204,f589])).

fof(f577,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK1)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f309,f283,f309,f283,f144])).

fof(f587,plain,
    ( spl14_148
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f578,f308,f282,f212,f204,f200,f196,f585])).

fof(f585,plain,
    ( spl14_148
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_148])])).

fof(f578,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK1,sK1)),sK0)
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f309,f283,f144])).

fof(f583,plain,
    ( spl14_146
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_42
    | spl14_55 ),
    inference(avatar_split_clause,[],[f579,f308,f282,f212,f204,f192,f188,f581])).

fof(f581,plain,
    ( spl14_146
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_146])])).

fof(f579,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK1,sK1)),sK0)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_42
    | ~ spl14_55 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f309,f283,f144])).

fof(f545,plain,
    ( spl14_144
    | ~ spl14_20
    | ~ spl14_32 ),
    inference(avatar_split_clause,[],[f439,f241,f204,f543])).

fof(f439,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_20
    | ~ spl14_32 ),
    inference(unit_resulting_resolution,[],[f205,f242,f117])).

fof(f541,plain,
    ( spl14_142
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_32 ),
    inference(avatar_split_clause,[],[f440,f241,f208,f204,f539])).

fof(f440,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_32 ),
    inference(unit_resulting_resolution,[],[f209,f205,f242,f124])).

fof(f537,plain,
    ( spl14_140
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f442,f251,f241,f212,f204,f200,f196,f533])).

fof(f533,plain,
    ( spl14_140
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_140])])).

fof(f442,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f252,f242,f141])).

fof(f536,plain,
    ( spl14_138
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f443,f251,f241,f212,f204,f192,f188,f529])).

fof(f529,plain,
    ( spl14_138
  <=> k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_138])])).

fof(f443,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f252,f242,f141])).

fof(f535,plain,
    ( spl14_140
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f445,f251,f241,f212,f204,f200,f196,f533])).

fof(f445,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK1) = k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f252,f242,f141])).

fof(f531,plain,
    ( spl14_138
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f446,f251,f241,f212,f204,f192,f188,f529])).

fof(f446,plain,
    ( k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK2) = k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f252,f242,f141])).

fof(f527,plain,
    ( ~ spl14_133
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f447,f251,f241,f212,f204,f516])).

fof(f516,plain,
    ( spl14_133
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_133])])).

fof(f447,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f252,f242,f142])).

fof(f526,plain,
    ( ~ spl14_137
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f448,f251,f241,f212,f204,f200,f196,f524])).

fof(f524,plain,
    ( spl14_137
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_137])])).

fof(f448,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f252,f242,f142])).

fof(f522,plain,
    ( ~ spl14_135
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f449,f251,f241,f212,f204,f192,f188,f520])).

fof(f520,plain,
    ( spl14_135
  <=> ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_135])])).

fof(f449,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f252,f242,f142])).

fof(f518,plain,
    ( ~ spl14_133
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f450,f251,f241,f212,f204,f516])).

fof(f450,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f252,f242,f142])).

fof(f514,plain,
    ( ~ spl14_131
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f451,f251,f241,f212,f204,f200,f196,f512])).

fof(f512,plain,
    ( spl14_131
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_131])])).

fof(f451,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f252,f242,f142])).

fof(f510,plain,
    ( ~ spl14_129
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f452,f251,f241,f212,f204,f192,f188,f508])).

fof(f508,plain,
    ( spl14_129
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_129])])).

fof(f452,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f252,f242,f142])).

fof(f506,plain,
    ( spl14_122
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f453,f251,f241,f212,f204,f495])).

fof(f495,plain,
    ( spl14_122
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_122])])).

fof(f453,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f252,f242,f143])).

fof(f505,plain,
    ( spl14_126
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f454,f251,f241,f212,f204,f200,f196,f503])).

fof(f503,plain,
    ( spl14_126
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_126])])).

fof(f454,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f252,f242,f143])).

fof(f501,plain,
    ( spl14_124
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f455,f251,f241,f212,f204,f192,f188,f499])).

fof(f499,plain,
    ( spl14_124
  <=> v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_124])])).

fof(f455,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f252,f242,f143])).

fof(f497,plain,
    ( spl14_122
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f456,f251,f241,f212,f204,f495])).

fof(f456,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f252,f242,f143])).

fof(f493,plain,
    ( spl14_120
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f457,f251,f241,f212,f204,f200,f196,f491])).

fof(f491,plain,
    ( spl14_120
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_120])])).

fof(f457,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f252,f242,f143])).

fof(f489,plain,
    ( spl14_118
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f458,f251,f241,f212,f204,f192,f188,f487])).

fof(f487,plain,
    ( spl14_118
  <=> v1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_118])])).

fof(f458,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK2)))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f252,f242,f143])).

fof(f485,plain,
    ( spl14_112
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f459,f251,f241,f212,f204,f474])).

fof(f474,plain,
    ( spl14_112
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_112])])).

fof(f459,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK2)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f252,f242,f144])).

fof(f484,plain,
    ( spl14_116
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f460,f251,f241,f212,f204,f200,f196,f482])).

fof(f482,plain,
    ( spl14_116
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_116])])).

fof(f460,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK1),sK0)
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f252,f242,f144])).

fof(f480,plain,
    ( spl14_114
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f461,f251,f241,f212,f204,f192,f188,f478])).

fof(f478,plain,
    ( spl14_114
  <=> m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_114])])).

fof(f461,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),sK2),sK0)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f252,f242,f144])).

fof(f476,plain,
    ( spl14_112
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f462,f251,f241,f212,f204,f474])).

fof(f462,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK2,sK2)),sK0)
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f252,f242,f252,f242,f144])).

fof(f472,plain,
    ( spl14_110
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f463,f251,f241,f212,f204,f200,f196,f470])).

fof(f470,plain,
    ( spl14_110
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_110])])).

fof(f463,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK2)),sK0)
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f252,f242,f144])).

fof(f468,plain,
    ( spl14_108
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25
    | ~ spl14_32
    | spl14_37 ),
    inference(avatar_split_clause,[],[f464,f251,f241,f212,f204,f192,f188,f466])).

fof(f466,plain,
    ( spl14_108
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_108])])).

fof(f464,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,k1_tsep_1(sK0,sK2,sK2)),sK0)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25
    | ~ spl14_32
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f252,f242,f144])).

fof(f438,plain,
    ( spl14_106
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f429,f426,f436])).

fof(f436,plain,
    ( spl14_106
  <=> m1_subset_1(u1_pre_topc(sK8(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_106])])).

fof(f426,plain,
    ( spl14_102
  <=> l1_pre_topc(sK8(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_102])])).

fof(f429,plain,
    ( m1_subset_1(u1_pre_topc(sK8(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8(sK0)))))
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f427,f115])).

fof(f427,plain,
    ( l1_pre_topc(sK8(sK0))
    | ~ spl14_102 ),
    inference(avatar_component_clause,[],[f426])).

fof(f434,plain,
    ( spl14_104
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f430,f426,f432])).

fof(f432,plain,
    ( spl14_104
  <=> m1_pre_topc(sK8(sK8(sK0)),sK8(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_104])])).

fof(f430,plain,
    ( m1_pre_topc(sK8(sK8(sK0)),sK8(sK0))
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f427,f118])).

fof(f428,plain,
    ( spl14_102
    | ~ spl14_20
    | ~ spl14_26 ),
    inference(avatar_split_clause,[],[f419,f218,f204,f426])).

fof(f218,plain,
    ( spl14_26
  <=> m1_pre_topc(sK8(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).

fof(f419,plain,
    ( l1_pre_topc(sK8(sK0))
    | ~ spl14_20
    | ~ spl14_26 ),
    inference(unit_resulting_resolution,[],[f205,f219,f117])).

fof(f219,plain,
    ( m1_pre_topc(sK8(sK0),sK0)
    | ~ spl14_26 ),
    inference(avatar_component_clause,[],[f218])).

fof(f424,plain,
    ( spl14_100
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_26 ),
    inference(avatar_split_clause,[],[f420,f218,f208,f204,f422])).

fof(f422,plain,
    ( spl14_100
  <=> v2_pre_topc(sK8(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_100])])).

fof(f420,plain,
    ( v2_pre_topc(sK8(sK0))
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_26 ),
    inference(unit_resulting_resolution,[],[f209,f205,f219,f124])).

fof(f418,plain,
    ( spl14_98
    | ~ spl14_64 ),
    inference(avatar_split_clause,[],[f394,f330,f416])).

fof(f416,plain,
    ( spl14_98
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_98])])).

fof(f394,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl14_64 ),
    inference(unit_resulting_resolution,[],[f331,f115])).

fof(f414,plain,
    ( spl14_96
    | ~ spl14_64 ),
    inference(avatar_split_clause,[],[f395,f330,f412])).

fof(f395,plain,
    ( m1_pre_topc(sK8(sK1),sK1)
    | ~ spl14_64 ),
    inference(unit_resulting_resolution,[],[f331,f118])).

fof(f410,plain,
    ( spl14_94
    | ~ spl14_2
    | ~ spl14_8
    | spl14_19
    | ~ spl14_62
    | ~ spl14_64 ),
    inference(avatar_split_clause,[],[f396,f330,f326,f200,f180,f168,f408])).

fof(f168,plain,
    ( spl14_2
  <=> m1_connsp_2(sK6,sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f180,plain,
    ( spl14_8
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f396,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_19
    | ~ spl14_62
    | ~ spl14_64 ),
    inference(unit_resulting_resolution,[],[f201,f327,f169,f181,f331,f135])).

fof(f181,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f180])).

fof(f169,plain,
    ( m1_connsp_2(sK6,sK1,sK4)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f168])).

fof(f406,plain,
    ( spl14_92
    | spl14_19
    | ~ spl14_62
    | ~ spl14_64 ),
    inference(avatar_split_clause,[],[f397,f330,f326,f200,f404])).

fof(f404,plain,
    ( spl14_92
  <=> m1_connsp_2(sK11(sK1,sK10(u1_struct_0(sK1))),sK1,sK10(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_92])])).

fof(f397,plain,
    ( m1_connsp_2(sK11(sK1,sK10(u1_struct_0(sK1))),sK1,sK10(u1_struct_0(sK1)))
    | ~ spl14_19
    | ~ spl14_62
    | ~ spl14_64 ),
    inference(unit_resulting_resolution,[],[f201,f327,f125,f331,f136])).

fof(f402,plain,
    ( spl14_90
    | ~ spl14_8
    | spl14_19
    | ~ spl14_62
    | ~ spl14_64 ),
    inference(avatar_split_clause,[],[f398,f330,f326,f200,f180,f400])).

fof(f400,plain,
    ( spl14_90
  <=> m1_connsp_2(sK11(sK1,sK4),sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_90])])).

fof(f398,plain,
    ( m1_connsp_2(sK11(sK1,sK4),sK1,sK4)
    | ~ spl14_8
    | ~ spl14_19
    | ~ spl14_62
    | ~ spl14_64 ),
    inference(unit_resulting_resolution,[],[f201,f327,f181,f331,f136])).

fof(f392,plain,
    ( spl14_88
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_12
    | spl14_15
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | ~ spl14_22
    | spl14_25
    | ~ spl14_66
    | ~ spl14_68
    | ~ spl14_80 ),
    inference(avatar_split_clause,[],[f373,f370,f340,f335,f212,f208,f204,f200,f196,f192,f188,f180,f168,f390])).

fof(f335,plain,
    ( spl14_66
  <=> m1_connsp_2(sK7,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_66])])).

fof(f340,plain,
    ( spl14_68
  <=> m1_subset_1(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_68])])).

fof(f373,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_25
    | ~ spl14_66
    | ~ spl14_68
    | ~ spl14_80 ),
    inference(unit_resulting_resolution,[],[f213,f209,f205,f201,f193,f197,f189,f336,f169,f181,f341,f371,f160])).

fof(f160,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( ~ m1_connsp_2(X7,X2,X5)
      | m1_subset_1(sK9(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f159])).

fof(f159,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tarski(sK9(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
                                    & r2_hidden(X3,sK9(X0,X1,X2,X3,X6,X7))
                                    & v3_pre_topc(sK9(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
                                    & m1_subset_1(sK9(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  | ~ m1_connsp_2(X7,X2,X5) )
                              | ~ m1_connsp_2(X6,X1,X4) )
                          | X3 != X5
                          | X3 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f54,f87])).

fof(f87,plain,(
    ! [X7,X6,X3,X2,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(X8,k2_xboole_0(X6,X7))
          & r2_hidden(X3,X8)
          & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
     => ( r1_tarski(sK9(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
        & r2_hidden(X3,sK9(X0,X1,X2,X3,X6,X7))
        & v3_pre_topc(sK9(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ? [X8] :
                                      ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                      & r2_hidden(X3,X8)
                                      & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  | ~ m1_connsp_2(X7,X2,X5) )
                              | ~ m1_connsp_2(X6,X1,X4) )
                          | X3 != X5
                          | X3 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ? [X8] :
                                      ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                      & r2_hidden(X3,X8)
                                      & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  | ~ m1_connsp_2(X7,X2,X5) )
                              | ~ m1_connsp_2(X6,X1,X4) )
                          | X3 != X5
                          | X3 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( X3 = X5
                              & X3 = X4 )
                           => ! [X6] :
                                ( m1_connsp_2(X6,X1,X4)
                               => ! [X7] :
                                    ( m1_connsp_2(X7,X2,X5)
                                   => ? [X8] :
                                        ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                        & r2_hidden(X3,X8)
                                        & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                        & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t21_tmap_1.p',t20_tmap_1)).

fof(f341,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ spl14_68 ),
    inference(avatar_component_clause,[],[f340])).

fof(f336,plain,
    ( m1_connsp_2(sK7,sK2,sK4)
    | ~ spl14_66 ),
    inference(avatar_component_clause,[],[f335])).

fof(f388,plain,
    ( spl14_86
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_12
    | spl14_15
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | ~ spl14_22
    | spl14_25
    | ~ spl14_66
    | ~ spl14_68
    | ~ spl14_80 ),
    inference(avatar_split_clause,[],[f374,f370,f340,f335,f212,f208,f204,f200,f196,f192,f188,f180,f168,f386])).

fof(f374,plain,
    ( v3_pre_topc(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_25
    | ~ spl14_66
    | ~ spl14_68
    | ~ spl14_80 ),
    inference(unit_resulting_resolution,[],[f213,f209,f205,f201,f193,f197,f189,f336,f169,f181,f341,f371,f158])).

fof(f158,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( ~ m1_connsp_2(X7,X2,X5)
      | v3_pre_topc(sK9(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2))
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f157])).

fof(f157,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( v3_pre_topc(sK9(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v3_pre_topc(sK9(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f384,plain,
    ( spl14_84
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_12
    | spl14_15
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | ~ spl14_22
    | spl14_25
    | ~ spl14_66
    | ~ spl14_68
    | ~ spl14_80 ),
    inference(avatar_split_clause,[],[f375,f370,f340,f335,f212,f208,f204,f200,f196,f192,f188,f180,f168,f382])).

fof(f375,plain,
    ( r2_hidden(sK4,sK9(sK0,sK1,sK2,sK4,sK6,sK7))
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_25
    | ~ spl14_66
    | ~ spl14_68
    | ~ spl14_80 ),
    inference(unit_resulting_resolution,[],[f213,f209,f205,f201,f193,f197,f189,f336,f169,f181,f341,f371,f156])).

fof(f156,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( ~ m1_connsp_2(X7,X2,X5)
      | r2_hidden(X5,sK9(X0,X1,X2,X5,X6,X7))
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f155])).

fof(f155,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( r2_hidden(X5,sK9(X0,X1,X2,X5,X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X3,sK9(X0,X1,X2,X3,X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f380,plain,
    ( spl14_82
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_12
    | spl14_15
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | ~ spl14_22
    | spl14_25
    | ~ spl14_66
    | ~ spl14_68
    | ~ spl14_80 ),
    inference(avatar_split_clause,[],[f376,f370,f340,f335,f212,f208,f204,f200,f196,f192,f188,f180,f168,f378])).

fof(f376,plain,
    ( r1_tarski(sK9(sK0,sK1,sK2,sK4,sK6,sK7),k2_xboole_0(sK6,sK7))
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_25
    | ~ spl14_66
    | ~ spl14_68
    | ~ spl14_80 ),
    inference(unit_resulting_resolution,[],[f213,f209,f205,f201,f193,f197,f189,f336,f169,f181,f341,f371,f154])).

fof(f154,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( ~ m1_connsp_2(X7,X2,X5)
      | r1_tarski(sK9(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7))
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f153])).

fof(f153,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( r1_tarski(sK9(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tarski(sK9(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f372,plain,
    ( spl14_80
    | ~ spl14_4
    | ~ spl14_10 ),
    inference(avatar_split_clause,[],[f368,f184,f172,f370])).

fof(f184,plain,
    ( spl14_10
  <=> m1_subset_1(sK5,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f368,plain,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_4
    | ~ spl14_10 ),
    inference(forward_demodulation,[],[f185,f173])).

fof(f185,plain,
    ( m1_subset_1(sK5,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f367,plain,
    ( spl14_78
    | spl14_15
    | ~ spl14_38
    | ~ spl14_40
    | ~ spl14_66
    | ~ spl14_68 ),
    inference(avatar_split_clause,[],[f358,f340,f335,f260,f256,f192,f365])).

fof(f358,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl14_15
    | ~ spl14_38
    | ~ spl14_40
    | ~ spl14_66
    | ~ spl14_68 ),
    inference(unit_resulting_resolution,[],[f193,f257,f261,f336,f341,f135])).

fof(f363,plain,
    ( spl14_76
    | spl14_15
    | ~ spl14_38
    | ~ spl14_40
    | ~ spl14_68 ),
    inference(avatar_split_clause,[],[f359,f340,f260,f256,f192,f361])).

fof(f361,plain,
    ( spl14_76
  <=> m1_connsp_2(sK11(sK2,sK4),sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_76])])).

fof(f359,plain,
    ( m1_connsp_2(sK11(sK2,sK4),sK2,sK4)
    | ~ spl14_15
    | ~ spl14_38
    | ~ spl14_40
    | ~ spl14_68 ),
    inference(unit_resulting_resolution,[],[f193,f257,f261,f341,f136])).

fof(f357,plain,
    ( spl14_74
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f343,f260,f355])).

fof(f355,plain,
    ( spl14_74
  <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_74])])).

fof(f343,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl14_40 ),
    inference(unit_resulting_resolution,[],[f261,f115])).

fof(f353,plain,
    ( spl14_72
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f344,f260,f351])).

fof(f344,plain,
    ( m1_pre_topc(sK8(sK2),sK2)
    | ~ spl14_40 ),
    inference(unit_resulting_resolution,[],[f261,f118])).

fof(f349,plain,
    ( spl14_70
    | spl14_15
    | ~ spl14_38
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f345,f260,f256,f192,f347])).

fof(f347,plain,
    ( spl14_70
  <=> m1_connsp_2(sK11(sK2,sK10(u1_struct_0(sK2))),sK2,sK10(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_70])])).

fof(f345,plain,
    ( m1_connsp_2(sK11(sK2,sK10(u1_struct_0(sK2))),sK2,sK10(u1_struct_0(sK2)))
    | ~ spl14_15
    | ~ spl14_38
    | ~ spl14_40 ),
    inference(unit_resulting_resolution,[],[f193,f257,f125,f261,f136])).

fof(f342,plain,
    ( spl14_68
    | ~ spl14_4
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f338,f176,f172,f340])).

fof(f176,plain,
    ( spl14_6
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f338,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ spl14_4
    | ~ spl14_6 ),
    inference(forward_demodulation,[],[f177,f173])).

fof(f177,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f176])).

fof(f337,plain,
    ( spl14_66
    | ~ spl14_0
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f333,f172,f164,f335])).

fof(f164,plain,
    ( spl14_0
  <=> m1_connsp_2(sK7,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_0])])).

fof(f333,plain,
    ( m1_connsp_2(sK7,sK2,sK4)
    | ~ spl14_0
    | ~ spl14_4 ),
    inference(forward_demodulation,[],[f165,f173])).

fof(f165,plain,
    ( m1_connsp_2(sK7,sK2,sK5)
    | ~ spl14_0 ),
    inference(avatar_component_clause,[],[f164])).

fof(f332,plain,
    ( spl14_64
    | ~ spl14_16
    | ~ spl14_20 ),
    inference(avatar_split_clause,[],[f263,f204,f196,f330])).

fof(f263,plain,
    ( l1_pre_topc(sK1)
    | ~ spl14_16
    | ~ spl14_20 ),
    inference(unit_resulting_resolution,[],[f205,f197,f117])).

fof(f328,plain,
    ( spl14_62
    | ~ spl14_16
    | ~ spl14_20
    | ~ spl14_22 ),
    inference(avatar_split_clause,[],[f264,f208,f204,f196,f326])).

fof(f264,plain,
    ( v2_pre_topc(sK1)
    | ~ spl14_16
    | ~ spl14_20
    | ~ spl14_22 ),
    inference(unit_resulting_resolution,[],[f209,f205,f197,f124])).

fof(f324,plain,
    ( spl14_60
    | ~ spl14_12
    | spl14_15
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f265,f212,f204,f200,f196,f192,f188,f321])).

fof(f265,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f193,f189,f197,f141])).

fof(f323,plain,
    ( spl14_60
    | ~ spl14_12
    | spl14_15
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f267,f212,f204,f200,f196,f192,f188,f321])).

fof(f267,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f201,f197,f141])).

fof(f319,plain,
    ( ~ spl14_59
    | ~ spl14_12
    | spl14_15
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f269,f212,f204,f200,f196,f192,f188,f317])).

fof(f269,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f193,f189,f197,f142])).

fof(f315,plain,
    ( ~ spl14_55
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f270,f212,f204,f200,f196,f308])).

fof(f270,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f201,f197,f197,f142])).

fof(f314,plain,
    ( ~ spl14_57
    | ~ spl14_12
    | spl14_15
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f271,f212,f204,f200,f196,f192,f188,f312])).

fof(f271,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f201,f197,f142])).

fof(f310,plain,
    ( ~ spl14_55
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f272,f212,f204,f200,f196,f308])).

fof(f272,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f201,f197,f142])).

fof(f306,plain,
    ( spl14_52
    | ~ spl14_12
    | spl14_15
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f273,f212,f204,f200,f196,f192,f188,f304])).

fof(f273,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f193,f189,f197,f143])).

fof(f302,plain,
    ( spl14_48
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f274,f212,f204,f200,f196,f295])).

fof(f274,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f201,f197,f197,f143])).

fof(f301,plain,
    ( spl14_50
    | ~ spl14_12
    | spl14_15
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f275,f212,f204,f200,f196,f192,f188,f299])).

fof(f299,plain,
    ( spl14_50
  <=> v1_pre_topc(k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_50])])).

fof(f275,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK2,sK1))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f201,f197,f143])).

fof(f297,plain,
    ( spl14_48
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f276,f212,f204,f200,f196,f295])).

fof(f276,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK1))
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f201,f197,f143])).

fof(f293,plain,
    ( spl14_46
    | ~ spl14_12
    | spl14_15
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f277,f212,f204,f200,f196,f192,f188,f291])).

fof(f277,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f193,f189,f197,f144])).

fof(f289,plain,
    ( spl14_42
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f278,f212,f204,f200,f196,f282])).

fof(f278,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),sK0)
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f201,f197,f197,f144])).

fof(f288,plain,
    ( spl14_44
    | ~ spl14_12
    | spl14_15
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f279,f212,f204,f200,f196,f192,f188,f286])).

fof(f279,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK1),sK0)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f201,f197,f144])).

fof(f284,plain,
    ( spl14_42
    | ~ spl14_16
    | spl14_19
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f280,f212,f204,f200,f196,f282])).

fof(f280,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),sK0)
    | ~ spl14_16
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f201,f197,f201,f197,f144])).

fof(f262,plain,
    ( spl14_40
    | ~ spl14_12
    | ~ spl14_20 ),
    inference(avatar_split_clause,[],[f230,f204,f188,f260])).

fof(f230,plain,
    ( l1_pre_topc(sK2)
    | ~ spl14_12
    | ~ spl14_20 ),
    inference(unit_resulting_resolution,[],[f205,f189,f117])).

fof(f258,plain,
    ( spl14_38
    | ~ spl14_12
    | ~ spl14_20
    | ~ spl14_22 ),
    inference(avatar_split_clause,[],[f231,f208,f204,f188,f256])).

fof(f231,plain,
    ( v2_pre_topc(sK2)
    | ~ spl14_12
    | ~ spl14_20
    | ~ spl14_22 ),
    inference(unit_resulting_resolution,[],[f209,f205,f189,f124])).

fof(f254,plain,
    ( ~ spl14_37
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f234,f212,f204,f192,f188,f251])).

fof(f234,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f193,f189,f189,f142])).

fof(f253,plain,
    ( ~ spl14_37
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f235,f212,f204,f192,f188,f251])).

fof(f235,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f193,f189,f142])).

fof(f249,plain,
    ( spl14_34
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f236,f212,f204,f192,f188,f246])).

fof(f236,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f193,f189,f189,f143])).

fof(f248,plain,
    ( spl14_34
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f237,f212,f204,f192,f188,f246])).

fof(f237,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK2,sK2))
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f193,f189,f143])).

fof(f244,plain,
    ( spl14_32
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f238,f212,f204,f192,f188,f241])).

fof(f238,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f193,f189,f189,f144])).

fof(f243,plain,
    ( spl14_32
    | ~ spl14_12
    | spl14_15
    | ~ spl14_20
    | spl14_25 ),
    inference(avatar_split_clause,[],[f239,f212,f204,f192,f188,f241])).

fof(f239,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0)
    | ~ spl14_12
    | ~ spl14_15
    | ~ spl14_20
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f213,f205,f193,f189,f193,f189,f144])).

fof(f229,plain,
    ( spl14_30
    | ~ spl14_20
    | ~ spl14_22
    | spl14_25 ),
    inference(avatar_split_clause,[],[f225,f212,f208,f204,f227])).

fof(f225,plain,
    ( m1_connsp_2(sK11(sK0,sK10(u1_struct_0(sK0))),sK0,sK10(u1_struct_0(sK0)))
    | ~ spl14_20
    | ~ spl14_22
    | ~ spl14_25 ),
    inference(unit_resulting_resolution,[],[f205,f209,f125,f213,f136])).

fof(f224,plain,
    ( spl14_28
    | ~ spl14_20 ),
    inference(avatar_split_clause,[],[f215,f204,f222])).

fof(f215,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl14_20 ),
    inference(unit_resulting_resolution,[],[f205,f115])).

fof(f220,plain,
    ( spl14_26
    | ~ spl14_20 ),
    inference(avatar_split_clause,[],[f216,f204,f218])).

fof(f216,plain,
    ( m1_pre_topc(sK8(sK0),sK0)
    | ~ spl14_20 ),
    inference(unit_resulting_resolution,[],[f205,f118])).

fof(f214,plain,(
    ~ spl14_25 ),
    inference(avatar_split_clause,[],[f96,f212])).

fof(f96,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f210,plain,(
    spl14_22 ),
    inference(avatar_split_clause,[],[f97,f208])).

fof(f97,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f206,plain,(
    spl14_20 ),
    inference(avatar_split_clause,[],[f98,f204])).

fof(f98,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f202,plain,(
    ~ spl14_19 ),
    inference(avatar_split_clause,[],[f99,f200])).

fof(f99,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

fof(f198,plain,(
    spl14_16 ),
    inference(avatar_split_clause,[],[f100,f196])).

fof(f100,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f194,plain,(
    ~ spl14_15 ),
    inference(avatar_split_clause,[],[f101,f192])).

fof(f101,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f84])).

fof(f190,plain,(
    spl14_12 ),
    inference(avatar_split_clause,[],[f102,f188])).

fof(f102,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f186,plain,(
    spl14_10 ),
    inference(avatar_split_clause,[],[f150,f184])).

fof(f150,plain,(
    m1_subset_1(sK5,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(definition_unfolding,[],[f103,f107])).

fof(f103,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f84])).

fof(f182,plain,(
    spl14_8 ),
    inference(avatar_split_clause,[],[f104,f180])).

fof(f104,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f84])).

fof(f178,plain,(
    spl14_6 ),
    inference(avatar_split_clause,[],[f105,f176])).

fof(f105,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f84])).

fof(f174,plain,(
    spl14_4 ),
    inference(avatar_split_clause,[],[f149,f172])).

fof(f149,plain,(
    sK4 = sK5 ),
    inference(definition_unfolding,[],[f106,f107])).

fof(f106,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f84])).

fof(f170,plain,(
    spl14_2 ),
    inference(avatar_split_clause,[],[f108,f168])).

fof(f108,plain,(
    m1_connsp_2(sK6,sK1,sK4) ),
    inference(cnf_transformation,[],[f84])).

fof(f166,plain,(
    spl14_0 ),
    inference(avatar_split_clause,[],[f109,f164])).

fof(f109,plain,(
    m1_connsp_2(sK7,sK2,sK5) ),
    inference(cnf_transformation,[],[f84])).
%------------------------------------------------------------------------------

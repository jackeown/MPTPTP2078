%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t17_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:28 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  520 ( 890 expanded)
%              Number of leaves         :  142 ( 399 expanded)
%              Depth                    :   10
%              Number of atoms          : 1382 (2507 expanded)
%              Number of equality atoms :   77 ( 192 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1417,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f359,f366,f373,f380,f387,f394,f401,f408,f415,f422,f429,f436,f443,f450,f457,f464,f471,f478,f485,f492,f499,f506,f513,f520,f527,f534,f541,f548,f555,f562,f569,f576,f583,f590,f597,f604,f611,f618,f625,f632,f639,f646,f653,f660,f667,f674,f681,f688,f695,f702,f709,f716,f723,f730,f737,f744,f751,f758,f765,f772,f779,f786,f793,f800,f807,f814,f821,f828,f835,f842,f860,f907,f929,f984,f1036,f1067,f1074,f1081,f1088,f1095,f1102,f1115,f1122,f1129,f1136,f1139,f1156,f1161,f1168,f1172,f1185,f1199,f1213,f1232,f1257,f1264,f1271,f1300,f1355,f1362,f1369,f1376,f1383,f1414])).

fof(f1414,plain,
    ( ~ spl21_0
    | spl21_5
    | ~ spl21_150
    | ~ spl21_198
    | ~ spl21_202 ),
    inference(avatar_contradiction_clause,[],[f1413])).

fof(f1413,plain,
    ( $false
    | ~ spl21_0
    | ~ spl21_5
    | ~ spl21_150
    | ~ spl21_198
    | ~ spl21_202 ),
    inference(subsumption_resolution,[],[f1412,f1361])).

fof(f1361,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl21_202 ),
    inference(avatar_component_clause,[],[f1360])).

fof(f1360,plain,
    ( spl21_202
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_202])])).

fof(f1412,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | ~ spl21_0
    | ~ spl21_5
    | ~ spl21_150
    | ~ spl21_198 ),
    inference(forward_demodulation,[],[f1411,f1035])).

fof(f1035,plain,
    ( u1_pre_topc(sK0) = k1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl21_150 ),
    inference(avatar_component_clause,[],[f1034])).

fof(f1034,plain,
    ( spl21_150
  <=> u1_pre_topc(sK0) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_150])])).

fof(f1411,plain,
    ( u1_pre_topc(sK1) != k1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl21_0
    | ~ spl21_5
    | ~ spl21_198 ),
    inference(subsumption_resolution,[],[f1410,f372])).

fof(f372,plain,
    ( ~ v1_tdlat_3(sK1)
    | ~ spl21_5 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl21_5
  <=> ~ v1_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_5])])).

fof(f1410,plain,
    ( u1_pre_topc(sK1) != k1_zfmisc_1(u1_struct_0(sK0))
    | v1_tdlat_3(sK1)
    | ~ spl21_0
    | ~ spl21_198 ),
    inference(subsumption_resolution,[],[f1404,f358])).

fof(f358,plain,
    ( l1_pre_topc(sK1)
    | ~ spl21_0 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl21_0
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_0])])).

fof(f1404,plain,
    ( u1_pre_topc(sK1) != k1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK1)
    | v1_tdlat_3(sK1)
    | ~ spl21_198 ),
    inference(superposition,[],[f352,f1299])).

fof(f1299,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl21_198 ),
    inference(avatar_component_clause,[],[f1298])).

fof(f1298,plain,
    ( spl21_198
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_198])])).

fof(f352,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) != k1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v1_tdlat_3(X0) ) ),
    inference(forward_demodulation,[],[f268,f284])).

fof(f284,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f158])).

fof(f158,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',redefinition_k9_setfam_1)).

fof(f268,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f169])).

fof(f169,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f70])).

fof(f70,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',d1_tdlat_3)).

fof(f1383,plain,
    ( spl21_208
    | ~ spl21_44
    | ~ spl21_48 ),
    inference(avatar_split_clause,[],[f950,f525,f511,f1381])).

fof(f1381,plain,
    ( spl21_208
  <=> g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_208])])).

fof(f511,plain,
    ( spl21_44
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_44])])).

fof(f525,plain,
    ( spl21_48
  <=> v1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_48])])).

fof(f950,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK5
    | ~ spl21_44
    | ~ spl21_48 ),
    inference(subsumption_resolution,[],[f935,f512])).

fof(f512,plain,
    ( l1_pre_topc(sK5)
    | ~ spl21_44 ),
    inference(avatar_component_clause,[],[f511])).

fof(f935,plain,
    ( ~ l1_pre_topc(sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK5
    | ~ spl21_48 ),
    inference(resolution,[],[f283,f526])).

fof(f526,plain,
    ( v1_pre_topc(sK5)
    | ~ spl21_48 ),
    inference(avatar_component_clause,[],[f525])).

fof(f283,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f188])).

fof(f188,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f187])).

fof(f187,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',abstractness_v1_pre_topc)).

fof(f1376,plain,
    ( spl21_206
    | ~ spl21_32
    | ~ spl21_36 ),
    inference(avatar_split_clause,[],[f949,f483,f469,f1374])).

fof(f1374,plain,
    ( spl21_206
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_206])])).

fof(f469,plain,
    ( spl21_32
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_32])])).

fof(f483,plain,
    ( spl21_36
  <=> v1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_36])])).

fof(f949,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
    | ~ spl21_32
    | ~ spl21_36 ),
    inference(subsumption_resolution,[],[f934,f470])).

fof(f470,plain,
    ( l1_pre_topc(sK4)
    | ~ spl21_32 ),
    inference(avatar_component_clause,[],[f469])).

fof(f934,plain,
    ( ~ l1_pre_topc(sK4)
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
    | ~ spl21_36 ),
    inference(resolution,[],[f283,f484])).

fof(f484,plain,
    ( v1_pre_topc(sK4)
    | ~ spl21_36 ),
    inference(avatar_component_clause,[],[f483])).

fof(f1369,plain,
    ( spl21_204
    | ~ spl21_20
    | ~ spl21_24 ),
    inference(avatar_split_clause,[],[f948,f441,f427,f1367])).

fof(f1367,plain,
    ( spl21_204
  <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_204])])).

fof(f427,plain,
    ( spl21_20
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_20])])).

fof(f441,plain,
    ( spl21_24
  <=> v1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_24])])).

fof(f948,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | ~ spl21_20
    | ~ spl21_24 ),
    inference(subsumption_resolution,[],[f933,f428])).

fof(f428,plain,
    ( l1_pre_topc(sK3)
    | ~ spl21_20 ),
    inference(avatar_component_clause,[],[f427])).

fof(f933,plain,
    ( ~ l1_pre_topc(sK3)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | ~ spl21_24 ),
    inference(resolution,[],[f283,f442])).

fof(f442,plain,
    ( v1_pre_topc(sK3)
    | ~ spl21_24 ),
    inference(avatar_component_clause,[],[f441])).

fof(f1362,plain,
    ( spl21_202
    | ~ spl21_136
    | ~ spl21_150
    | ~ spl21_152 ),
    inference(avatar_split_clause,[],[f1242,f1065,f1034,f833,f1360])).

fof(f833,plain,
    ( spl21_136
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_136])])).

fof(f1065,plain,
    ( spl21_152
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_152])])).

fof(f1242,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl21_136
    | ~ spl21_150
    | ~ spl21_152 ),
    inference(subsumption_resolution,[],[f1241,f1066])).

fof(f1066,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(u1_pre_topc(sK0)))
    | ~ spl21_152 ),
    inference(avatar_component_clause,[],[f1065])).

fof(f1241,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(u1_pre_topc(sK0)))
    | u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl21_136
    | ~ spl21_150 ),
    inference(forward_demodulation,[],[f1240,f1035])).

fof(f1240,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl21_136 ),
    inference(equality_resolution,[],[f989])).

fof(f989,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | u1_pre_topc(sK1) = X1 )
    | ~ spl21_136 ),
    inference(superposition,[],[f281,f834])).

fof(f834,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl21_136 ),
    inference(avatar_component_clause,[],[f833])).

fof(f281,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f98])).

fof(f98,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',free_g1_pre_topc)).

fof(f1355,plain,
    ( spl21_200
    | ~ spl21_8
    | ~ spl21_12 ),
    inference(avatar_split_clause,[],[f947,f399,f385,f1353])).

fof(f1353,plain,
    ( spl21_200
  <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_200])])).

fof(f385,plain,
    ( spl21_8
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_8])])).

fof(f399,plain,
    ( spl21_12
  <=> v1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_12])])).

fof(f947,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2
    | ~ spl21_8
    | ~ spl21_12 ),
    inference(subsumption_resolution,[],[f932,f386])).

fof(f386,plain,
    ( l1_pre_topc(sK2)
    | ~ spl21_8 ),
    inference(avatar_component_clause,[],[f385])).

fof(f932,plain,
    ( ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2
    | ~ spl21_12 ),
    inference(resolution,[],[f283,f400])).

fof(f400,plain,
    ( v1_pre_topc(sK2)
    | ~ spl21_12 ),
    inference(avatar_component_clause,[],[f399])).

fof(f1300,plain,
    ( spl21_198
    | ~ spl21_136
    | ~ spl21_150
    | ~ spl21_152 ),
    inference(avatar_split_clause,[],[f1218,f1065,f1034,f833,f1298])).

fof(f1218,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl21_136
    | ~ spl21_150
    | ~ spl21_152 ),
    inference(subsumption_resolution,[],[f1217,f1066])).

fof(f1217,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(u1_pre_topc(sK0)))
    | u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl21_136
    | ~ spl21_150 ),
    inference(forward_demodulation,[],[f1216,f1035])).

fof(f1216,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl21_136 ),
    inference(equality_resolution,[],[f986])).

fof(f986,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | u1_struct_0(sK1) = X0 )
    | ~ spl21_136 ),
    inference(superposition,[],[f280,f834])).

fof(f280,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f185])).

fof(f1271,plain,
    ( spl21_196
    | ~ spl21_70
    | ~ spl21_76 ),
    inference(avatar_split_clause,[],[f922,f623,f602,f1269])).

fof(f1269,plain,
    ( spl21_196
  <=> u1_pre_topc(sK7) = k1_zfmisc_1(u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_196])])).

fof(f602,plain,
    ( spl21_70
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_70])])).

fof(f623,plain,
    ( spl21_76
  <=> v1_tdlat_3(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_76])])).

fof(f922,plain,
    ( u1_pre_topc(sK7) = k1_zfmisc_1(u1_struct_0(sK7))
    | ~ spl21_70
    | ~ spl21_76 ),
    inference(subsumption_resolution,[],[f918,f603])).

fof(f603,plain,
    ( l1_pre_topc(sK7)
    | ~ spl21_70 ),
    inference(avatar_component_clause,[],[f602])).

fof(f918,plain,
    ( ~ l1_pre_topc(sK7)
    | u1_pre_topc(sK7) = k1_zfmisc_1(u1_struct_0(sK7))
    | ~ spl21_76 ),
    inference(resolution,[],[f351,f624])).

fof(f624,plain,
    ( v1_tdlat_3(sK7)
    | ~ spl21_76 ),
    inference(avatar_component_clause,[],[f623])).

fof(f351,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = k1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(forward_demodulation,[],[f269,f284])).

fof(f269,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f169])).

fof(f1264,plain,
    ( spl21_194
    | ~ spl21_20
    | ~ spl21_28 ),
    inference(avatar_split_clause,[],[f921,f455,f427,f1262])).

fof(f1262,plain,
    ( spl21_194
  <=> u1_pre_topc(sK3) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_194])])).

fof(f455,plain,
    ( spl21_28
  <=> v1_tdlat_3(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_28])])).

fof(f921,plain,
    ( u1_pre_topc(sK3) = k1_zfmisc_1(u1_struct_0(sK3))
    | ~ spl21_20
    | ~ spl21_28 ),
    inference(subsumption_resolution,[],[f917,f428])).

fof(f917,plain,
    ( ~ l1_pre_topc(sK3)
    | u1_pre_topc(sK3) = k1_zfmisc_1(u1_struct_0(sK3))
    | ~ spl21_28 ),
    inference(resolution,[],[f351,f456])).

fof(f456,plain,
    ( v1_tdlat_3(sK3)
    | ~ spl21_28 ),
    inference(avatar_component_clause,[],[f455])).

fof(f1257,plain,
    ( spl21_192
    | ~ spl21_8
    | ~ spl21_16 ),
    inference(avatar_split_clause,[],[f920,f413,f385,f1255])).

fof(f1255,plain,
    ( spl21_192
  <=> u1_pre_topc(sK2) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_192])])).

fof(f413,plain,
    ( spl21_16
  <=> v1_tdlat_3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_16])])).

fof(f920,plain,
    ( u1_pre_topc(sK2) = k1_zfmisc_1(u1_struct_0(sK2))
    | ~ spl21_8
    | ~ spl21_16 ),
    inference(subsumption_resolution,[],[f916,f386])).

fof(f916,plain,
    ( ~ l1_pre_topc(sK2)
    | u1_pre_topc(sK2) = k1_zfmisc_1(u1_struct_0(sK2))
    | ~ spl21_16 ),
    inference(resolution,[],[f351,f414])).

fof(f414,plain,
    ( v1_tdlat_3(sK2)
    | ~ spl21_16 ),
    inference(avatar_component_clause,[],[f413])).

fof(f1232,plain,
    ( spl21_190
    | ~ spl21_136
    | ~ spl21_150
    | ~ spl21_152 ),
    inference(avatar_split_clause,[],[f1222,f1065,f1034,f833,f1230])).

fof(f1230,plain,
    ( spl21_190
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_190])])).

fof(f1222,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl21_136
    | ~ spl21_150
    | ~ spl21_152 ),
    inference(backward_demodulation,[],[f1218,f834])).

fof(f1213,plain,
    ( spl21_188
    | ~ spl21_177
    | ~ spl21_70
    | spl21_73
    | ~ spl21_76
    | ~ spl21_78 ),
    inference(avatar_split_clause,[],[f977,f630,f623,f609,f602,f1154,f1211])).

fof(f1211,plain,
    ( spl21_188
  <=> v7_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_188])])).

fof(f1154,plain,
    ( spl21_177
  <=> ~ v2_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_177])])).

fof(f609,plain,
    ( spl21_73
  <=> ~ v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_73])])).

fof(f630,plain,
    ( spl21_78
  <=> v2_tdlat_3(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_78])])).

fof(f977,plain,
    ( ~ v2_pre_topc(sK7)
    | v7_struct_0(sK7)
    | ~ spl21_70
    | ~ spl21_73
    | ~ spl21_76
    | ~ spl21_78 ),
    inference(subsumption_resolution,[],[f976,f603])).

fof(f976,plain,
    ( ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | v7_struct_0(sK7)
    | ~ spl21_73
    | ~ spl21_76
    | ~ spl21_78 ),
    inference(subsumption_resolution,[],[f975,f624])).

fof(f975,plain,
    ( ~ v2_pre_topc(sK7)
    | ~ v1_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7)
    | v7_struct_0(sK7)
    | ~ spl21_73
    | ~ spl21_78 ),
    inference(subsumption_resolution,[],[f969,f610])).

fof(f610,plain,
    ( ~ v2_struct_0(sK7)
    | ~ spl21_73 ),
    inference(avatar_component_clause,[],[f609])).

fof(f969,plain,
    ( v2_struct_0(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ v1_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7)
    | v7_struct_0(sK7)
    | ~ spl21_78 ),
    inference(resolution,[],[f271,f631])).

fof(f631,plain,
    ( v2_tdlat_3(sK7)
    | ~ spl21_78 ),
    inference(avatar_component_clause,[],[f630])).

fof(f271,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f173])).

fof(f173,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f172])).

fof(f172,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',cc2_tex_1)).

fof(f1199,plain,
    ( ~ spl21_165
    | spl21_184
    | spl21_186
    | spl21_149
    | ~ spl21_150 ),
    inference(avatar_split_clause,[],[f1057,f1034,f979,f1197,f1191,f1107])).

fof(f1107,plain,
    ( spl21_165
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_165])])).

fof(f1191,plain,
    ( spl21_184
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_184])])).

fof(f1197,plain,
    ( spl21_186
  <=> m1_subset_1(sK10(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_186])])).

fof(f979,plain,
    ( spl21_149
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_149])])).

fof(f1057,plain,
    ( m1_subset_1(sK10(sK0),u1_pre_topc(sK0))
    | v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl21_149
    | ~ spl21_150 ),
    inference(subsumption_resolution,[],[f1042,f980])).

fof(f980,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl21_149 ),
    inference(avatar_component_clause,[],[f979])).

fof(f1042,plain,
    ( m1_subset_1(sK10(sK0),u1_pre_topc(sK0))
    | v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl21_150 ),
    inference(superposition,[],[f307,f1035])).

fof(f307,plain,(
    ! [X0] :
      ( m1_subset_1(sK10(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f215])).

fof(f215,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f214])).

fof(f214,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f138])).

fof(f138,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc4_tex_2)).

fof(f1185,plain,
    ( spl21_180
    | ~ spl21_183
    | ~ spl21_108
    | spl21_111
    | ~ spl21_112 ),
    inference(avatar_split_clause,[],[f878,f749,f742,f735,f1183,f1177])).

fof(f1177,plain,
    ( spl21_180
  <=> v1_tdlat_3(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_180])])).

fof(f1183,plain,
    ( spl21_183
  <=> ~ v2_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_183])])).

fof(f735,plain,
    ( spl21_108
  <=> l1_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_108])])).

fof(f742,plain,
    ( spl21_111
  <=> ~ v2_struct_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_111])])).

fof(f749,plain,
    ( spl21_112
  <=> v7_struct_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_112])])).

fof(f878,plain,
    ( ~ v2_pre_topc(sK17)
    | v1_tdlat_3(sK17)
    | ~ spl21_108
    | ~ spl21_111
    | ~ spl21_112 ),
    inference(subsumption_resolution,[],[f877,f736])).

fof(f736,plain,
    ( l1_pre_topc(sK17)
    | ~ spl21_108 ),
    inference(avatar_component_clause,[],[f735])).

fof(f877,plain,
    ( ~ v2_pre_topc(sK17)
    | v1_tdlat_3(sK17)
    | ~ l1_pre_topc(sK17)
    | ~ spl21_111
    | ~ spl21_112 ),
    inference(subsumption_resolution,[],[f873,f743])).

fof(f743,plain,
    ( ~ v2_struct_0(sK17)
    | ~ spl21_111 ),
    inference(avatar_component_clause,[],[f742])).

fof(f873,plain,
    ( v2_struct_0(sK17)
    | ~ v2_pre_topc(sK17)
    | v1_tdlat_3(sK17)
    | ~ l1_pre_topc(sK17)
    | ~ spl21_112 ),
    inference(resolution,[],[f274,f750])).

fof(f750,plain,
    ( v7_struct_0(sK17)
    | ~ spl21_112 ),
    inference(avatar_component_clause,[],[f749])).

fof(f274,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f177])).

fof(f177,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f176])).

fof(f176,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',cc3_tex_1)).

fof(f1172,plain,
    ( ~ spl21_70
    | ~ spl21_76
    | spl21_177 ),
    inference(avatar_contradiction_clause,[],[f1171])).

fof(f1171,plain,
    ( $false
    | ~ spl21_70
    | ~ spl21_76
    | ~ spl21_177 ),
    inference(subsumption_resolution,[],[f1170,f603])).

fof(f1170,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ spl21_76
    | ~ spl21_177 ),
    inference(subsumption_resolution,[],[f1169,f624])).

fof(f1169,plain,
    ( ~ v1_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ spl21_177 ),
    inference(resolution,[],[f1155,f277])).

fof(f277,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f181])).

fof(f181,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f180])).

fof(f180,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',cc1_tdlat_3)).

fof(f1155,plain,
    ( ~ v2_pre_topc(sK7)
    | ~ spl21_177 ),
    inference(avatar_component_clause,[],[f1154])).

fof(f1168,plain,
    ( ~ spl21_165
    | spl21_178
    | spl21_149
    | ~ spl21_150 ),
    inference(avatar_split_clause,[],[f1056,f1034,f979,f1166,f1107])).

fof(f1166,plain,
    ( spl21_178
  <=> m1_subset_1(sK9(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_178])])).

fof(f1056,plain,
    ( m1_subset_1(sK9(sK0),u1_pre_topc(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl21_149
    | ~ spl21_150 ),
    inference(subsumption_resolution,[],[f1041,f980])).

fof(f1041,plain,
    ( m1_subset_1(sK9(sK0),u1_pre_topc(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl21_150 ),
    inference(superposition,[],[f304,f1035])).

fof(f304,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f211])).

fof(f211,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f210])).

fof(f210,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f135])).

fof(f135,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc4_struct_0)).

fof(f1161,plain,
    ( ~ spl21_70
    | ~ spl21_76
    | spl21_175 ),
    inference(avatar_contradiction_clause,[],[f1160])).

fof(f1160,plain,
    ( $false
    | ~ spl21_70
    | ~ spl21_76
    | ~ spl21_175 ),
    inference(subsumption_resolution,[],[f1159,f603])).

fof(f1159,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ spl21_76
    | ~ spl21_175 ),
    inference(subsumption_resolution,[],[f1158,f624])).

fof(f1158,plain,
    ( ~ v1_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ spl21_175 ),
    inference(resolution,[],[f1146,f278])).

fof(f278,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f183])).

fof(f183,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f182])).

fof(f182,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v3_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',cc3_tdlat_3)).

fof(f1146,plain,
    ( ~ v3_tdlat_3(sK7)
    | ~ spl21_175 ),
    inference(avatar_component_clause,[],[f1145])).

fof(f1145,plain,
    ( spl21_175
  <=> ~ v3_tdlat_3(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_175])])).

fof(f1156,plain,
    ( spl21_174
    | ~ spl21_177
    | ~ spl21_70
    | spl21_73
    | ~ spl21_78 ),
    inference(avatar_split_clause,[],[f871,f630,f609,f602,f1154,f1148])).

fof(f1148,plain,
    ( spl21_174
  <=> v3_tdlat_3(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_174])])).

fof(f871,plain,
    ( ~ v2_pre_topc(sK7)
    | v3_tdlat_3(sK7)
    | ~ spl21_70
    | ~ spl21_73
    | ~ spl21_78 ),
    inference(subsumption_resolution,[],[f870,f603])).

fof(f870,plain,
    ( ~ v2_pre_topc(sK7)
    | v3_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ spl21_73
    | ~ spl21_78 ),
    inference(subsumption_resolution,[],[f863,f610])).

fof(f863,plain,
    ( v2_struct_0(sK7)
    | ~ v2_pre_topc(sK7)
    | v3_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ spl21_78 ),
    inference(resolution,[],[f273,f631])).

fof(f273,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f175])).

fof(f175,plain,(
    ! [X0] :
      ( ( ~ v2_tdlat_3(X0)
        & ~ v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f174])).

fof(f174,plain,(
    ! [X0] :
      ( ( ~ v2_tdlat_3(X0)
        & ~ v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ~ v2_tdlat_3(X0)
          & ~ v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',cc5_tex_1)).

fof(f1139,plain,
    ( ~ spl21_6
    | spl21_165 ),
    inference(avatar_contradiction_clause,[],[f1138])).

fof(f1138,plain,
    ( $false
    | ~ spl21_6
    | ~ spl21_165 ),
    inference(subsumption_resolution,[],[f1137,f379])).

fof(f379,plain,
    ( l1_pre_topc(sK0)
    | ~ spl21_6 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl21_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_6])])).

fof(f1137,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl21_165 ),
    inference(resolution,[],[f1108,f350])).

fof(f350,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',dt_l1_pre_topc)).

fof(f1108,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl21_165 ),
    inference(avatar_component_clause,[],[f1107])).

fof(f1136,plain,
    ( spl21_172
    | ~ spl21_8
    | spl21_11
    | ~ spl21_14
    | ~ spl21_16
    | ~ spl21_18 ),
    inference(avatar_split_clause,[],[f974,f420,f413,f406,f392,f385,f1134])).

fof(f1134,plain,
    ( spl21_172
  <=> v7_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_172])])).

fof(f392,plain,
    ( spl21_11
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_11])])).

fof(f406,plain,
    ( spl21_14
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_14])])).

fof(f420,plain,
    ( spl21_18
  <=> v2_tdlat_3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_18])])).

fof(f974,plain,
    ( v7_struct_0(sK2)
    | ~ spl21_8
    | ~ spl21_11
    | ~ spl21_14
    | ~ spl21_16
    | ~ spl21_18 ),
    inference(subsumption_resolution,[],[f973,f386])).

fof(f973,plain,
    ( ~ l1_pre_topc(sK2)
    | v7_struct_0(sK2)
    | ~ spl21_11
    | ~ spl21_14
    | ~ spl21_16
    | ~ spl21_18 ),
    inference(subsumption_resolution,[],[f972,f414])).

fof(f972,plain,
    ( ~ v1_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | v7_struct_0(sK2)
    | ~ spl21_11
    | ~ spl21_14
    | ~ spl21_18 ),
    inference(subsumption_resolution,[],[f971,f407])).

fof(f407,plain,
    ( v2_pre_topc(sK2)
    | ~ spl21_14 ),
    inference(avatar_component_clause,[],[f406])).

fof(f971,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ v1_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | v7_struct_0(sK2)
    | ~ spl21_11
    | ~ spl21_18 ),
    inference(subsumption_resolution,[],[f967,f393])).

fof(f393,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl21_11 ),
    inference(avatar_component_clause,[],[f392])).

fof(f967,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ v1_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | v7_struct_0(sK2)
    | ~ spl21_18 ),
    inference(resolution,[],[f271,f421])).

fof(f421,plain,
    ( v2_tdlat_3(sK2)
    | ~ spl21_18 ),
    inference(avatar_component_clause,[],[f420])).

fof(f1129,plain,
    ( ~ spl21_171
    | ~ spl21_58
    | spl21_61
    | ~ spl21_64
    | spl21_69 ),
    inference(avatar_split_clause,[],[f892,f595,f581,f567,f560,f1127])).

fof(f1127,plain,
    ( spl21_171
  <=> ~ v7_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_171])])).

fof(f560,plain,
    ( spl21_58
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_58])])).

fof(f567,plain,
    ( spl21_61
  <=> ~ v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_61])])).

fof(f581,plain,
    ( spl21_64
  <=> v2_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_64])])).

fof(f595,plain,
    ( spl21_69
  <=> ~ v2_tdlat_3(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_69])])).

fof(f892,plain,
    ( ~ v7_struct_0(sK6)
    | ~ spl21_58
    | ~ spl21_61
    | ~ spl21_64
    | ~ spl21_69 ),
    inference(subsumption_resolution,[],[f891,f561])).

fof(f561,plain,
    ( l1_pre_topc(sK6)
    | ~ spl21_58 ),
    inference(avatar_component_clause,[],[f560])).

fof(f891,plain,
    ( ~ v7_struct_0(sK6)
    | ~ l1_pre_topc(sK6)
    | ~ spl21_61
    | ~ spl21_64
    | ~ spl21_69 ),
    inference(subsumption_resolution,[],[f890,f582])).

fof(f582,plain,
    ( v2_pre_topc(sK6)
    | ~ spl21_64 ),
    inference(avatar_component_clause,[],[f581])).

fof(f890,plain,
    ( ~ v7_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | ~ spl21_61
    | ~ spl21_69 ),
    inference(subsumption_resolution,[],[f882,f568])).

fof(f568,plain,
    ( ~ v2_struct_0(sK6)
    | ~ spl21_61 ),
    inference(avatar_component_clause,[],[f567])).

fof(f882,plain,
    ( v2_struct_0(sK6)
    | ~ v7_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | ~ spl21_69 ),
    inference(resolution,[],[f276,f596])).

fof(f596,plain,
    ( ~ v2_tdlat_3(sK6)
    | ~ spl21_69 ),
    inference(avatar_component_clause,[],[f595])).

fof(f276,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v7_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f179])).

fof(f179,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f178])).

fof(f178,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',cc1_tex_1)).

fof(f1122,plain,
    ( ~ spl21_169
    | ~ spl21_44
    | spl21_47
    | ~ spl21_50
    | spl21_55 ),
    inference(avatar_split_clause,[],[f889,f546,f532,f518,f511,f1120])).

fof(f1120,plain,
    ( spl21_169
  <=> ~ v7_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_169])])).

fof(f518,plain,
    ( spl21_47
  <=> ~ v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_47])])).

fof(f532,plain,
    ( spl21_50
  <=> v2_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_50])])).

fof(f546,plain,
    ( spl21_55
  <=> ~ v2_tdlat_3(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_55])])).

fof(f889,plain,
    ( ~ v7_struct_0(sK5)
    | ~ spl21_44
    | ~ spl21_47
    | ~ spl21_50
    | ~ spl21_55 ),
    inference(subsumption_resolution,[],[f888,f512])).

fof(f888,plain,
    ( ~ v7_struct_0(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ spl21_47
    | ~ spl21_50
    | ~ spl21_55 ),
    inference(subsumption_resolution,[],[f887,f533])).

fof(f533,plain,
    ( v2_pre_topc(sK5)
    | ~ spl21_50 ),
    inference(avatar_component_clause,[],[f532])).

fof(f887,plain,
    ( ~ v7_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ spl21_47
    | ~ spl21_55 ),
    inference(subsumption_resolution,[],[f881,f519])).

fof(f519,plain,
    ( ~ v2_struct_0(sK5)
    | ~ spl21_47 ),
    inference(avatar_component_clause,[],[f518])).

fof(f881,plain,
    ( v2_struct_0(sK5)
    | ~ v7_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ spl21_55 ),
    inference(resolution,[],[f276,f547])).

fof(f547,plain,
    ( ~ v2_tdlat_3(sK5)
    | ~ spl21_55 ),
    inference(avatar_component_clause,[],[f546])).

fof(f1115,plain,
    ( ~ spl21_165
    | spl21_166
    | spl21_149
    | ~ spl21_150 ),
    inference(avatar_split_clause,[],[f1055,f1034,f979,f1113,f1107])).

fof(f1113,plain,
    ( spl21_166
  <=> m1_subset_1(sK8(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_166])])).

fof(f1055,plain,
    ( m1_subset_1(sK8(sK0),u1_pre_topc(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl21_149
    | ~ spl21_150 ),
    inference(subsumption_resolution,[],[f1040,f980])).

fof(f1040,plain,
    ( m1_subset_1(sK8(sK0),u1_pre_topc(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl21_150 ),
    inference(superposition,[],[f301,f1035])).

fof(f301,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f209])).

fof(f209,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f208])).

fof(f208,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f113])).

fof(f113,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc20_struct_0)).

fof(f1102,plain,
    ( ~ spl21_163
    | ~ spl21_20
    | spl21_23
    | ~ spl21_26
    | spl21_31 ),
    inference(avatar_split_clause,[],[f886,f462,f448,f434,f427,f1100])).

fof(f1100,plain,
    ( spl21_163
  <=> ~ v7_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_163])])).

fof(f434,plain,
    ( spl21_23
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_23])])).

fof(f448,plain,
    ( spl21_26
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_26])])).

fof(f462,plain,
    ( spl21_31
  <=> ~ v2_tdlat_3(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_31])])).

fof(f886,plain,
    ( ~ v7_struct_0(sK3)
    | ~ spl21_20
    | ~ spl21_23
    | ~ spl21_26
    | ~ spl21_31 ),
    inference(subsumption_resolution,[],[f885,f428])).

fof(f885,plain,
    ( ~ v7_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl21_23
    | ~ spl21_26
    | ~ spl21_31 ),
    inference(subsumption_resolution,[],[f884,f449])).

fof(f449,plain,
    ( v2_pre_topc(sK3)
    | ~ spl21_26 ),
    inference(avatar_component_clause,[],[f448])).

fof(f884,plain,
    ( ~ v7_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl21_23
    | ~ spl21_31 ),
    inference(subsumption_resolution,[],[f880,f435])).

fof(f435,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl21_23 ),
    inference(avatar_component_clause,[],[f434])).

fof(f880,plain,
    ( v2_struct_0(sK3)
    | ~ v7_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl21_31 ),
    inference(resolution,[],[f276,f463])).

fof(f463,plain,
    ( ~ v2_tdlat_3(sK3)
    | ~ spl21_31 ),
    inference(avatar_component_clause,[],[f462])).

fof(f1095,plain,
    ( spl21_160
    | ~ spl21_98
    | spl21_101
    | ~ spl21_102
    | ~ spl21_106 ),
    inference(avatar_split_clause,[],[f876,f728,f714,f707,f700,f1093])).

fof(f1093,plain,
    ( spl21_160
  <=> v1_tdlat_3(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_160])])).

fof(f700,plain,
    ( spl21_98
  <=> l1_pre_topc(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_98])])).

fof(f707,plain,
    ( spl21_101
  <=> ~ v2_struct_0(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_101])])).

fof(f714,plain,
    ( spl21_102
  <=> v7_struct_0(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_102])])).

fof(f728,plain,
    ( spl21_106
  <=> v2_pre_topc(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_106])])).

fof(f876,plain,
    ( v1_tdlat_3(sK16)
    | ~ spl21_98
    | ~ spl21_101
    | ~ spl21_102
    | ~ spl21_106 ),
    inference(subsumption_resolution,[],[f875,f701])).

fof(f701,plain,
    ( l1_pre_topc(sK16)
    | ~ spl21_98 ),
    inference(avatar_component_clause,[],[f700])).

fof(f875,plain,
    ( v1_tdlat_3(sK16)
    | ~ l1_pre_topc(sK16)
    | ~ spl21_101
    | ~ spl21_102
    | ~ spl21_106 ),
    inference(subsumption_resolution,[],[f874,f729])).

fof(f729,plain,
    ( v2_pre_topc(sK16)
    | ~ spl21_106 ),
    inference(avatar_component_clause,[],[f728])).

fof(f874,plain,
    ( ~ v2_pre_topc(sK16)
    | v1_tdlat_3(sK16)
    | ~ l1_pre_topc(sK16)
    | ~ spl21_101
    | ~ spl21_102 ),
    inference(subsumption_resolution,[],[f872,f708])).

fof(f708,plain,
    ( ~ v2_struct_0(sK16)
    | ~ spl21_101 ),
    inference(avatar_component_clause,[],[f707])).

fof(f872,plain,
    ( v2_struct_0(sK16)
    | ~ v2_pre_topc(sK16)
    | v1_tdlat_3(sK16)
    | ~ l1_pre_topc(sK16)
    | ~ spl21_102 ),
    inference(resolution,[],[f274,f715])).

fof(f715,plain,
    ( v7_struct_0(sK16)
    | ~ spl21_102 ),
    inference(avatar_component_clause,[],[f714])).

fof(f1088,plain,
    ( spl21_158
    | ~ spl21_32
    | spl21_35
    | ~ spl21_38
    | ~ spl21_42 ),
    inference(avatar_split_clause,[],[f869,f504,f490,f476,f469,f1086])).

fof(f1086,plain,
    ( spl21_158
  <=> v3_tdlat_3(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_158])])).

fof(f476,plain,
    ( spl21_35
  <=> ~ v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_35])])).

fof(f490,plain,
    ( spl21_38
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_38])])).

fof(f504,plain,
    ( spl21_42
  <=> v2_tdlat_3(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_42])])).

fof(f869,plain,
    ( v3_tdlat_3(sK4)
    | ~ spl21_32
    | ~ spl21_35
    | ~ spl21_38
    | ~ spl21_42 ),
    inference(subsumption_resolution,[],[f868,f470])).

fof(f868,plain,
    ( v3_tdlat_3(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl21_35
    | ~ spl21_38
    | ~ spl21_42 ),
    inference(subsumption_resolution,[],[f867,f491])).

fof(f491,plain,
    ( v2_pre_topc(sK4)
    | ~ spl21_38 ),
    inference(avatar_component_clause,[],[f490])).

fof(f867,plain,
    ( ~ v2_pre_topc(sK4)
    | v3_tdlat_3(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl21_35
    | ~ spl21_42 ),
    inference(subsumption_resolution,[],[f862,f477])).

fof(f477,plain,
    ( ~ v2_struct_0(sK4)
    | ~ spl21_35 ),
    inference(avatar_component_clause,[],[f476])).

fof(f862,plain,
    ( v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | v3_tdlat_3(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl21_42 ),
    inference(resolution,[],[f273,f505])).

fof(f505,plain,
    ( v2_tdlat_3(sK4)
    | ~ spl21_42 ),
    inference(avatar_component_clause,[],[f504])).

fof(f1081,plain,
    ( spl21_156
    | ~ spl21_8
    | spl21_11
    | ~ spl21_14
    | ~ spl21_18 ),
    inference(avatar_split_clause,[],[f866,f420,f406,f392,f385,f1079])).

fof(f1079,plain,
    ( spl21_156
  <=> v3_tdlat_3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_156])])).

fof(f866,plain,
    ( v3_tdlat_3(sK2)
    | ~ spl21_8
    | ~ spl21_11
    | ~ spl21_14
    | ~ spl21_18 ),
    inference(subsumption_resolution,[],[f865,f386])).

fof(f865,plain,
    ( v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl21_11
    | ~ spl21_14
    | ~ spl21_18 ),
    inference(subsumption_resolution,[],[f864,f407])).

fof(f864,plain,
    ( ~ v2_pre_topc(sK2)
    | v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl21_11
    | ~ spl21_18 ),
    inference(subsumption_resolution,[],[f861,f393])).

fof(f861,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl21_18 ),
    inference(resolution,[],[f273,f421])).

fof(f1074,plain,
    ( spl21_146
    | ~ spl21_155
    | ~ spl21_0
    | ~ spl21_136 ),
    inference(avatar_split_clause,[],[f910,f833,f357,f1072,f927])).

fof(f927,plain,
    ( spl21_146
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_146])])).

fof(f1072,plain,
    ( spl21_155
  <=> ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_155])])).

fof(f910,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(sK1)
    | ~ spl21_0
    | ~ spl21_136 ),
    inference(subsumption_resolution,[],[f909,f358])).

fof(f909,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl21_136 ),
    inference(superposition,[],[f292,f834])).

fof(f292,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f195])).

fof(f195,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f194])).

fof(f194,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f93])).

fof(f93,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',fc7_pre_topc)).

fof(f1067,plain,
    ( spl21_152
    | ~ spl21_6
    | ~ spl21_150 ),
    inference(avatar_split_clause,[],[f1052,f1034,f378,f1065])).

fof(f1052,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(u1_pre_topc(sK0)))
    | ~ spl21_6
    | ~ spl21_150 ),
    inference(subsumption_resolution,[],[f1037,f379])).

fof(f1037,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl21_150 ),
    inference(superposition,[],[f295,f1035])).

fof(f295,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f198])).

fof(f198,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f80])).

fof(f80,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',dt_u1_pre_topc)).

fof(f1036,plain,
    ( spl21_150
    | ~ spl21_2
    | ~ spl21_6 ),
    inference(avatar_split_clause,[],[f919,f378,f364,f1034])).

fof(f364,plain,
    ( spl21_2
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_2])])).

fof(f919,plain,
    ( u1_pre_topc(sK0) = k1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl21_2
    | ~ spl21_6 ),
    inference(subsumption_resolution,[],[f915,f379])).

fof(f915,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_pre_topc(sK0) = k1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl21_2 ),
    inference(resolution,[],[f351,f365])).

fof(f365,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl21_2 ),
    inference(avatar_component_clause,[],[f364])).

fof(f984,plain,
    ( spl21_148
    | ~ spl21_6
    | spl21_145 ),
    inference(avatar_split_clause,[],[f964,f902,f378,f982])).

fof(f982,plain,
    ( spl21_148
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_148])])).

fof(f902,plain,
    ( spl21_145
  <=> ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_145])])).

fof(f964,plain,
    ( v2_struct_0(sK0)
    | ~ spl21_6
    | ~ spl21_145 ),
    inference(subsumption_resolution,[],[f962,f379])).

fof(f962,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl21_145 ),
    inference(resolution,[],[f903,f293])).

fof(f293,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f195])).

fof(f903,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl21_145 ),
    inference(avatar_component_clause,[],[f902])).

fof(f929,plain,
    ( spl21_146
    | ~ spl21_0
    | ~ spl21_136
    | spl21_145 ),
    inference(avatar_split_clause,[],[f913,f902,f833,f357,f927])).

fof(f913,plain,
    ( v2_struct_0(sK1)
    | ~ spl21_0
    | ~ spl21_136
    | ~ spl21_145 ),
    inference(subsumption_resolution,[],[f912,f358])).

fof(f912,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl21_136
    | ~ spl21_145 ),
    inference(subsumption_resolution,[],[f911,f903])).

fof(f911,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl21_136 ),
    inference(superposition,[],[f293,f834])).

fof(f907,plain,
    ( ~ spl21_143
    | spl21_144
    | ~ spl21_0
    | ~ spl21_136 ),
    inference(avatar_split_clause,[],[f894,f833,f357,f905,f899])).

fof(f899,plain,
    ( spl21_143
  <=> ~ v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_143])])).

fof(f905,plain,
    ( spl21_144
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_144])])).

fof(f894,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ spl21_0
    | ~ spl21_136 ),
    inference(subsumption_resolution,[],[f893,f358])).

fof(f893,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl21_136 ),
    inference(superposition,[],[f290,f834])).

fof(f290,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f193])).

fof(f193,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f192])).

fof(f192,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f91])).

fof(f91,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',fc6_pre_topc)).

fof(f860,plain,
    ( spl21_140
    | ~ spl21_0
    | ~ spl21_136 ),
    inference(avatar_split_clause,[],[f853,f833,f357,f858])).

fof(f858,plain,
    ( spl21_140
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_140])])).

fof(f853,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl21_0
    | ~ spl21_136 ),
    inference(subsumption_resolution,[],[f852,f358])).

fof(f852,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl21_136 ),
    inference(superposition,[],[f850,f834])).

fof(f850,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f295,f289])).

fof(f289,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f72])).

fof(f72,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',dt_g1_pre_topc)).

fof(f842,plain,(
    spl21_138 ),
    inference(avatar_split_clause,[],[f285,f840])).

fof(f840,plain,
    ( spl21_138
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_138])])).

fof(f285,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

fof(f71,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',d2_xboole_0)).

fof(f835,plain,(
    spl21_136 ),
    inference(avatar_split_clause,[],[f228,f833])).

fof(f228,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f168])).

fof(f168,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f167])).

fof(f167,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v1_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v1_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v1_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v1_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',t17_tex_2)).

fof(f828,plain,(
    spl21_134 ),
    inference(avatar_split_clause,[],[f349,f826])).

fof(f826,plain,
    ( spl21_134
  <=> l1_pre_topc(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_134])])).

fof(f349,plain,(
    l1_pre_topc(sK20) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',existence_l1_pre_topc)).

fof(f821,plain,(
    spl21_132 ),
    inference(avatar_split_clause,[],[f348,f819])).

fof(f819,plain,
    ( spl21_132
  <=> v1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_132])])).

fof(f348,plain,(
    v1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f121])).

fof(f121,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc2_tex_1)).

fof(f814,plain,(
    ~ spl21_131 ),
    inference(avatar_split_clause,[],[f347,f812])).

fof(f812,plain,
    ( spl21_131
  <=> ~ v7_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_131])])).

fof(f347,plain,(
    ~ v7_struct_0(sK19) ),
    inference(cnf_transformation,[],[f121])).

fof(f807,plain,(
    ~ spl21_129 ),
    inference(avatar_split_clause,[],[f346,f805])).

fof(f805,plain,
    ( spl21_129
  <=> ~ v2_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_129])])).

fof(f346,plain,(
    ~ v2_struct_0(sK19) ),
    inference(cnf_transformation,[],[f121])).

fof(f800,plain,(
    spl21_126 ),
    inference(avatar_split_clause,[],[f345,f798])).

fof(f798,plain,
    ( spl21_126
  <=> l1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_126])])).

fof(f345,plain,(
    l1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f121])).

fof(f793,plain,(
    spl21_124 ),
    inference(avatar_split_clause,[],[f344,f791])).

fof(f791,plain,
    ( spl21_124
  <=> v2_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_124])])).

fof(f344,plain,(
    v2_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f137])).

fof(f137,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc4_tex_1)).

fof(f786,plain,(
    spl21_122 ),
    inference(avatar_split_clause,[],[f343,f784])).

fof(f784,plain,
    ( spl21_122
  <=> v1_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_122])])).

fof(f343,plain,(
    v1_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f137])).

fof(f779,plain,(
    ~ spl21_121 ),
    inference(avatar_split_clause,[],[f342,f777])).

fof(f777,plain,
    ( spl21_121
  <=> ~ v7_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_121])])).

fof(f342,plain,(
    ~ v7_struct_0(sK18) ),
    inference(cnf_transformation,[],[f137])).

fof(f772,plain,(
    ~ spl21_119 ),
    inference(avatar_split_clause,[],[f341,f770])).

fof(f770,plain,
    ( spl21_119
  <=> ~ v2_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_119])])).

fof(f341,plain,(
    ~ v2_struct_0(sK18) ),
    inference(cnf_transformation,[],[f137])).

fof(f765,plain,(
    spl21_116 ),
    inference(avatar_split_clause,[],[f340,f763])).

fof(f763,plain,
    ( spl21_116
  <=> l1_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_116])])).

fof(f340,plain,(
    l1_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f137])).

fof(f758,plain,(
    spl21_114 ),
    inference(avatar_split_clause,[],[f339,f756])).

fof(f756,plain,
    ( spl21_114
  <=> v1_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_114])])).

fof(f339,plain,(
    v1_pre_topc(sK17) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc1_tex_1)).

fof(f751,plain,(
    spl21_112 ),
    inference(avatar_split_clause,[],[f338,f749])).

fof(f338,plain,(
    v7_struct_0(sK17) ),
    inference(cnf_transformation,[],[f109])).

fof(f744,plain,(
    ~ spl21_111 ),
    inference(avatar_split_clause,[],[f337,f742])).

fof(f337,plain,(
    ~ v2_struct_0(sK17) ),
    inference(cnf_transformation,[],[f109])).

fof(f737,plain,(
    spl21_108 ),
    inference(avatar_split_clause,[],[f336,f735])).

fof(f336,plain,(
    l1_pre_topc(sK17) ),
    inference(cnf_transformation,[],[f109])).

fof(f730,plain,(
    spl21_106 ),
    inference(avatar_split_clause,[],[f335,f728])).

fof(f335,plain,(
    v2_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f130])).

fof(f130,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc3_tex_1)).

fof(f723,plain,(
    spl21_104 ),
    inference(avatar_split_clause,[],[f334,f721])).

fof(f721,plain,
    ( spl21_104
  <=> v1_pre_topc(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_104])])).

fof(f334,plain,(
    v1_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f130])).

fof(f716,plain,(
    spl21_102 ),
    inference(avatar_split_clause,[],[f333,f714])).

fof(f333,plain,(
    v7_struct_0(sK16) ),
    inference(cnf_transformation,[],[f130])).

fof(f709,plain,(
    ~ spl21_101 ),
    inference(avatar_split_clause,[],[f332,f707])).

fof(f332,plain,(
    ~ v2_struct_0(sK16) ),
    inference(cnf_transformation,[],[f130])).

fof(f702,plain,(
    spl21_98 ),
    inference(avatar_split_clause,[],[f331,f700])).

fof(f331,plain,(
    l1_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f130])).

fof(f695,plain,(
    spl21_96 ),
    inference(avatar_split_clause,[],[f330,f693])).

fof(f693,plain,
    ( spl21_96
  <=> v2_pre_topc(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_96])])).

fof(f330,plain,(
    v2_pre_topc(sK15) ),
    inference(cnf_transformation,[],[f116])).

fof(f116,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc2_pre_topc)).

fof(f688,plain,(
    spl21_94 ),
    inference(avatar_split_clause,[],[f329,f686])).

fof(f686,plain,
    ( spl21_94
  <=> v1_pre_topc(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_94])])).

fof(f329,plain,(
    v1_pre_topc(sK15) ),
    inference(cnf_transformation,[],[f116])).

fof(f681,plain,(
    ~ spl21_93 ),
    inference(avatar_split_clause,[],[f328,f679])).

fof(f679,plain,
    ( spl21_93
  <=> ~ v2_struct_0(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_93])])).

fof(f328,plain,(
    ~ v2_struct_0(sK15) ),
    inference(cnf_transformation,[],[f116])).

fof(f674,plain,(
    spl21_90 ),
    inference(avatar_split_clause,[],[f327,f672])).

fof(f672,plain,
    ( spl21_90
  <=> l1_pre_topc(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_90])])).

fof(f327,plain,(
    l1_pre_topc(sK15) ),
    inference(cnf_transformation,[],[f116])).

fof(f667,plain,(
    spl21_88 ),
    inference(avatar_split_clause,[],[f326,f665])).

fof(f665,plain,
    ( spl21_88
  <=> v1_pre_topc(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_88])])).

fof(f326,plain,(
    v1_pre_topc(sK14) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc1_pre_topc)).

fof(f660,plain,(
    spl21_86 ),
    inference(avatar_split_clause,[],[f325,f658])).

fof(f658,plain,
    ( spl21_86
  <=> l1_pre_topc(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_86])])).

fof(f325,plain,(
    l1_pre_topc(sK14) ),
    inference(cnf_transformation,[],[f104])).

fof(f653,plain,(
    spl21_84 ),
    inference(avatar_split_clause,[],[f324,f651])).

fof(f651,plain,
    ( spl21_84
  <=> v1_pre_topc(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_84])])).

fof(f324,plain,(
    v1_pre_topc(sK13) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc11_pre_topc)).

fof(f646,plain,(
    spl21_82 ),
    inference(avatar_split_clause,[],[f323,f644])).

fof(f644,plain,
    ( spl21_82
  <=> v2_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_82])])).

fof(f323,plain,(
    v2_struct_0(sK13) ),
    inference(cnf_transformation,[],[f101])).

fof(f639,plain,(
    spl21_80 ),
    inference(avatar_split_clause,[],[f322,f637])).

fof(f637,plain,
    ( spl21_80
  <=> l1_pre_topc(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_80])])).

fof(f322,plain,(
    l1_pre_topc(sK13) ),
    inference(cnf_transformation,[],[f101])).

fof(f632,plain,(
    spl21_78 ),
    inference(avatar_split_clause,[],[f267,f630])).

fof(f267,plain,(
    v2_tdlat_3(sK7) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,axiom,(
    ? [X0] :
      ( v2_tdlat_3(X0)
      & v1_tdlat_3(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc1_tdlat_3)).

fof(f625,plain,(
    spl21_76 ),
    inference(avatar_split_clause,[],[f266,f623])).

fof(f266,plain,(
    v1_tdlat_3(sK7) ),
    inference(cnf_transformation,[],[f108])).

fof(f618,plain,(
    spl21_74 ),
    inference(avatar_split_clause,[],[f265,f616])).

fof(f616,plain,
    ( spl21_74
  <=> v1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_74])])).

fof(f265,plain,(
    v1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f108])).

fof(f611,plain,(
    ~ spl21_73 ),
    inference(avatar_split_clause,[],[f264,f609])).

fof(f264,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f108])).

fof(f604,plain,(
    spl21_70 ),
    inference(avatar_split_clause,[],[f263,f602])).

fof(f263,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f108])).

fof(f597,plain,(
    ~ spl21_69 ),
    inference(avatar_split_clause,[],[f262,f595])).

fof(f262,plain,(
    ~ v2_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f150])).

fof(f150,axiom,(
    ? [X0] :
      ( ~ v2_tdlat_3(X0)
      & ~ v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc7_tex_1)).

fof(f590,plain,(
    ~ spl21_67 ),
    inference(avatar_split_clause,[],[f261,f588])).

fof(f588,plain,
    ( spl21_67
  <=> ~ v1_tdlat_3(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_67])])).

fof(f261,plain,(
    ~ v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f150])).

fof(f583,plain,(
    spl21_64 ),
    inference(avatar_split_clause,[],[f260,f581])).

fof(f260,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f150])).

fof(f576,plain,(
    spl21_62 ),
    inference(avatar_split_clause,[],[f259,f574])).

fof(f574,plain,
    ( spl21_62
  <=> v1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_62])])).

fof(f259,plain,(
    v1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f150])).

fof(f569,plain,(
    ~ spl21_61 ),
    inference(avatar_split_clause,[],[f258,f567])).

fof(f258,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f150])).

fof(f562,plain,(
    spl21_58 ),
    inference(avatar_split_clause,[],[f257,f560])).

fof(f257,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f150])).

fof(f555,plain,(
    spl21_56 ),
    inference(avatar_split_clause,[],[f256,f553])).

fof(f553,plain,
    ( spl21_56
  <=> v3_tdlat_3(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_56])])).

fof(f256,plain,(
    v3_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f153])).

fof(f153,axiom,(
    ? [X0] :
      ( v3_tdlat_3(X0)
      & ~ v2_tdlat_3(X0)
      & ~ v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc8_tex_1)).

fof(f548,plain,(
    ~ spl21_55 ),
    inference(avatar_split_clause,[],[f255,f546])).

fof(f255,plain,(
    ~ v2_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f153])).

fof(f541,plain,(
    ~ spl21_53 ),
    inference(avatar_split_clause,[],[f254,f539])).

fof(f539,plain,
    ( spl21_53
  <=> ~ v1_tdlat_3(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_53])])).

fof(f254,plain,(
    ~ v1_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f153])).

fof(f534,plain,(
    spl21_50 ),
    inference(avatar_split_clause,[],[f253,f532])).

fof(f253,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f153])).

fof(f527,plain,(
    spl21_48 ),
    inference(avatar_split_clause,[],[f252,f525])).

fof(f252,plain,(
    v1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f153])).

fof(f520,plain,(
    ~ spl21_47 ),
    inference(avatar_split_clause,[],[f251,f518])).

fof(f251,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f153])).

fof(f513,plain,(
    spl21_44 ),
    inference(avatar_split_clause,[],[f250,f511])).

fof(f250,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f153])).

fof(f506,plain,(
    spl21_42 ),
    inference(avatar_split_clause,[],[f249,f504])).

fof(f249,plain,(
    v2_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f145])).

fof(f145,axiom,(
    ? [X0] :
      ( v2_tdlat_3(X0)
      & ~ v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc6_tex_1)).

fof(f499,plain,(
    ~ spl21_41 ),
    inference(avatar_split_clause,[],[f248,f497])).

fof(f497,plain,
    ( spl21_41
  <=> ~ v1_tdlat_3(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_41])])).

fof(f248,plain,(
    ~ v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f145])).

fof(f492,plain,(
    spl21_38 ),
    inference(avatar_split_clause,[],[f247,f490])).

fof(f247,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f145])).

fof(f485,plain,(
    spl21_36 ),
    inference(avatar_split_clause,[],[f246,f483])).

fof(f246,plain,(
    v1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f145])).

fof(f478,plain,(
    ~ spl21_35 ),
    inference(avatar_split_clause,[],[f245,f476])).

fof(f245,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f145])).

fof(f471,plain,(
    spl21_32 ),
    inference(avatar_split_clause,[],[f244,f469])).

fof(f244,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f145])).

fof(f464,plain,(
    ~ spl21_31 ),
    inference(avatar_split_clause,[],[f243,f462])).

fof(f243,plain,(
    ~ v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f140])).

fof(f140,axiom,(
    ? [X0] :
      ( ~ v2_tdlat_3(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc5_tex_1)).

fof(f457,plain,(
    spl21_28 ),
    inference(avatar_split_clause,[],[f242,f455])).

fof(f242,plain,(
    v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f140])).

fof(f450,plain,(
    spl21_26 ),
    inference(avatar_split_clause,[],[f241,f448])).

fof(f241,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f140])).

fof(f443,plain,(
    spl21_24 ),
    inference(avatar_split_clause,[],[f240,f441])).

fof(f240,plain,(
    v1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f140])).

fof(f436,plain,(
    ~ spl21_23 ),
    inference(avatar_split_clause,[],[f239,f434])).

fof(f239,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f140])).

fof(f429,plain,(
    spl21_20 ),
    inference(avatar_split_clause,[],[f238,f427])).

fof(f238,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f140])).

fof(f422,plain,(
    spl21_18 ),
    inference(avatar_split_clause,[],[f237,f420])).

fof(f237,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f129])).

fof(f129,axiom,(
    ? [X0] :
      ( v2_tdlat_3(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t17_tex_2.p',rc3_tdlat_3)).

fof(f415,plain,(
    spl21_16 ),
    inference(avatar_split_clause,[],[f236,f413])).

fof(f236,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f129])).

fof(f408,plain,(
    spl21_14 ),
    inference(avatar_split_clause,[],[f235,f406])).

fof(f235,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f129])).

fof(f401,plain,(
    spl21_12 ),
    inference(avatar_split_clause,[],[f234,f399])).

fof(f234,plain,(
    v1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f129])).

fof(f394,plain,(
    ~ spl21_11 ),
    inference(avatar_split_clause,[],[f233,f392])).

fof(f233,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f129])).

fof(f387,plain,(
    spl21_8 ),
    inference(avatar_split_clause,[],[f232,f385])).

fof(f232,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f129])).

fof(f380,plain,(
    spl21_6 ),
    inference(avatar_split_clause,[],[f231,f378])).

fof(f231,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f168])).

fof(f373,plain,(
    ~ spl21_5 ),
    inference(avatar_split_clause,[],[f230,f371])).

fof(f230,plain,(
    ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f168])).

fof(f366,plain,(
    spl21_2 ),
    inference(avatar_split_clause,[],[f229,f364])).

fof(f229,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f168])).

fof(f359,plain,(
    spl21_0 ),
    inference(avatar_split_clause,[],[f227,f357])).

fof(f227,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f168])).
%------------------------------------------------------------------------------

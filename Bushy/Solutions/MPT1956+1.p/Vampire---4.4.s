%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t3_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:06 EDT 2019

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  532 (1533 expanded)
%              Number of leaves         :  140 ( 650 expanded)
%              Depth                    :   13
%              Number of atoms          : 1618 (4295 expanded)
%              Number of equality atoms :   48 ( 195 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1335,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f116,f123,f130,f137,f144,f151,f158,f165,f190,f201,f213,f221,f240,f247,f262,f281,f289,f309,f318,f325,f332,f350,f364,f376,f383,f392,f399,f423,f437,f450,f463,f472,f479,f491,f505,f518,f527,f534,f562,f566,f583,f600,f609,f616,f659,f673,f680,f687,f694,f703,f710,f732,f746,f760,f778,f782,f797,f814,f821,f836,f858,f859,f873,f880,f890,f897,f906,f913,f946,f953,f962,f969,f973,f986,f1000,f1016,f1025,f1041,f1048,f1057,f1061,f1068,f1077,f1084,f1090,f1107,f1124,f1133,f1140,f1141,f1145,f1205,f1214,f1227,f1293,f1301,f1308,f1324,f1329,f1334])).

fof(f1334,plain,
    ( spl5_88
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_8
    | spl5_211 ),
    inference(avatar_split_clause,[],[f1333,f1322,f135,f128,f114,f557])).

fof(f557,plain,
    ( spl5_88
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f114,plain,
    ( spl5_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f128,plain,
    ( spl5_6
  <=> v3_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f135,plain,
    ( spl5_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1322,plain,
    ( spl5_211
  <=> ~ r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_211])])).

fof(f1333,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_211 ),
    inference(subsumption_resolution,[],[f1332,f115])).

fof(f115,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1332,plain,
    ( ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_211 ),
    inference(subsumption_resolution,[],[f1331,f129])).

fof(f129,plain,
    ( v3_lattice3(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f1331,plain,
    ( ~ v3_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_8
    | ~ spl5_211 ),
    inference(subsumption_resolution,[],[f1330,f136])).

fof(f136,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f1330,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_211 ),
    inference(resolution,[],[f1323,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t17_yellow_0)).

fof(f1323,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ spl5_211 ),
    inference(avatar_component_clause,[],[f1322])).

fof(f1329,plain,
    ( spl5_88
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_8
    | spl5_209 ),
    inference(avatar_split_clause,[],[f1328,f1316,f135,f128,f114,f557])).

fof(f1316,plain,
    ( spl5_209
  <=> ~ r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_209])])).

fof(f1328,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_209 ),
    inference(subsumption_resolution,[],[f1327,f115])).

fof(f1327,plain,
    ( ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_209 ),
    inference(subsumption_resolution,[],[f1326,f129])).

fof(f1326,plain,
    ( ~ v3_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_8
    | ~ spl5_209 ),
    inference(subsumption_resolution,[],[f1325,f136])).

fof(f1325,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_209 ),
    inference(resolution,[],[f1317,f84])).

fof(f1317,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ spl5_209 ),
    inference(avatar_component_clause,[],[f1316])).

fof(f1324,plain,
    ( ~ spl5_209
    | ~ spl5_211
    | ~ spl5_8
    | ~ spl5_14
    | spl5_71 ),
    inference(avatar_split_clause,[],[f1311,f461,f156,f135,f1322,f1316])).

fof(f156,plain,
    ( spl5_14
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f461,plain,
    ( spl5_71
  <=> ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f1311,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ r2_yellow_0(sK0,sK1)
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_71 ),
    inference(subsumption_resolution,[],[f1310,f136])).

fof(f1310,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl5_14
    | ~ spl5_71 ),
    inference(subsumption_resolution,[],[f1309,f157])).

fof(f157,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f1309,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ r2_yellow_0(sK0,sK1)
    | ~ r1_tarski(sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl5_71 ),
    inference(resolution,[],[f462,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t35_yellow_0)).

fof(f462,plain,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ spl5_71 ),
    inference(avatar_component_clause,[],[f461])).

fof(f1308,plain,
    ( ~ spl5_8
    | ~ spl5_14
    | spl5_69
    | ~ spl5_206 ),
    inference(avatar_contradiction_clause,[],[f1307])).

fof(f1307,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_69
    | ~ spl5_206 ),
    inference(subsumption_resolution,[],[f1305,f157])).

fof(f1305,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl5_8
    | ~ spl5_69
    | ~ spl5_206 ),
    inference(resolution,[],[f1304,f456])).

fof(f456,plain,
    ( ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ spl5_69 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl5_69
  <=> ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f1304,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_8
    | ~ spl5_206 ),
    inference(subsumption_resolution,[],[f1302,f136])).

fof(f1302,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | ~ r1_tarski(X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl5_206 ),
    inference(resolution,[],[f1300,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',dt_k1_yellow_0)).

fof(f1300,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_206 ),
    inference(avatar_component_clause,[],[f1299])).

fof(f1299,plain,
    ( spl5_206
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_206])])).

fof(f1301,plain,
    ( spl5_88
    | spl5_206
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_204 ),
    inference(avatar_split_clause,[],[f1297,f1291,f135,f128,f114,f1299,f557])).

fof(f1291,plain,
    ( spl5_204
  <=> ! [X1,X0] :
        ( r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).

fof(f1297,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_204 ),
    inference(subsumption_resolution,[],[f1296,f115])).

fof(f1296,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_204 ),
    inference(subsumption_resolution,[],[f1295,f129])).

fof(f1295,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | ~ v3_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_8
    | ~ spl5_204 ),
    inference(subsumption_resolution,[],[f1294,f136])).

fof(f1294,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | ~ l1_orders_2(sK0)
        | ~ v3_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_204 ),
    inference(resolution,[],[f1292,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1292,plain,
    ( ! [X0,X1] :
        ( ~ r1_yellow_0(sK0,X1)
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1)) )
    | ~ spl5_204 ),
    inference(avatar_component_clause,[],[f1291])).

fof(f1293,plain,
    ( spl5_88
    | spl5_204
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_194 ),
    inference(avatar_split_clause,[],[f1248,f1143,f135,f128,f114,f1291,f557])).

fof(f1143,plain,
    ( spl5_194
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).

fof(f1248,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | ~ r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | ~ r1_tarski(X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_194 ),
    inference(subsumption_resolution,[],[f1247,f115])).

fof(f1247,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | ~ r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | ~ r1_tarski(X0,X1)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_194 ),
    inference(subsumption_resolution,[],[f1246,f129])).

fof(f1246,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | ~ r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | ~ r1_tarski(X0,X1)
        | ~ v3_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_8
    | ~ spl5_194 ),
    inference(subsumption_resolution,[],[f1245,f136])).

fof(f1245,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK0,k1_yellow_0(sK0,X0),k1_yellow_0(sK0,X1))
        | ~ r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | ~ r1_tarski(X0,X1)
        | ~ l1_orders_2(sK0)
        | ~ v3_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_8
    | ~ spl5_194 ),
    inference(resolution,[],[f1162,f83])).

fof(f1162,plain,
    ( ! [X2,X1] :
        ( ~ r1_yellow_0(sK0,X1)
        | r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2))
        | ~ r1_yellow_0(sK0,X2)
        | ~ m1_subset_1(k1_yellow_0(sK0,X1),u1_struct_0(sK0))
        | ~ r1_tarski(X1,X2) )
    | ~ spl5_8
    | ~ spl5_194 ),
    inference(subsumption_resolution,[],[f1160,f136])).

fof(f1160,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k1_yellow_0(sK0,X1),u1_struct_0(sK0))
        | r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2))
        | ~ r1_yellow_0(sK0,X2)
        | ~ r1_yellow_0(sK0,X1)
        | ~ r1_tarski(X1,X2)
        | ~ l1_orders_2(sK0) )
    | ~ spl5_8
    | ~ spl5_194 ),
    inference(resolution,[],[f1151,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t34_yellow_0)).

fof(f1151,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK0,X2,k1_yellow_0(sK0,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_orders_2(sK0,X2,k1_yellow_0(sK0,X3)) )
    | ~ spl5_8
    | ~ spl5_194 ),
    inference(subsumption_resolution,[],[f1147,f136])).

fof(f1147,plain,
    ( ! [X2,X3] :
        ( r3_orders_2(sK0,X2,k1_yellow_0(sK0,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,k1_yellow_0(sK0,X3))
        | ~ l1_orders_2(sK0) )
    | ~ spl5_194 ),
    inference(resolution,[],[f1144,f86])).

fof(f1144,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl5_194 ),
    inference(avatar_component_clause,[],[f1143])).

fof(f1227,plain,
    ( ~ spl5_203
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f1218,f1212,f1225])).

fof(f1225,plain,
    ( spl5_203
  <=> ~ r2_hidden(sK2,sK3(sK3(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_203])])).

fof(f1212,plain,
    ( spl5_200
  <=> r2_hidden(sK3(sK3(k1_zfmisc_1(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_200])])).

fof(f1218,plain,
    ( ~ r2_hidden(sK2,sK3(sK3(k1_zfmisc_1(sK1))))
    | ~ spl5_200 ),
    inference(resolution,[],[f1213,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',antisymmetry_r2_hidden)).

fof(f1213,plain,
    ( r2_hidden(sK3(sK3(k1_zfmisc_1(sK1))),sK2)
    | ~ spl5_200 ),
    inference(avatar_component_clause,[],[f1212])).

fof(f1214,plain,
    ( spl5_200
    | spl5_107
    | ~ spl5_198 ),
    inference(avatar_split_clause,[],[f1207,f1203,f654,f1212])).

fof(f654,plain,
    ( spl5_107
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f1203,plain,
    ( spl5_198
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_198])])).

fof(f1207,plain,
    ( r2_hidden(sK3(sK3(k1_zfmisc_1(sK1))),sK2)
    | ~ spl5_107
    | ~ spl5_198 ),
    inference(subsumption_resolution,[],[f1206,f655])).

fof(f655,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_107 ),
    inference(avatar_component_clause,[],[f654])).

fof(f1206,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(sK3(sK3(k1_zfmisc_1(sK1))),sK2)
    | ~ spl5_198 ),
    inference(resolution,[],[f1204,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t2_subset)).

fof(f1204,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(sK1))),sK2)
    | ~ spl5_198 ),
    inference(avatar_component_clause,[],[f1203])).

fof(f1205,plain,
    ( spl5_196
    | spl5_198
    | ~ spl5_14
    | spl5_103 ),
    inference(avatar_split_clause,[],[f1192,f642,f156,f1203,f1197])).

fof(f1197,plain,
    ( spl5_196
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_196])])).

fof(f642,plain,
    ( spl5_103
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f1192,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(sK1))),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(sK1)))
    | ~ spl5_14
    | ~ spl5_103 ),
    inference(subsumption_resolution,[],[f1186,f643])).

fof(f643,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_103 ),
    inference(avatar_component_clause,[],[f642])).

fof(f1186,plain,
    ( v1_xboole_0(sK1)
    | m1_subset_1(sK3(sK3(k1_zfmisc_1(sK1))),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(sK1)))
    | ~ spl5_14 ),
    inference(resolution,[],[f1179,f157])).

fof(f1179,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X0)
      | m1_subset_1(sK3(sK3(k1_zfmisc_1(X0))),X1)
      | v1_xboole_0(sK3(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f924,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t3_subset)).

fof(f924,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(sK3(k1_zfmisc_1(X1)))
      | v1_xboole_0(X1)
      | m1_subset_1(sK3(sK3(k1_zfmisc_1(X1))),X2) ) ),
    inference(resolution,[],[f634,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t4_subset)).

fof(f634,plain,(
    ! [X4] :
      ( r2_hidden(sK3(sK3(k1_zfmisc_1(X4))),X4)
      | v1_xboole_0(X4)
      | v1_xboole_0(sK3(k1_zfmisc_1(X4))) ) ),
    inference(resolution,[],[f404,f85])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',existence_m1_subset_1)).

fof(f404,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | v1_xboole_0(X3)
      | v1_xboole_0(X4)
      | r2_hidden(sK3(X3),X4) ) ),
    inference(resolution,[],[f248,f90])).

fof(f248,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f98,f175])).

fof(f175,plain,(
    ! [X8] :
      ( r2_hidden(sK3(X8),X8)
      | v1_xboole_0(X8) ) ),
    inference(resolution,[],[f90,f85])).

fof(f1145,plain,
    ( spl5_88
    | spl5_194
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f922,f135,f107,f1143,f557])).

fof(f107,plain,
    ( spl5_0
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f922,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f921,f136])).

fof(f921,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r3_orders_2(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f97,f108])).

fof(f108,plain,
    ( v3_orders_2(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f107])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r3_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',redefinition_r3_orders_2)).

fof(f1141,plain,
    ( spl5_168
    | ~ spl5_187
    | spl5_96
    | ~ spl5_90
    | ~ spl5_162 ),
    inference(avatar_split_clause,[],[f1005,f998,f560,f598,f1116,f1033])).

fof(f1033,plain,
    ( spl5_168
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_168])])).

fof(f1116,plain,
    ( spl5_187
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).

fof(f598,plain,
    ( spl5_96
  <=> r3_orders_2(sK0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f560,plain,
    ( spl5_90
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f998,plain,
    ( spl5_162
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).

fof(f1005,plain,
    ( r3_orders_2(sK0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_90
    | ~ spl5_162 ),
    inference(superposition,[],[f571,f999])).

fof(f999,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_162 ),
    inference(avatar_component_clause,[],[f998])).

fof(f571,plain,
    ( ! [X3] :
        ( r3_orders_2(sK0,sK3(X3),sK3(X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X3) )
    | ~ spl5_90 ),
    inference(resolution,[],[f561,f248])).

fof(f561,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X0) )
    | ~ spl5_90 ),
    inference(avatar_component_clause,[],[f560])).

fof(f1140,plain,
    ( ~ spl5_193
    | spl5_187 ),
    inference(avatar_split_clause,[],[f1126,f1116,f1138])).

fof(f1138,plain,
    ( spl5_193
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_193])])).

fof(f1126,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_187 ),
    inference(resolution,[],[f1117,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t1_subset)).

fof(f1117,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_187 ),
    inference(avatar_component_clause,[],[f1116])).

fof(f1133,plain,
    ( ~ spl5_191
    | spl5_187 ),
    inference(avatar_split_clause,[],[f1125,f1116,f1131])).

fof(f1131,plain,
    ( spl5_191
  <=> ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_191])])).

fof(f1125,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_187 ),
    inference(resolution,[],[f1117,f92])).

fof(f1124,plain,
    ( ~ spl5_187
    | spl5_188
    | ~ spl5_90
    | ~ spl5_162
    | spl5_169
    | ~ spl5_174 ),
    inference(avatar_split_clause,[],[f1111,f1059,f1030,f998,f560,f1122,f1116])).

fof(f1122,plain,
    ( spl5_188
  <=> r1_orders_2(sK0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).

fof(f1030,plain,
    ( spl5_169
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f1059,plain,
    ( spl5_174
  <=> ! [X1,X0] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).

fof(f1111,plain,
    ( r1_orders_2(sK0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_90
    | ~ spl5_162
    | ~ spl5_169
    | ~ spl5_174 ),
    inference(subsumption_resolution,[],[f1110,f1031])).

fof(f1031,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_169 ),
    inference(avatar_component_clause,[],[f1030])).

fof(f1110,plain,
    ( r1_orders_2(sK0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_90
    | ~ spl5_162
    | ~ spl5_174 ),
    inference(superposition,[],[f1100,f999])).

fof(f1100,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(X0),sK3(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0) )
    | ~ spl5_90
    | ~ spl5_174 ),
    inference(subsumption_resolution,[],[f1097,f248])).

fof(f1097,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(X0),sK3(X0))
        | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0) )
    | ~ spl5_90
    | ~ spl5_174 ),
    inference(duplicate_literal_removal,[],[f1092])).

fof(f1092,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(X0),sK3(X0))
        | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0) )
    | ~ spl5_90
    | ~ spl5_174 ),
    inference(resolution,[],[f1060,f571])).

fof(f1060,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_174 ),
    inference(avatar_component_clause,[],[f1059])).

fof(f1107,plain,
    ( spl5_184
    | ~ spl5_92
    | ~ spl5_174 ),
    inference(avatar_split_clause,[],[f1099,f1059,f581,f1105])).

fof(f1105,plain,
    ( spl5_184
  <=> r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_184])])).

fof(f581,plain,
    ( spl5_92
  <=> r3_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f1099,plain,
    ( r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0)))
    | ~ spl5_92
    | ~ spl5_174 ),
    inference(subsumption_resolution,[],[f1098,f85])).

fof(f1098,plain,
    ( r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_92
    | ~ spl5_174 ),
    inference(duplicate_literal_removal,[],[f1091])).

fof(f1091,plain,
    ( r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_92
    | ~ spl5_174 ),
    inference(resolution,[],[f1060,f582])).

fof(f582,plain,
    ( r3_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0)))
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f581])).

fof(f1090,plain,
    ( spl5_168
    | spl5_182
    | ~ spl5_162 ),
    inference(avatar_split_clause,[],[f1006,f998,f1088,f1033])).

fof(f1088,plain,
    ( spl5_182
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_182])])).

fof(f1006,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_162 ),
    inference(superposition,[],[f248,f999])).

fof(f1084,plain,
    ( ~ spl5_181
    | spl5_177 ),
    inference(avatar_split_clause,[],[f1070,f1066,f1082])).

fof(f1082,plain,
    ( spl5_181
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_181])])).

fof(f1066,plain,
    ( spl5_177
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).

fof(f1070,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_177 ),
    inference(resolution,[],[f1067,f89])).

fof(f1067,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_177 ),
    inference(avatar_component_clause,[],[f1066])).

fof(f1077,plain,
    ( ~ spl5_179
    | spl5_177 ),
    inference(avatar_split_clause,[],[f1069,f1066,f1075])).

fof(f1075,plain,
    ( spl5_179
  <=> ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_179])])).

fof(f1069,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0)
    | ~ spl5_177 ),
    inference(resolution,[],[f1067,f92])).

fof(f1068,plain,
    ( ~ spl5_177
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f1056,f1046,f199,f188,f1066])).

fof(f188,plain,
    ( spl5_18
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f199,plain,
    ( spl5_20
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1046,plain,
    ( spl5_172
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).

fof(f1056,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_172 ),
    inference(forward_demodulation,[],[f1051,f200])).

fof(f200,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f199])).

fof(f1051,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_18
    | ~ spl5_172 ),
    inference(resolution,[],[f1047,f191])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl5_18 ),
    inference(resolution,[],[f189,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t5_subset)).

fof(f189,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f188])).

fof(f1047,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_172 ),
    inference(avatar_component_clause,[],[f1046])).

fof(f1061,plain,
    ( spl5_88
    | spl5_174
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f825,f135,f107,f1059,f557])).

fof(f825,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f824,f136])).

fof(f824,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f96,f108])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f1057,plain,
    ( ~ spl5_169
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f1055,f1046,f1030])).

fof(f1055,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_172 ),
    inference(resolution,[],[f1047,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t7_boole)).

fof(f1048,plain,
    ( spl5_168
    | spl5_172
    | ~ spl5_162 ),
    inference(avatar_split_clause,[],[f1008,f998,f1046,f1033])).

fof(f1008,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_162 ),
    inference(superposition,[],[f175,f999])).

fof(f1041,plain,
    ( spl5_168
    | ~ spl5_171
    | ~ spl5_162 ),
    inference(avatar_split_clause,[],[f1007,f998,f1039,f1033])).

fof(f1039,plain,
    ( spl5_171
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).

fof(f1007,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_162 ),
    inference(superposition,[],[f176,f999])).

fof(f176,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f175,f88])).

fof(f1025,plain,
    ( spl5_166
    | ~ spl5_162 ),
    inference(avatar_split_clause,[],[f1009,f998,f1023])).

fof(f1023,plain,
    ( spl5_166
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).

fof(f1009,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_162 ),
    inference(superposition,[],[f85,f999])).

fof(f1016,plain,
    ( spl5_164
    | ~ spl5_162 ),
    inference(avatar_split_clause,[],[f1004,f998,f1014])).

fof(f1014,plain,
    ( spl5_164
  <=> r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_164])])).

fof(f1004,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl5_162 ),
    inference(superposition,[],[f167,f999])).

fof(f167,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f91,f85])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f1000,plain,
    ( spl5_162
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_160 ),
    inference(avatar_split_clause,[],[f991,f984,f199,f188,f998])).

fof(f984,plain,
    ( spl5_160
  <=> v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f991,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_160 ),
    inference(forward_demodulation,[],[f987,f200])).

fof(f987,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18
    | ~ spl5_160 ),
    inference(resolution,[],[f985,f192])).

fof(f192,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl5_18 ),
    inference(resolution,[],[f189,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t8_boole)).

fof(f985,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_160 ),
    inference(avatar_component_clause,[],[f984])).

fof(f986,plain,
    ( spl5_158
    | spl5_160
    | spl5_61
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f937,f560,f415,f984,f978])).

fof(f978,plain,
    ( spl5_158
  <=> r3_orders_2(sK0,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).

fof(f415,plain,
    ( spl5_61
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f937,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | r3_orders_2(sK0,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_61
    | ~ spl5_90 ),
    inference(subsumption_resolution,[],[f928,f416])).

fof(f416,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f415])).

fof(f928,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | r3_orders_2(sK0,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_90 ),
    inference(resolution,[],[f634,f567])).

fof(f567,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X0) )
    | ~ spl5_90 ),
    inference(resolution,[],[f561,f89])).

fof(f973,plain,
    ( spl5_138
    | spl5_156
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f847,f758,f971,f865])).

fof(f865,plain,
    ( spl5_138
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f971,plain,
    ( spl5_156
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).

fof(f758,plain,
    ( spl5_124
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f847,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl5_124 ),
    inference(superposition,[],[f248,f759])).

fof(f759,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f758])).

fof(f969,plain,
    ( ~ spl5_155
    | spl5_151 ),
    inference(avatar_split_clause,[],[f955,f951,f967])).

fof(f967,plain,
    ( spl5_155
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_155])])).

fof(f951,plain,
    ( spl5_151
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_151])])).

fof(f955,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_151 ),
    inference(resolution,[],[f952,f89])).

fof(f952,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_151 ),
    inference(avatar_component_clause,[],[f951])).

fof(f962,plain,
    ( ~ spl5_153
    | spl5_151 ),
    inference(avatar_split_clause,[],[f954,f951,f960])).

fof(f960,plain,
    ( spl5_153
  <=> ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).

fof(f954,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl5_151 ),
    inference(resolution,[],[f952,f92])).

fof(f953,plain,
    ( spl5_138
    | ~ spl5_151
    | spl5_96
    | ~ spl5_90
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f846,f758,f560,f598,f951,f865])).

fof(f846,plain,
    ( r3_orders_2(sK0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_90
    | ~ spl5_124 ),
    inference(superposition,[],[f571,f759])).

fof(f946,plain,
    ( spl5_132
    | spl5_120
    | ~ spl5_126 ),
    inference(avatar_split_clause,[],[f799,f776,f730,f819])).

fof(f819,plain,
    ( spl5_132
  <=> r2_hidden(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f730,plain,
    ( spl5_120
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f776,plain,
    ( spl5_126
  <=> m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f799,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | r2_hidden(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_126 ),
    inference(resolution,[],[f777,f90])).

fof(f777,plain,
    ( m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_126 ),
    inference(avatar_component_clause,[],[f776])).

fof(f913,plain,
    ( ~ spl5_149
    | spl5_145 ),
    inference(avatar_split_clause,[],[f899,f895,f911])).

fof(f911,plain,
    ( spl5_149
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f895,plain,
    ( spl5_145
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_145])])).

fof(f899,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_145 ),
    inference(resolution,[],[f896,f89])).

fof(f896,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_145 ),
    inference(avatar_component_clause,[],[f895])).

fof(f906,plain,
    ( ~ spl5_147
    | spl5_145 ),
    inference(avatar_split_clause,[],[f898,f895,f904])).

fof(f904,plain,
    ( spl5_147
  <=> ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_147])])).

fof(f898,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl5_145 ),
    inference(resolution,[],[f896,f92])).

fof(f897,plain,
    ( ~ spl5_145
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_142 ),
    inference(avatar_split_clause,[],[f889,f878,f199,f188,f895])).

fof(f878,plain,
    ( spl5_142
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f889,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_142 ),
    inference(forward_demodulation,[],[f884,f200])).

fof(f884,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_18
    | ~ spl5_142 ),
    inference(resolution,[],[f879,f191])).

fof(f879,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_142 ),
    inference(avatar_component_clause,[],[f878])).

fof(f890,plain,
    ( ~ spl5_139
    | ~ spl5_142 ),
    inference(avatar_split_clause,[],[f888,f878,f862])).

fof(f862,plain,
    ( spl5_139
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).

fof(f888,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_142 ),
    inference(resolution,[],[f879,f94])).

fof(f880,plain,
    ( spl5_138
    | spl5_142
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f829,f795,f878,f865])).

fof(f795,plain,
    ( spl5_128
  <=> r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f829,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_128 ),
    inference(resolution,[],[f796,f172])).

fof(f172,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | r2_hidden(X3,k1_zfmisc_1(X2))
      | v1_xboole_0(k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f90,f92])).

fof(f796,plain,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_128 ),
    inference(avatar_component_clause,[],[f795])).

fof(f873,plain,
    ( spl5_138
    | ~ spl5_141
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f848,f758,f871,f865])).

fof(f871,plain,
    ( spl5_141
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).

fof(f848,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_124 ),
    inference(superposition,[],[f176,f759])).

fof(f859,plain,
    ( spl5_36
    | ~ spl5_124
    | ~ spl5_126 ),
    inference(avatar_split_clause,[],[f843,f776,f758,f287])).

fof(f287,plain,
    ( spl5_36
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f843,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_124
    | ~ spl5_126 ),
    inference(superposition,[],[f777,f759])).

fof(f858,plain,
    ( ~ spl5_137
    | ~ spl5_124
    | spl5_131 ),
    inference(avatar_split_clause,[],[f842,f812,f758,f856])).

fof(f856,plain,
    ( spl5_137
  <=> ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f812,plain,
    ( spl5_131
  <=> ~ r2_hidden(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f842,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl5_124
    | ~ spl5_131 ),
    inference(superposition,[],[f813,f759])).

fof(f813,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl5_131 ),
    inference(avatar_component_clause,[],[f812])).

fof(f836,plain,
    ( spl5_134
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f789,f758,f834])).

fof(f834,plain,
    ( spl5_134
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f789,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_124 ),
    inference(superposition,[],[f85,f759])).

fof(f821,plain,
    ( spl5_132
    | spl5_121
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f771,f744,f727,f819])).

fof(f727,plain,
    ( spl5_121
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f744,plain,
    ( spl5_122
  <=> k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f771,plain,
    ( r2_hidden(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_121
    | ~ spl5_122 ),
    inference(subsumption_resolution,[],[f766,f728])).

fof(f728,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_121 ),
    inference(avatar_component_clause,[],[f727])).

fof(f766,plain,
    ( r2_hidden(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_122 ),
    inference(superposition,[],[f175,f745])).

fof(f745,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_122 ),
    inference(avatar_component_clause,[],[f744])).

fof(f814,plain,
    ( ~ spl5_131
    | spl5_121
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f770,f744,f727,f812])).

fof(f770,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl5_121
    | ~ spl5_122 ),
    inference(subsumption_resolution,[],[f765,f728])).

fof(f765,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_122 ),
    inference(superposition,[],[f176,f745])).

fof(f797,plain,
    ( spl5_128
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f784,f758,f795])).

fof(f784,plain,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_124 ),
    inference(superposition,[],[f167,f759])).

fof(f782,plain,
    ( ~ spl5_45
    | spl5_123
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f779,f758,f741,f327])).

fof(f327,plain,
    ( spl5_45
  <=> k1_xboole_0 != sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f741,plain,
    ( spl5_123
  <=> k1_xboole_0 != sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f779,plain,
    ( k1_xboole_0 != sK3(k1_xboole_0)
    | ~ spl5_123
    | ~ spl5_124 ),
    inference(forward_demodulation,[],[f742,f759])).

fof(f742,plain,
    ( k1_xboole_0 != sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_123 ),
    inference(avatar_component_clause,[],[f741])).

fof(f778,plain,
    ( spl5_126
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f767,f744,f776])).

fof(f767,plain,
    ( m1_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_122 ),
    inference(superposition,[],[f85,f745])).

fof(f760,plain,
    ( spl5_124
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f751,f730,f199,f188,f758])).

fof(f751,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_120 ),
    inference(forward_demodulation,[],[f747,f200])).

fof(f747,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_18
    | ~ spl5_120 ),
    inference(resolution,[],[f731,f192])).

fof(f731,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_120 ),
    inference(avatar_component_clause,[],[f730])).

fof(f746,plain,
    ( spl5_122
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f737,f724,f199,f188,f744])).

fof(f724,plain,
    ( spl5_118
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f737,plain,
    ( k1_xboole_0 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_118 ),
    inference(forward_demodulation,[],[f733,f200])).

fof(f733,plain,
    ( sK3(k1_zfmisc_1(k1_xboole_0)) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_18
    | ~ spl5_118 ),
    inference(resolution,[],[f725,f192])).

fof(f725,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f724])).

fof(f732,plain,
    ( spl5_118
    | spl5_120
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f624,f149,f730,f724])).

fof(f149,plain,
    ( spl5_12
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f624,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_12 ),
    inference(resolution,[],[f403,f85])).

fof(f403,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK3(X2)) )
    | ~ spl5_12 ),
    inference(resolution,[],[f248,f180])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl5_12 ),
    inference(resolution,[],[f179,f175])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_12 ),
    inference(resolution,[],[f99,f150])).

fof(f150,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f710,plain,
    ( ~ spl5_117
    | spl5_113 ),
    inference(avatar_split_clause,[],[f696,f692,f708])).

fof(f708,plain,
    ( spl5_117
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f692,plain,
    ( spl5_113
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f696,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_113 ),
    inference(resolution,[],[f693,f89])).

fof(f693,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_113 ),
    inference(avatar_component_clause,[],[f692])).

fof(f703,plain,
    ( ~ spl5_115
    | spl5_113 ),
    inference(avatar_split_clause,[],[f695,f692,f701])).

fof(f701,plain,
    ( spl5_115
  <=> ~ r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f695,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_113 ),
    inference(resolution,[],[f693,f92])).

fof(f694,plain,
    ( ~ spl5_113
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_104 ),
    inference(avatar_split_clause,[],[f679,f651,f199,f188,f692])).

fof(f651,plain,
    ( spl5_104
  <=> r2_hidden(sK3(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f679,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_104 ),
    inference(forward_demodulation,[],[f674,f200])).

fof(f674,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_18
    | ~ spl5_104 ),
    inference(resolution,[],[f652,f191])).

fof(f652,plain,
    ( r2_hidden(sK3(sK1),sK2)
    | ~ spl5_104 ),
    inference(avatar_component_clause,[],[f651])).

fof(f687,plain,
    ( ~ spl5_111
    | ~ spl5_104 ),
    inference(avatar_split_clause,[],[f677,f651,f685])).

fof(f685,plain,
    ( spl5_111
  <=> ~ r2_hidden(sK2,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f677,plain,
    ( ~ r2_hidden(sK2,sK3(sK1))
    | ~ spl5_104 ),
    inference(resolution,[],[f652,f88])).

fof(f680,plain,
    ( ~ spl5_107
    | ~ spl5_104 ),
    inference(avatar_split_clause,[],[f678,f651,f654])).

fof(f678,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_104 ),
    inference(resolution,[],[f652,f94])).

fof(f673,plain,
    ( spl5_108
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_102 ),
    inference(avatar_split_clause,[],[f664,f645,f199,f188,f671])).

fof(f671,plain,
    ( spl5_108
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f645,plain,
    ( spl5_102
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f664,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_102 ),
    inference(forward_demodulation,[],[f660,f200])).

fof(f660,plain,
    ( sK1 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_102 ),
    inference(resolution,[],[f646,f192])).

fof(f646,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_102 ),
    inference(avatar_component_clause,[],[f645])).

fof(f659,plain,
    ( spl5_102
    | spl5_104
    | spl5_106
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f637,f156,f657,f651,f645])).

fof(f657,plain,
    ( spl5_106
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f637,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(sK3(sK1),sK2)
    | v1_xboole_0(sK1)
    | ~ spl5_14 ),
    inference(resolution,[],[f631,f157])).

fof(f631,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(sK3(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f404,f92])).

fof(f616,plain,
    ( ~ spl5_101
    | spl5_95 ),
    inference(avatar_split_clause,[],[f602,f592,f614])).

fof(f614,plain,
    ( spl5_101
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f592,plain,
    ( spl5_95
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f602,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_95 ),
    inference(resolution,[],[f593,f89])).

fof(f593,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_95 ),
    inference(avatar_component_clause,[],[f592])).

fof(f609,plain,
    ( ~ spl5_99
    | spl5_95 ),
    inference(avatar_split_clause,[],[f601,f592,f607])).

fof(f607,plain,
    ( spl5_99
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f601,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),u1_struct_0(sK0))
    | ~ spl5_95 ),
    inference(resolution,[],[f593,f92])).

fof(f600,plain,
    ( ~ spl5_95
    | spl5_96
    | ~ spl5_20
    | spl5_27
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f587,f560,f229,f199,f598,f592])).

fof(f229,plain,
    ( spl5_27
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f587,plain,
    ( r3_orders_2(sK0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20
    | ~ spl5_27
    | ~ spl5_90 ),
    inference(subsumption_resolution,[],[f586,f230])).

fof(f230,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f229])).

fof(f586,plain,
    ( r3_orders_2(sK0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20
    | ~ spl5_90 ),
    inference(superposition,[],[f571,f200])).

fof(f583,plain,
    ( spl5_92
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f570,f560,f581])).

fof(f570,plain,
    ( r3_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0)))
    | ~ spl5_90 ),
    inference(resolution,[],[f561,f85])).

fof(f566,plain,
    ( ~ spl5_4
    | ~ spl5_8
    | ~ spl5_88 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f564,f136])).

fof(f564,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl5_4
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f563,f122])).

fof(f122,plain,
    ( v2_lattice3(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_4
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f563,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl5_88 ),
    inference(resolution,[],[f558,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',cc2_lattice3)).

fof(f558,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f557])).

fof(f562,plain,
    ( spl5_88
    | spl5_90
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f546,f135,f107,f560,f557])).

fof(f546,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X0)
        | v2_struct_0(sK0) )
    | ~ spl5_0
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f545,f136])).

fof(f545,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r3_orders_2(sK0,X0,X0)
        | v2_struct_0(sK0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f101,f108])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r3_orders_2(X0,X1,X1)
      | v2_struct_0(X0) ) ),
    inference(condensation,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',reflexivity_r3_orders_2)).

fof(f534,plain,
    ( ~ spl5_87
    | spl5_83 ),
    inference(avatar_split_clause,[],[f520,f516,f532])).

fof(f532,plain,
    ( spl5_87
  <=> ~ r2_hidden(u1_struct_0(sK4),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f516,plain,
    ( spl5_83
  <=> ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f520,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_83 ),
    inference(resolution,[],[f517,f89])).

fof(f517,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_83 ),
    inference(avatar_component_clause,[],[f516])).

fof(f527,plain,
    ( ~ spl5_85
    | spl5_83 ),
    inference(avatar_split_clause,[],[f519,f516,f525])).

fof(f525,plain,
    ( spl5_85
  <=> ~ r1_tarski(u1_struct_0(sK4),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f519,plain,
    ( ~ r1_tarski(u1_struct_0(sK4),k1_xboole_0)
    | ~ spl5_83 ),
    inference(resolution,[],[f517,f92])).

fof(f518,plain,
    ( ~ spl5_83
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f511,f489,f199,f188,f516])).

fof(f489,plain,
    ( spl5_78
  <=> ! [X1] : r2_hidden(k1_yellow_0(sK4,X1),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f511,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_78 ),
    inference(forward_demodulation,[],[f506,f200])).

fof(f506,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_18
    | ~ spl5_78 ),
    inference(resolution,[],[f490,f191])).

fof(f490,plain,
    ( ! [X1] : r2_hidden(k1_yellow_0(sK4,X1),u1_struct_0(sK4))
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f489])).

fof(f505,plain,
    ( spl5_80
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f496,f486,f199,f188,f503])).

fof(f503,plain,
    ( spl5_80
  <=> k1_xboole_0 = u1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f486,plain,
    ( spl5_76
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f496,plain,
    ( k1_xboole_0 = u1_struct_0(sK4)
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f492,f200])).

fof(f492,plain,
    ( u1_struct_0(sK4) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_76 ),
    inference(resolution,[],[f487,f192])).

fof(f487,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f486])).

fof(f491,plain,
    ( spl5_76
    | spl5_78
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f413,f142,f489,f486])).

fof(f142,plain,
    ( spl5_10
  <=> l1_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f413,plain,
    ( ! [X1] :
        ( r2_hidden(k1_yellow_0(sK4,X1),u1_struct_0(sK4))
        | v1_xboole_0(u1_struct_0(sK4)) )
    | ~ spl5_10 ),
    inference(resolution,[],[f173,f143])).

fof(f143,plain,
    ( l1_orders_2(sK4)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f173,plain,(
    ! [X4,X5] :
      ( ~ l1_orders_2(X4)
      | r2_hidden(k1_yellow_0(X4,X5),u1_struct_0(X4))
      | v1_xboole_0(u1_struct_0(X4)) ) ),
    inference(resolution,[],[f90,f86])).

fof(f479,plain,
    ( ~ spl5_75
    | spl5_67 ),
    inference(avatar_split_clause,[],[f465,f448,f477])).

fof(f477,plain,
    ( spl5_75
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f448,plain,
    ( spl5_67
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f465,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_67 ),
    inference(resolution,[],[f449,f89])).

fof(f449,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f448])).

fof(f472,plain,
    ( ~ spl5_73
    | spl5_67 ),
    inference(avatar_split_clause,[],[f464,f448,f470])).

fof(f470,plain,
    ( spl5_73
  <=> ~ r1_tarski(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f464,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_67 ),
    inference(resolution,[],[f449,f92])).

fof(f463,plain,
    ( ~ spl5_69
    | ~ spl5_71 ),
    inference(avatar_split_clause,[],[f76,f461,f455])).

fof(f76,plain,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
      | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) )
    & r1_tarski(sK1,sK2)
    & l1_orders_2(sK0)
    & v3_lattice3(sK0)
    & v2_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f62,f61])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1))
            | ~ r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK0)
      & v3_lattice3(sK0)
      & v2_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
     => ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,sK2),k2_yellow_0(X0,sK1))
          | ~ r3_orders_2(X0,k1_yellow_0(X0,sK1),k1_yellow_0(X0,sK2)) )
        & r1_tarski(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f33])).

fof(f33,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t3_waybel_7)).

fof(f450,plain,
    ( ~ spl5_67
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f443,f421,f199,f188,f448])).

fof(f421,plain,
    ( spl5_62
  <=> ! [X0] : r2_hidden(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f443,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f438,f200])).

fof(f438,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK3(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_18
    | ~ spl5_62 ),
    inference(resolution,[],[f422,f191])).

fof(f422,plain,
    ( ! [X0] : r2_hidden(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f421])).

fof(f437,plain,
    ( spl5_64
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f428,f418,f199,f188,f435])).

fof(f435,plain,
    ( spl5_64
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f418,plain,
    ( spl5_60
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f428,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f424,f200])).

fof(f424,plain,
    ( u1_struct_0(sK0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_60 ),
    inference(resolution,[],[f419,f192])).

fof(f419,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f418])).

fof(f423,plain,
    ( spl5_60
    | spl5_62
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f412,f135,f421,f418])).

fof(f412,plain,
    ( ! [X0] :
        ( r2_hidden(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl5_8 ),
    inference(resolution,[],[f173,f136])).

fof(f399,plain,
    ( ~ spl5_59
    | spl5_55 ),
    inference(avatar_split_clause,[],[f385,f381,f397])).

fof(f397,plain,
    ( spl5_59
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f381,plain,
    ( spl5_55
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f385,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_55 ),
    inference(resolution,[],[f382,f89])).

fof(f382,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_55 ),
    inference(avatar_component_clause,[],[f381])).

fof(f392,plain,
    ( ~ spl5_57
    | spl5_55 ),
    inference(avatar_split_clause,[],[f384,f381,f390])).

fof(f390,plain,
    ( spl5_57
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f384,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),k1_xboole_0)
    | ~ spl5_55 ),
    inference(resolution,[],[f382,f92])).

fof(f383,plain,
    ( ~ spl5_55
    | ~ spl5_12
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f367,f348,f149,f381])).

fof(f348,plain,
    ( spl5_48
  <=> r2_hidden(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f367,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_12
    | ~ spl5_48 ),
    inference(resolution,[],[f349,f179])).

fof(f349,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK2))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f348])).

fof(f376,plain,
    ( ~ spl5_53
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f368,f348,f374])).

fof(f374,plain,
    ( spl5_53
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f368,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK1)
    | ~ spl5_48 ),
    inference(resolution,[],[f349,f88])).

fof(f364,plain,
    ( spl5_50
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f355,f342,f199,f188,f362])).

fof(f362,plain,
    ( spl5_50
  <=> k1_xboole_0 = k1_zfmisc_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f342,plain,
    ( spl5_46
  <=> v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f355,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK2)
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f351,f200])).

fof(f351,plain,
    ( k1_zfmisc_1(sK2) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_46 ),
    inference(resolution,[],[f343,f192])).

fof(f343,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f342])).

fof(f350,plain,
    ( spl5_46
    | spl5_48
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f335,f156,f348,f342])).

fof(f335,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl5_14 ),
    inference(resolution,[],[f172,f157])).

fof(f332,plain,
    ( spl5_44
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f294,f279,f199,f188,f330])).

fof(f330,plain,
    ( spl5_44
  <=> k1_xboole_0 = sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f279,plain,
    ( spl5_34
  <=> v1_xboole_0(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f294,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_34 ),
    inference(forward_demodulation,[],[f290,f200])).

fof(f290,plain,
    ( sK3(k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_34 ),
    inference(resolution,[],[f280,f192])).

fof(f280,plain,
    ( v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f279])).

fof(f325,plain,
    ( ~ spl5_43
    | spl5_39 ),
    inference(avatar_split_clause,[],[f311,f307,f323])).

fof(f323,plain,
    ( spl5_43
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f307,plain,
    ( spl5_39
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f311,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_39 ),
    inference(resolution,[],[f308,f89])).

fof(f308,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f307])).

fof(f318,plain,
    ( ~ spl5_41
    | spl5_39 ),
    inference(avatar_split_clause,[],[f310,f307,f316])).

fof(f316,plain,
    ( spl5_41
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f310,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_39 ),
    inference(resolution,[],[f308,f92])).

fof(f309,plain,
    ( ~ spl5_39
    | ~ spl5_12
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f300,f245,f149,f307])).

fof(f245,plain,
    ( spl5_30
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f300,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_12
    | ~ spl5_30 ),
    inference(resolution,[],[f246,f179])).

fof(f246,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f245])).

fof(f289,plain,
    ( spl5_36
    | ~ spl5_24
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f267,f260,f219,f287])).

fof(f219,plain,
    ( spl5_24
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f260,plain,
    ( spl5_32
  <=> k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f267,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_24
    | ~ spl5_32 ),
    inference(superposition,[],[f220,f261])).

fof(f261,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f260])).

fof(f220,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f281,plain,
    ( spl5_34
    | ~ spl5_18
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f265,f260,f188,f279])).

fof(f265,plain,
    ( v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_32 ),
    inference(superposition,[],[f189,f261])).

fof(f262,plain,
    ( spl5_32
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f253,f232,f199,f188,f260])).

fof(f232,plain,
    ( spl5_26
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f253,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl5_18
    | ~ spl5_20
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f249,f200])).

fof(f249,plain,
    ( k1_zfmisc_1(k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18
    | ~ spl5_26 ),
    inference(resolution,[],[f233,f192])).

fof(f233,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f232])).

fof(f247,plain,
    ( spl5_26
    | spl5_30
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f205,f199,f245,f232])).

fof(f205,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20 ),
    inference(superposition,[],[f175,f200])).

fof(f240,plain,
    ( spl5_26
    | ~ spl5_29
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f204,f199,f238,f232])).

fof(f238,plain,
    ( spl5_29
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f204,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20 ),
    inference(superposition,[],[f176,f200])).

fof(f221,plain,
    ( spl5_24
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f206,f199,f219])).

fof(f206,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20 ),
    inference(superposition,[],[f85,f200])).

fof(f213,plain,
    ( spl5_22
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f203,f199,f211])).

fof(f211,plain,
    ( spl5_22
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f203,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_20 ),
    inference(superposition,[],[f167,f200])).

fof(f201,plain,
    ( spl5_20
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f193,f188,f199])).

fof(f193,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_18 ),
    inference(resolution,[],[f189,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',t6_boole)).

fof(f190,plain,
    ( spl5_18
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f183,f149,f188])).

fof(f183,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_12 ),
    inference(resolution,[],[f180,f85])).

fof(f165,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f78,f163])).

fof(f163,plain,
    ( spl5_16
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f78,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',d2_xboole_0)).

fof(f158,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f75,f156])).

fof(f75,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f151,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f102,f149])).

fof(f102,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f77,f78])).

fof(f77,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',dt_o_0_0_xboole_0)).

fof(f144,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f100,f142])).

fof(f100,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    l1_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f68])).

fof(f68,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK4) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t3_waybel_7.p',existence_l1_orders_2)).

fof(f137,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f74,f135])).

fof(f74,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f130,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f73,f128])).

fof(f73,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f123,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f72,f121])).

fof(f72,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f116,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f71,f114])).

fof(f71,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f109,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f70,f107])).

fof(f70,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f63])).
%------------------------------------------------------------------------------

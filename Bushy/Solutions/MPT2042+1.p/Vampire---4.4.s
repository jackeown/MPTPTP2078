%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_9__t41_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:10 EDT 2019

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       : 1230 (4198 expanded)
%              Number of leaves         :  335 (1730 expanded)
%              Depth                    :   24
%              Number of atoms          : 4614 (13607 expanded)
%              Number of equality atoms :  126 ( 546 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3701,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f157,f164,f171,f178,f185,f192,f199,f206,f213,f220,f227,f234,f241,f248,f255,f262,f280,f290,f303,f320,f324,f346,f367,f381,f390,f404,f420,f441,f448,f458,f471,f488,f517,f525,f537,f538,f539,f540,f566,f587,f593,f600,f621,f627,f634,f641,f648,f668,f674,f684,f698,f714,f717,f729,f736,f770,f776,f783,f791,f798,f828,f849,f870,f884,f906,f915,f922,f925,f929,f946,f959,f973,f987,f993,f1000,f1007,f1017,f1021,f1035,f1041,f1048,f1055,f1068,f1076,f1087,f1096,f1103,f1128,f1138,f1145,f1155,f1174,f1188,f1191,f1212,f1222,f1234,f1240,f1245,f1262,f1276,f1290,f1302,f1317,f1321,f1338,f1352,f1367,f1380,f1383,f1393,f1411,f1418,f1422,f1435,f1446,f1460,f1474,f1485,f1499,f1561,f1587,f1623,f1648,f1800,f1831,f1888,f1916,f2095,f2101,f2108,f2115,f2128,f2150,f2155,f2168,f2174,f2182,f2189,f2236,f2249,f2255,f2262,f2269,f2288,f2294,f2301,f2308,f2316,f2330,f2336,f2343,f2350,f2401,f2423,f2446,f2449,f2464,f2469,f2473,f2486,f2508,f2522,f2528,f2535,f2542,f2546,f2559,f2565,f2572,f2579,f2593,f2596,f2640,f2662,f2678,f2693,f2715,f2727,f2860,f2864,f2959,f2965,f2972,f2994,f3006,f3015,f3055,f3077,f3091,f3098,f3105,f3123,f3145,f3157,f3164,f3171,f3180,f3204,f3212,f3231,f3253,f3267,f3277,f3287,f3309,f3326,f3348,f3372,f3379,f3386,f3394,f3408,f3409,f3416,f3423,f3431,f3441,f3463,f3492,f3514,f3526,f3533,f3547,f3554,f3563,f3581,f3603,f3617,f3623,f3631,f3638,f3651,f3654,f3657,f3686,f3698,f3699,f3700])).

fof(f3700,plain,
    ( ~ spl11_455
    | spl11_490
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(avatar_split_clause,[],[f3677,f1101,f1094,f1060,f211,f204,f197,f190,f183,f176,f169,f162,f155,f3392,f3196])).

fof(f3196,plain,
    ( spl11_455
  <=> ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_455])])).

fof(f3392,plain,
    ( spl11_490
  <=> r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_490])])).

fof(f155,plain,
    ( spl11_0
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f162,plain,
    ( spl11_2
  <=> v8_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f169,plain,
    ( spl11_4
  <=> v3_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f176,plain,
    ( spl11_6
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f183,plain,
    ( spl11_8
  <=> v5_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f190,plain,
    ( spl11_10
  <=> v1_lattice3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f197,plain,
    ( spl11_12
  <=> v2_lattice3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f204,plain,
    ( spl11_14
  <=> v1_compts_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f211,plain,
    ( spl11_16
  <=> l1_waybel_9(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f1060,plain,
    ( spl11_182
  <=> sP0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_182])])).

fof(f1094,plain,
    ( spl11_188
  <=> v10_waybel_0(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_188])])).

fof(f1101,plain,
    ( spl11_190
  <=> l1_waybel_0(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_190])])).

fof(f3677,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f3676,f1102])).

fof(f1102,plain,
    ( l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_190 ),
    inference(avatar_component_clause,[],[f1101])).

fof(f3676,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3675,f156])).

fof(f156,plain,
    ( v2_pre_topc(sK1)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f155])).

fof(f3675,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3674,f163])).

fof(f163,plain,
    ( v8_pre_topc(sK1)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f162])).

fof(f3674,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3673,f170])).

fof(f170,plain,
    ( v3_orders_2(sK1)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f169])).

fof(f3673,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3672,f177])).

fof(f177,plain,
    ( v4_orders_2(sK1)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f176])).

fof(f3672,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3671,f184])).

fof(f184,plain,
    ( v5_orders_2(sK1)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f183])).

fof(f3671,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3670,f191])).

fof(f191,plain,
    ( v1_lattice3(sK1)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f190])).

fof(f3670,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3669,f198])).

fof(f198,plain,
    ( v2_lattice3(sK1)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f197])).

fof(f3669,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3668,f205])).

fof(f205,plain,
    ( v1_compts_1(sK1)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f204])).

fof(f3668,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v1_compts_1(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3624,f212])).

fof(f212,plain,
    ( l1_waybel_9(sK1)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f211])).

fof(f3624,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ l1_waybel_9(sK1)
    | ~ v1_compts_1(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(resolution,[],[f2580,f1095])).

fof(f1095,plain,
    ( v10_waybel_0(sK4(sK1),sK1)
    | ~ spl11_188 ),
    inference(avatar_component_clause,[],[f1094])).

fof(f2580,plain,
    ( ! [X0] :
        ( ~ v10_waybel_0(sK4(sK1),X0)
        | r2_hidden(k1_waybel_2(X0,sK4(sK1)),k10_yellow_6(X0,sK4(sK1)))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        | ~ l1_waybel_9(X0)
        | ~ v1_compts_1(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v8_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_waybel_0(sK4(sK1),X0) )
    | ~ spl11_182 ),
    inference(resolution,[],[f1414,f1061])).

fof(f1061,plain,
    ( sP0(sK1)
    | ~ spl11_182 ),
    inference(avatar_component_clause,[],[f1060])).

fof(f1414,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0)
      | ~ l1_waybel_0(sK4(X0),X1)
      | r2_hidden(k1_waybel_2(X1,sK4(X0)),k10_yellow_6(X1,sK4(X0)))
      | ~ v5_pre_topc(k4_waybel_1(X1,sK3(X1)),X1,X1)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ v10_waybel_0(sK4(X0),X1) ) ),
    inference(subsumption_resolution,[],[f1413,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK4(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ( ( ~ r2_hidden(k1_waybel_2(X0,sK4(X0)),k10_yellow_6(X0,sK4(X0)))
          | ~ r1_waybel_9(X0,sK4(X0)) )
        & v10_waybel_0(sK4(X0),X0)
        & l1_waybel_0(sK4(X0),X0)
        & v7_waybel_0(sK4(X0))
        & v4_orders_2(sK4(X0))
        & ~ v2_struct_0(sK4(X0)) )
      | ~ sP0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f86,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            | ~ r1_waybel_9(X0,X1) )
          & v10_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ( ~ r2_hidden(k1_waybel_2(X0,sK4(X0)),k10_yellow_6(X0,sK4(X0)))
          | ~ r1_waybel_9(X0,sK4(X0)) )
        & v10_waybel_0(sK4(X0),X0)
        & l1_waybel_0(sK4(X0),X0)
        & v7_waybel_0(sK4(X0))
        & v4_orders_2(sK4(X0))
        & ~ v2_struct_0(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            | ~ r1_waybel_9(X0,X1) )
          & v10_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ sP0(X0) ) ),
    inference(rectify,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1413,plain,(
    ! [X0,X1] :
      ( ~ v10_waybel_0(sK4(X0),X1)
      | ~ l1_waybel_0(sK4(X0),X1)
      | r2_hidden(k1_waybel_2(X1,sK4(X0)),k10_yellow_6(X1,sK4(X0)))
      | v2_struct_0(sK4(X0))
      | ~ v5_pre_topc(k4_waybel_1(X1,sK3(X1)),X1,X1)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ sP0(X0) ) ),
    inference(subsumption_resolution,[],[f1412,f127])).

fof(f127,plain,(
    ! [X0] :
      ( v4_orders_2(sK4(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f1412,plain,(
    ! [X0,X1] :
      ( ~ v10_waybel_0(sK4(X0),X1)
      | ~ l1_waybel_0(sK4(X0),X1)
      | r2_hidden(k1_waybel_2(X1,sK4(X0)),k10_yellow_6(X1,sK4(X0)))
      | ~ v4_orders_2(sK4(X0))
      | v2_struct_0(sK4(X0))
      | ~ v5_pre_topc(k4_waybel_1(X1,sK3(X1)),X1,X1)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f125,f128])).

fof(f128,plain,(
    ! [X0] :
      ( v7_waybel_0(sK4(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            & r1_waybel_9(X0,X1) )
          | ~ v10_waybel_0(X1,X0)
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f82,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            & r1_waybel_9(X0,X1) )
          | ~ v10_waybel_0(X1,X0)
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ? [X2] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X2] :
          ( ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            & r1_waybel_9(X0,X2) )
          | ~ v10_waybel_0(X2,X0)
          | ~ l1_waybel_0(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) )
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X2] :
          ( ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            & r1_waybel_9(X0,X2) )
          | ~ v10_waybel_0(X2,X0)
          | ~ l1_waybel_0(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) )
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
       => ! [X2] :
            ( ( l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
           => ( v10_waybel_0(X2,X0)
             => ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
                & r1_waybel_9(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v10_waybel_0(X1,X0)
             => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                & r1_waybel_9(X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t38_waybel_9)).

fof(f3699,plain,
    ( spl11_458
    | spl11_490
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(avatar_split_clause,[],[f3667,f1101,f1094,f1060,f211,f204,f197,f190,f183,f176,f169,f162,f155,f3392,f3207])).

fof(f3207,plain,
    ( spl11_458
  <=> m1_subset_1(sK3(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_458])])).

fof(f3667,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f3666,f1102])).

fof(f3666,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3665,f156])).

fof(f3665,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3664,f163])).

fof(f3664,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3663,f170])).

fof(f3663,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3662,f177])).

fof(f3662,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3661,f184])).

fof(f3661,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3660,f191])).

fof(f3660,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3659,f198])).

fof(f3659,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3658,f205])).

fof(f3658,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v1_compts_1(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3349,f212])).

fof(f3349,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ l1_waybel_9(sK1)
    | ~ v1_compts_1(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(resolution,[],[f2465,f1095])).

fof(f2465,plain,
    ( ! [X0] :
        ( ~ v10_waybel_0(sK4(sK1),X0)
        | r2_hidden(k1_waybel_2(X0,sK4(sK1)),k10_yellow_6(X0,sK4(sK1)))
        | m1_subset_1(sK3(X0),u1_struct_0(X0))
        | ~ l1_waybel_9(X0)
        | ~ v1_compts_1(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v8_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_waybel_0(sK4(sK1),X0) )
    | ~ spl11_182 ),
    inference(resolution,[],[f1326,f1061])).

fof(f1326,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0)
      | ~ l1_waybel_0(sK4(X0),X1)
      | r2_hidden(k1_waybel_2(X1,sK4(X0)),k10_yellow_6(X1,sK4(X0)))
      | m1_subset_1(sK3(X1),u1_struct_0(X1))
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ v10_waybel_0(sK4(X0),X1) ) ),
    inference(subsumption_resolution,[],[f1325,f126])).

fof(f1325,plain,(
    ! [X0,X1] :
      ( ~ v10_waybel_0(sK4(X0),X1)
      | ~ l1_waybel_0(sK4(X0),X1)
      | r2_hidden(k1_waybel_2(X1,sK4(X0)),k10_yellow_6(X1,sK4(X0)))
      | v2_struct_0(sK4(X0))
      | m1_subset_1(sK3(X1),u1_struct_0(X1))
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ sP0(X0) ) ),
    inference(subsumption_resolution,[],[f1324,f127])).

fof(f1324,plain,(
    ! [X0,X1] :
      ( ~ v10_waybel_0(sK4(X0),X1)
      | ~ l1_waybel_0(sK4(X0),X1)
      | r2_hidden(k1_waybel_2(X1,sK4(X0)),k10_yellow_6(X1,sK4(X0)))
      | ~ v4_orders_2(sK4(X0))
      | v2_struct_0(sK4(X0))
      | m1_subset_1(sK3(X1),u1_struct_0(X1))
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f124,f128])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f3698,plain,
    ( ~ spl11_543
    | ~ spl11_540 ),
    inference(avatar_split_clause,[],[f3689,f3684,f3696])).

fof(f3696,plain,
    ( spl11_543
  <=> ~ r2_hidden(u1_struct_0(sK1),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_543])])).

fof(f3684,plain,
    ( spl11_540
  <=> r2_hidden(sK3(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_540])])).

fof(f3689,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK3(sK1))
    | ~ spl11_540 ),
    inference(resolution,[],[f3685,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',antisymmetry_r2_hidden)).

fof(f3685,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK1))
    | ~ spl11_540 ),
    inference(avatar_component_clause,[],[f3684])).

fof(f3686,plain,
    ( spl11_540
    | spl11_89
    | ~ spl11_458 ),
    inference(avatar_split_clause,[],[f3679,f3207,f616,f3684])).

fof(f616,plain,
    ( spl11_89
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_89])])).

fof(f3679,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK1))
    | ~ spl11_89
    | ~ spl11_458 ),
    inference(subsumption_resolution,[],[f3678,f617])).

fof(f617,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl11_89 ),
    inference(avatar_component_clause,[],[f616])).

fof(f3678,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK3(sK1),u1_struct_0(sK1))
    | ~ spl11_458 ),
    inference(resolution,[],[f3208,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t2_subset)).

fof(f3208,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ spl11_458 ),
    inference(avatar_component_clause,[],[f3207])).

fof(f3657,plain,
    ( ~ spl11_182
    | spl11_539 ),
    inference(avatar_contradiction_clause,[],[f3656])).

fof(f3656,plain,
    ( $false
    | ~ spl11_182
    | ~ spl11_539 ),
    inference(subsumption_resolution,[],[f3655,f1061])).

fof(f3655,plain,
    ( ~ sP0(sK1)
    | ~ spl11_539 ),
    inference(resolution,[],[f3650,f128])).

fof(f3650,plain,
    ( ~ v7_waybel_0(sK4(sK1))
    | ~ spl11_539 ),
    inference(avatar_component_clause,[],[f3649])).

fof(f3649,plain,
    ( spl11_539
  <=> ~ v7_waybel_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_539])])).

fof(f3654,plain,
    ( ~ spl11_182
    | spl11_537 ),
    inference(avatar_contradiction_clause,[],[f3653])).

fof(f3653,plain,
    ( $false
    | ~ spl11_182
    | ~ spl11_537 ),
    inference(subsumption_resolution,[],[f3652,f1061])).

fof(f3652,plain,
    ( ~ sP0(sK1)
    | ~ spl11_537 ),
    inference(resolution,[],[f3644,f127])).

fof(f3644,plain,
    ( ~ v4_orders_2(sK4(sK1))
    | ~ spl11_537 ),
    inference(avatar_component_clause,[],[f3643])).

fof(f3643,plain,
    ( spl11_537
  <=> ~ v4_orders_2(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_537])])).

fof(f3651,plain,
    ( spl11_458
    | spl11_204
    | ~ spl11_537
    | ~ spl11_539
    | spl11_456
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(avatar_split_clause,[],[f1114,f1101,f1094,f211,f204,f197,f190,f183,f176,f169,f162,f155,f3202,f3649,f3643,f1172,f3207])).

fof(f1172,plain,
    ( spl11_204
  <=> v2_struct_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_204])])).

fof(f3202,plain,
    ( spl11_456
  <=> r1_waybel_9(sK1,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_456])])).

fof(f1114,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v7_waybel_0(sK4(sK1))
    | ~ v4_orders_2(sK4(sK1))
    | v2_struct_0(sK4(sK1))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1113,f156])).

fof(f1113,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v7_waybel_0(sK4(sK1))
    | ~ v4_orders_2(sK4(sK1))
    | v2_struct_0(sK4(sK1))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1112,f163])).

fof(f1112,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v7_waybel_0(sK4(sK1))
    | ~ v4_orders_2(sK4(sK1))
    | v2_struct_0(sK4(sK1))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1111,f170])).

fof(f1111,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v7_waybel_0(sK4(sK1))
    | ~ v4_orders_2(sK4(sK1))
    | v2_struct_0(sK4(sK1))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1110,f177])).

fof(f1110,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v7_waybel_0(sK4(sK1))
    | ~ v4_orders_2(sK4(sK1))
    | v2_struct_0(sK4(sK1))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1109,f184])).

fof(f1109,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v7_waybel_0(sK4(sK1))
    | ~ v4_orders_2(sK4(sK1))
    | v2_struct_0(sK4(sK1))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1108,f191])).

fof(f1108,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v7_waybel_0(sK4(sK1))
    | ~ v4_orders_2(sK4(sK1))
    | v2_struct_0(sK4(sK1))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1107,f198])).

fof(f1107,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v7_waybel_0(sK4(sK1))
    | ~ v4_orders_2(sK4(sK1))
    | v2_struct_0(sK4(sK1))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1106,f205])).

fof(f1106,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v7_waybel_0(sK4(sK1))
    | ~ v4_orders_2(sK4(sK1))
    | v2_struct_0(sK4(sK1))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ v1_compts_1(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_16
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1105,f212])).

fof(f1105,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v7_waybel_0(sK4(sK1))
    | ~ v4_orders_2(sK4(sK1))
    | v2_struct_0(sK4(sK1))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ l1_waybel_9(sK1)
    | ~ v1_compts_1(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1104,f1102])).

fof(f1104,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ v7_waybel_0(sK4(sK1))
    | ~ v4_orders_2(sK4(sK1))
    | v2_struct_0(sK4(sK1))
    | m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ l1_waybel_9(sK1)
    | ~ v1_compts_1(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_188 ),
    inference(resolution,[],[f1095,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v10_waybel_0(X1,X0)
      | r1_waybel_9(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f3638,plain,
    ( ~ spl11_535
    | ~ spl11_528 ),
    inference(avatar_split_clause,[],[f3620,f3609,f3636])).

fof(f3636,plain,
    ( spl11_535
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0),sK6(u1_waybel_0(sK2(sK8),sK2(sK2(sK8))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_535])])).

fof(f3609,plain,
    ( spl11_528
  <=> r2_hidden(sK6(u1_waybel_0(sK2(sK8),sK2(sK2(sK8)))),k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_528])])).

fof(f3620,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0),sK6(u1_waybel_0(sK2(sK8),sK2(sK2(sK8)))))
    | ~ spl11_528 ),
    inference(resolution,[],[f3610,f135])).

fof(f3610,plain,
    ( r2_hidden(sK6(u1_waybel_0(sK2(sK8),sK2(sK2(sK8)))),k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0))
    | ~ spl11_528 ),
    inference(avatar_component_clause,[],[f3609])).

fof(f3631,plain,
    ( ~ spl11_533
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_528 ),
    inference(avatar_split_clause,[],[f3622,f3609,f288,f278,f3629])).

fof(f3629,plain,
    ( spl11_533
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_533])])).

fof(f278,plain,
    ( spl11_32
  <=> v1_xboole_0(sK6(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f288,plain,
    ( spl11_34
  <=> k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f3622,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_528 ),
    inference(forward_demodulation,[],[f3618,f289])).

fof(f289,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f288])).

fof(f3618,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_528 ),
    inference(resolution,[],[f3610,f281])).

fof(f281,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl11_32 ),
    inference(resolution,[],[f279,f145])).

fof(f145,plain,(
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
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t5_subset)).

fof(f279,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f278])).

fof(f3623,plain,
    ( ~ spl11_531
    | ~ spl11_528 ),
    inference(avatar_split_clause,[],[f3621,f3609,f3612])).

fof(f3612,plain,
    ( spl11_531
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_531])])).

fof(f3621,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0))
    | ~ spl11_528 ),
    inference(resolution,[],[f3610,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t7_boole)).

fof(f3617,plain,
    ( spl11_528
    | spl11_530
    | ~ spl11_524 ),
    inference(avatar_split_clause,[],[f3604,f3579,f3615,f3609])).

fof(f3615,plain,
    ( spl11_530
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_530])])).

fof(f3579,plain,
    ( spl11_524
  <=> m1_subset_1(sK6(u1_waybel_0(sK2(sK8),sK2(sK2(sK8)))),k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_524])])).

fof(f3604,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0))
    | r2_hidden(sK6(u1_waybel_0(sK2(sK8),sK2(sK2(sK8)))),k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0))
    | ~ spl11_524 ),
    inference(resolution,[],[f3580,f137])).

fof(f3580,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK2(sK8),sK2(sK2(sK8)))),k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0))
    | ~ spl11_524 ),
    inference(avatar_component_clause,[],[f3579])).

fof(f3603,plain,
    ( spl11_526
    | ~ spl11_522 ),
    inference(avatar_split_clause,[],[f3582,f3573,f3601])).

fof(f3601,plain,
    ( spl11_526
  <=> u1_waybel_0(sK2(sK8),sK2(sK2(sK8))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_526])])).

fof(f3573,plain,
    ( spl11_522
  <=> v1_xboole_0(u1_waybel_0(sK2(sK8),sK2(sK2(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_522])])).

fof(f3582,plain,
    ( u1_waybel_0(sK2(sK8),sK2(sK2(sK8))) = k1_xboole_0
    | ~ spl11_522 ),
    inference(resolution,[],[f3574,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t6_boole)).

fof(f3574,plain,
    ( v1_xboole_0(u1_waybel_0(sK2(sK8),sK2(sK2(sK8))))
    | ~ spl11_522 ),
    inference(avatar_component_clause,[],[f3573])).

fof(f3581,plain,
    ( spl11_522
    | spl11_524
    | ~ spl11_392 ),
    inference(avatar_split_clause,[],[f2600,f2591,f3579,f3573])).

fof(f2591,plain,
    ( spl11_392
  <=> m1_subset_1(u1_waybel_0(sK2(sK8),sK2(sK2(sK8))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_392])])).

fof(f2600,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK2(sK8),sK2(sK2(sK8)))),k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0))
    | v1_xboole_0(u1_waybel_0(sK2(sK8),sK2(sK2(sK8))))
    | ~ spl11_392 ),
    inference(resolution,[],[f2598,f267])).

fof(f267,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f137,f134])).

fof(f134,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',existence_m1_subset_1)).

fof(f2598,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK2(sK8),sK2(sK2(sK8))))
        | m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0)) )
    | ~ spl11_392 ),
    inference(resolution,[],[f2592,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t4_subset)).

fof(f2592,plain,
    ( m1_subset_1(u1_waybel_0(sK2(sK8),sK2(sK2(sK8))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0)))
    | ~ spl11_392 ),
    inference(avatar_component_clause,[],[f2591])).

fof(f3563,plain,
    ( spl11_520
    | ~ spl11_442
    | ~ spl11_510 ),
    inference(avatar_split_clause,[],[f3539,f3512,f3121,f3561])).

fof(f3561,plain,
    ( spl11_520
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_520])])).

fof(f3121,plain,
    ( spl11_442
  <=> r2_hidden(u1_waybel_0(sK7,sK2(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_442])])).

fof(f3512,plain,
    ( spl11_510
  <=> u1_waybel_0(sK7,sK2(sK7)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_510])])).

fof(f3539,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))))
    | ~ spl11_442
    | ~ spl11_510 ),
    inference(superposition,[],[f3122,f3513])).

fof(f3513,plain,
    ( u1_waybel_0(sK7,sK2(sK7)) = k1_xboole_0
    | ~ spl11_510 ),
    inference(avatar_component_clause,[],[f3512])).

fof(f3122,plain,
    ( r2_hidden(u1_waybel_0(sK7,sK2(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))))
    | ~ spl11_442 ),
    inference(avatar_component_clause,[],[f3121])).

fof(f3554,plain,
    ( spl11_518
    | ~ spl11_446
    | ~ spl11_510 ),
    inference(avatar_split_clause,[],[f3538,f3512,f3155,f3552])).

fof(f3552,plain,
    ( spl11_518
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_518])])).

fof(f3155,plain,
    ( spl11_446
  <=> m1_subset_1(u1_waybel_0(sK7,sK2(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_446])])).

fof(f3538,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))))
    | ~ spl11_446
    | ~ spl11_510 ),
    inference(superposition,[],[f3156,f3513])).

fof(f3156,plain,
    ( m1_subset_1(u1_waybel_0(sK7,sK2(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))))
    | ~ spl11_446 ),
    inference(avatar_component_clause,[],[f3155])).

fof(f3547,plain,
    ( ~ spl11_517
    | spl11_509
    | ~ spl11_510 ),
    inference(avatar_split_clause,[],[f3534,f3512,f3487,f3545])).

fof(f3545,plain,
    ( spl11_517
  <=> ~ r2_hidden(sK6(k1_xboole_0),k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_517])])).

fof(f3487,plain,
    ( spl11_509
  <=> ~ r2_hidden(sK6(u1_waybel_0(sK7,sK2(sK7))),k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_509])])).

fof(f3534,plain,
    ( ~ r2_hidden(sK6(k1_xboole_0),k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))
    | ~ spl11_509
    | ~ spl11_510 ),
    inference(forward_demodulation,[],[f3488,f3513])).

fof(f3488,plain,
    ( ~ r2_hidden(sK6(u1_waybel_0(sK7,sK2(sK7))),k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))
    | ~ spl11_509 ),
    inference(avatar_component_clause,[],[f3487])).

fof(f3533,plain,
    ( spl11_514
    | ~ spl11_508 ),
    inference(avatar_split_clause,[],[f3516,f3490,f3531])).

fof(f3531,plain,
    ( spl11_514
  <=> m1_subset_1(sK6(u1_waybel_0(sK7,sK2(sK7))),k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_514])])).

fof(f3490,plain,
    ( spl11_508
  <=> r2_hidden(sK6(u1_waybel_0(sK7,sK2(sK7))),k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_508])])).

fof(f3516,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK7,sK2(sK7))),k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))
    | ~ spl11_508 ),
    inference(resolution,[],[f3491,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t1_subset)).

fof(f3491,plain,
    ( r2_hidden(sK6(u1_waybel_0(sK7,sK2(sK7))),k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))
    | ~ spl11_508 ),
    inference(avatar_component_clause,[],[f3490])).

fof(f3526,plain,
    ( ~ spl11_513
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_508 ),
    inference(avatar_split_clause,[],[f3519,f3490,f288,f278,f3524])).

fof(f3524,plain,
    ( spl11_513
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_513])])).

fof(f3519,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_508 ),
    inference(forward_demodulation,[],[f3515,f289])).

fof(f3515,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_508 ),
    inference(resolution,[],[f3491,f281])).

fof(f3514,plain,
    ( spl11_510
    | ~ spl11_506 ),
    inference(avatar_split_clause,[],[f3493,f3484,f3512])).

fof(f3484,plain,
    ( spl11_506
  <=> v1_xboole_0(u1_waybel_0(sK7,sK2(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_506])])).

fof(f3493,plain,
    ( u1_waybel_0(sK7,sK2(sK7)) = k1_xboole_0
    | ~ spl11_506 ),
    inference(resolution,[],[f3485,f117])).

fof(f3485,plain,
    ( v1_xboole_0(u1_waybel_0(sK7,sK2(sK7)))
    | ~ spl11_506 ),
    inference(avatar_component_clause,[],[f3484])).

fof(f3492,plain,
    ( spl11_506
    | spl11_508
    | ~ spl11_502 ),
    inference(avatar_split_clause,[],[f3476,f3439,f3490,f3484])).

fof(f3439,plain,
    ( spl11_502
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK7,sK2(sK7)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_502])])).

fof(f3476,plain,
    ( r2_hidden(sK6(u1_waybel_0(sK7,sK2(sK7))),k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))
    | v1_xboole_0(u1_waybel_0(sK7,sK2(sK7)))
    | ~ spl11_502 ),
    inference(resolution,[],[f3440,f267])).

fof(f3440,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK7,sK2(sK7)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))) )
    | ~ spl11_502 ),
    inference(avatar_component_clause,[],[f3439])).

fof(f3463,plain,
    ( spl11_504
    | ~ spl11_500 ),
    inference(avatar_split_clause,[],[f3442,f3436,f3461])).

fof(f3461,plain,
    ( spl11_504
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_504])])).

fof(f3436,plain,
    ( spl11_500
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_500])])).

fof(f3442,plain,
    ( k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))
    | ~ spl11_500 ),
    inference(resolution,[],[f3437,f117])).

fof(f3437,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))
    | ~ spl11_500 ),
    inference(avatar_component_clause,[],[f3436])).

fof(f3441,plain,
    ( spl11_500
    | spl11_502
    | ~ spl11_446 ),
    inference(avatar_split_clause,[],[f3174,f3155,f3439,f3436])).

fof(f3174,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK7,sK2(sK7)))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))) )
    | ~ spl11_446 ),
    inference(resolution,[],[f3172,f137])).

fof(f3172,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))
        | ~ r2_hidden(X0,u1_waybel_0(sK7,sK2(sK7))) )
    | ~ spl11_446 ),
    inference(resolution,[],[f3156,f144])).

fof(f3431,plain,
    ( ~ spl11_499
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_490 ),
    inference(avatar_split_clause,[],[f3401,f3392,f288,f278,f3429])).

fof(f3429,plain,
    ( spl11_499
  <=> ~ m1_subset_1(k10_yellow_6(sK1,sK4(sK1)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_499])])).

fof(f3401,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK1,sK4(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_490 ),
    inference(forward_demodulation,[],[f3396,f289])).

fof(f3396,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK1,sK4(sK1)),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_490 ),
    inference(resolution,[],[f3393,f281])).

fof(f3393,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ spl11_490 ),
    inference(avatar_component_clause,[],[f3392])).

fof(f3423,plain,
    ( ~ spl11_497
    | ~ spl11_490 ),
    inference(avatar_split_clause,[],[f3398,f3392,f3421])).

fof(f3421,plain,
    ( spl11_497
  <=> ~ r2_hidden(k10_yellow_6(sK1,sK4(sK1)),k1_waybel_2(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_497])])).

fof(f3398,plain,
    ( ~ r2_hidden(k10_yellow_6(sK1,sK4(sK1)),k1_waybel_2(sK1,sK4(sK1)))
    | ~ spl11_490 ),
    inference(resolution,[],[f3393,f135])).

fof(f3416,plain,
    ( spl11_494
    | ~ spl11_490 ),
    inference(avatar_split_clause,[],[f3397,f3392,f3414])).

fof(f3414,plain,
    ( spl11_494
  <=> m1_subset_1(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_494])])).

fof(f3397,plain,
    ( m1_subset_1(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ spl11_490 ),
    inference(resolution,[],[f3393,f136])).

fof(f3409,plain,
    ( ~ spl11_457
    | ~ spl11_182
    | ~ spl11_490 ),
    inference(avatar_split_clause,[],[f3400,f3392,f1060,f3199])).

fof(f3199,plain,
    ( spl11_457
  <=> ~ r1_waybel_9(sK1,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_457])])).

fof(f3400,plain,
    ( ~ r1_waybel_9(sK1,sK4(sK1))
    | ~ spl11_182
    | ~ spl11_490 ),
    inference(subsumption_resolution,[],[f3395,f1061])).

fof(f3395,plain,
    ( ~ r1_waybel_9(sK1,sK4(sK1))
    | ~ sP0(sK1)
    | ~ spl11_490 ),
    inference(resolution,[],[f3393,f131])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_waybel_2(X0,sK4(X0)),k10_yellow_6(X0,sK4(X0)))
      | ~ r1_waybel_9(X0,sK4(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f3408,plain,
    ( ~ spl11_493
    | ~ spl11_490 ),
    inference(avatar_split_clause,[],[f3399,f3392,f3406])).

fof(f3406,plain,
    ( spl11_493
  <=> ~ v1_xboole_0(k10_yellow_6(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_493])])).

fof(f3399,plain,
    ( ~ v1_xboole_0(k10_yellow_6(sK1,sK4(sK1)))
    | ~ spl11_490 ),
    inference(resolution,[],[f3393,f143])).

fof(f3394,plain,
    ( spl11_490
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_190
    | spl11_459 ),
    inference(avatar_split_clause,[],[f3360,f3210,f1101,f1094,f1060,f211,f204,f197,f190,f183,f176,f169,f162,f155,f3392])).

fof(f3210,plain,
    ( spl11_459
  <=> ~ m1_subset_1(sK3(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_459])])).

fof(f3360,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_190
    | ~ spl11_459 ),
    inference(subsumption_resolution,[],[f3359,f1102])).

fof(f3359,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_459 ),
    inference(subsumption_resolution,[],[f3358,f156])).

fof(f3358,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_459 ),
    inference(subsumption_resolution,[],[f3357,f163])).

fof(f3357,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_459 ),
    inference(subsumption_resolution,[],[f3356,f170])).

fof(f3356,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_459 ),
    inference(subsumption_resolution,[],[f3355,f177])).

fof(f3355,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_459 ),
    inference(subsumption_resolution,[],[f3354,f184])).

fof(f3354,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_459 ),
    inference(subsumption_resolution,[],[f3353,f191])).

fof(f3353,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_459 ),
    inference(subsumption_resolution,[],[f3352,f198])).

fof(f3352,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_459 ),
    inference(subsumption_resolution,[],[f3351,f205])).

fof(f3351,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ v1_compts_1(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_459 ),
    inference(subsumption_resolution,[],[f3350,f212])).

fof(f3350,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK4(sK1)),k10_yellow_6(sK1,sK4(sK1)))
    | ~ l1_waybel_9(sK1)
    | ~ v1_compts_1(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_459 ),
    inference(subsumption_resolution,[],[f3349,f3211])).

fof(f3211,plain,
    ( ~ m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ spl11_459 ),
    inference(avatar_component_clause,[],[f3210])).

fof(f3386,plain,
    ( ~ spl11_489
    | ~ spl11_480 ),
    inference(avatar_split_clause,[],[f3363,f3324,f3384])).

fof(f3384,plain,
    ( spl11_489
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)),sK6(u1_waybel_0(sK10,sK2(sK10)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_489])])).

fof(f3324,plain,
    ( spl11_480
  <=> r2_hidden(sK6(u1_waybel_0(sK10,sK2(sK10))),k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_480])])).

fof(f3363,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)),sK6(u1_waybel_0(sK10,sK2(sK10))))
    | ~ spl11_480 ),
    inference(resolution,[],[f3325,f135])).

fof(f3325,plain,
    ( r2_hidden(sK6(u1_waybel_0(sK10,sK2(sK10))),k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)))
    | ~ spl11_480 ),
    inference(avatar_component_clause,[],[f3324])).

fof(f3379,plain,
    ( spl11_486
    | ~ spl11_480 ),
    inference(avatar_split_clause,[],[f3362,f3324,f3377])).

fof(f3377,plain,
    ( spl11_486
  <=> m1_subset_1(sK6(u1_waybel_0(sK10,sK2(sK10))),k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_486])])).

fof(f3362,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK10,sK2(sK10))),k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)))
    | ~ spl11_480 ),
    inference(resolution,[],[f3325,f136])).

fof(f3372,plain,
    ( ~ spl11_485
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_480 ),
    inference(avatar_split_clause,[],[f3365,f3324,f288,f278,f3370])).

fof(f3370,plain,
    ( spl11_485
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_485])])).

fof(f3365,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_480 ),
    inference(forward_demodulation,[],[f3361,f289])).

fof(f3361,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_480 ),
    inference(resolution,[],[f3325,f281])).

fof(f3348,plain,
    ( spl11_482
    | ~ spl11_478 ),
    inference(avatar_split_clause,[],[f3327,f3318,f3346])).

fof(f3346,plain,
    ( spl11_482
  <=> u1_waybel_0(sK10,sK2(sK10)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_482])])).

fof(f3318,plain,
    ( spl11_478
  <=> v1_xboole_0(u1_waybel_0(sK10,sK2(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_478])])).

fof(f3327,plain,
    ( u1_waybel_0(sK10,sK2(sK10)) = k1_xboole_0
    | ~ spl11_478 ),
    inference(resolution,[],[f3319,f117])).

fof(f3319,plain,
    ( v1_xboole_0(u1_waybel_0(sK10,sK2(sK10)))
    | ~ spl11_478 ),
    inference(avatar_component_clause,[],[f3318])).

fof(f3326,plain,
    ( spl11_478
    | spl11_480
    | ~ spl11_474 ),
    inference(avatar_split_clause,[],[f3310,f3285,f3324,f3318])).

fof(f3285,plain,
    ( spl11_474
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK10,sK2(sK10)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_474])])).

fof(f3310,plain,
    ( r2_hidden(sK6(u1_waybel_0(sK10,sK2(sK10))),k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)))
    | v1_xboole_0(u1_waybel_0(sK10,sK2(sK10)))
    | ~ spl11_474 ),
    inference(resolution,[],[f3286,f267])).

fof(f3286,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK10,sK2(sK10)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))) )
    | ~ spl11_474 ),
    inference(avatar_component_clause,[],[f3285])).

fof(f3309,plain,
    ( spl11_476
    | ~ spl11_472 ),
    inference(avatar_split_clause,[],[f3288,f3282,f3307])).

fof(f3307,plain,
    ( spl11_476
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_476])])).

fof(f3282,plain,
    ( spl11_472
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_472])])).

fof(f3288,plain,
    ( k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))
    | ~ spl11_472 ),
    inference(resolution,[],[f3283,f117])).

fof(f3283,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)))
    | ~ spl11_472 ),
    inference(avatar_component_clause,[],[f3282])).

fof(f3287,plain,
    ( spl11_472
    | spl11_474
    | ~ spl11_434 ),
    inference(avatar_split_clause,[],[f3108,f3089,f3285,f3282])).

fof(f3089,plain,
    ( spl11_434
  <=> m1_subset_1(u1_waybel_0(sK10,sK2(sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_434])])).

fof(f3108,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK10,sK2(sK10)))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))) )
    | ~ spl11_434 ),
    inference(resolution,[],[f3106,f137])).

fof(f3106,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)))
        | ~ r2_hidden(X0,u1_waybel_0(sK10,sK2(sK10))) )
    | ~ spl11_434 ),
    inference(resolution,[],[f3090,f144])).

fof(f3090,plain,
    ( m1_subset_1(u1_waybel_0(sK10,sK2(sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))))
    | ~ spl11_434 ),
    inference(avatar_component_clause,[],[f3089])).

fof(f3277,plain,
    ( spl11_468
    | ~ spl11_471
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_462 ),
    inference(avatar_split_clause,[],[f3258,f3229,f288,f278,f3275,f3269])).

fof(f3269,plain,
    ( spl11_468
  <=> ! [X0] : ~ r2_hidden(X0,u1_waybel_0(sK9,sK2(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_468])])).

fof(f3275,plain,
    ( spl11_471
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_471])])).

fof(f3229,plain,
    ( spl11_462
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK9,sK2(sK9)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_462])])).

fof(f3258,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)),k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X0,u1_waybel_0(sK9,sK2(sK9))) )
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_462 ),
    inference(forward_demodulation,[],[f3254,f289])).

fof(f3254,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK9,sK2(sK9)))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl11_32
    | ~ spl11_462 ),
    inference(resolution,[],[f3230,f281])).

fof(f3230,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)))
        | ~ r2_hidden(X0,u1_waybel_0(sK9,sK2(sK9))) )
    | ~ spl11_462 ),
    inference(avatar_component_clause,[],[f3229])).

fof(f3267,plain,
    ( ~ spl11_467
    | ~ spl11_462 ),
    inference(avatar_split_clause,[],[f3260,f3229,f3265])).

fof(f3265,plain,
    ( spl11_467
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)),u1_waybel_0(sK9,sK2(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_467])])).

fof(f3260,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)),u1_waybel_0(sK9,sK2(sK9)))
    | ~ spl11_462 ),
    inference(duplicate_literal_removal,[],[f3259])).

fof(f3259,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)),u1_waybel_0(sK9,sK2(sK9)))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)),u1_waybel_0(sK9,sK2(sK9)))
    | ~ spl11_462 ),
    inference(resolution,[],[f3256,f3230])).

fof(f3256,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)),X2)
        | ~ r2_hidden(X2,u1_waybel_0(sK9,sK2(sK9))) )
    | ~ spl11_462 ),
    inference(resolution,[],[f3230,f135])).

fof(f3253,plain,
    ( spl11_464
    | ~ spl11_460 ),
    inference(avatar_split_clause,[],[f3232,f3226,f3251])).

fof(f3251,plain,
    ( spl11_464
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_464])])).

fof(f3226,plain,
    ( spl11_460
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_460])])).

fof(f3232,plain,
    ( k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))
    | ~ spl11_460 ),
    inference(resolution,[],[f3227,f117])).

fof(f3227,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)))
    | ~ spl11_460 ),
    inference(avatar_component_clause,[],[f3226])).

fof(f3231,plain,
    ( spl11_460
    | spl11_462
    | ~ spl11_420 ),
    inference(avatar_split_clause,[],[f3016,f2970,f3229,f3226])).

fof(f2970,plain,
    ( spl11_420
  <=> m1_subset_1(u1_waybel_0(sK9,sK2(sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_420])])).

fof(f3016,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK9,sK2(sK9)))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))) )
    | ~ spl11_420 ),
    inference(resolution,[],[f3007,f137])).

fof(f3007,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)))
        | ~ r2_hidden(X0,u1_waybel_0(sK9,sK2(sK9))) )
    | ~ spl11_420 ),
    inference(resolution,[],[f2971,f144])).

fof(f2971,plain,
    ( m1_subset_1(u1_waybel_0(sK9,sK2(sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))))
    | ~ spl11_420 ),
    inference(avatar_component_clause,[],[f2970])).

fof(f3212,plain,
    ( ~ spl11_459
    | spl11_455 ),
    inference(avatar_split_clause,[],[f3205,f3196,f3210])).

fof(f3205,plain,
    ( ~ m1_subset_1(sK3(sK1),u1_struct_0(sK1))
    | ~ spl11_455 ),
    inference(resolution,[],[f3197,f110])).

fof(f110,plain,(
    ! [X1] :
      ( v5_pre_topc(k4_waybel_1(sK1,X1),sK1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,
    ( ~ v2_waybel_2(sK1)
    & ! [X1] :
        ( v5_pre_topc(k4_waybel_1(sK1,X1),sK1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    & l1_waybel_9(sK1)
    & v1_compts_1(sK1)
    & v2_lattice3(sK1)
    & v1_lattice3(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & v8_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f78])).

fof(f78,plain,
    ( ? [X0] :
        ( ~ v2_waybel_2(X0)
        & ! [X1] :
            ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ~ v2_waybel_2(sK1)
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(sK1,X1),sK1,sK1)
          | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_waybel_9(sK1)
      & v1_compts_1(sK1)
      & v2_lattice3(sK1)
      & v1_lattice3(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & v8_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ~ v2_waybel_2(X0)
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ~ v2_waybel_2(X0)
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
         => v2_waybel_2(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
       => v2_waybel_2(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t41_waybel_9)).

fof(f3197,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ spl11_455 ),
    inference(avatar_component_clause,[],[f3196])).

fof(f3204,plain,
    ( ~ spl11_455
    | spl11_456
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(avatar_split_clause,[],[f3191,f1101,f1094,f1060,f211,f204,f197,f190,f183,f176,f169,f162,f155,f3202,f3196])).

fof(f3191,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f3190,f1102])).

fof(f3190,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3189,f156])).

fof(f3189,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3188,f163])).

fof(f3188,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3187,f170])).

fof(f3187,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3186,f177])).

fof(f3186,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3185,f184])).

fof(f3185,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3184,f191])).

fof(f3184,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3183,f198])).

fof(f3183,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3182,f205])).

fof(f3182,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ v1_compts_1(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_16
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f3181,f212])).

fof(f3181,plain,
    ( r1_waybel_9(sK1,sK4(sK1))
    | ~ v5_pre_topc(k4_waybel_1(sK1,sK3(sK1)),sK1,sK1)
    | ~ l1_waybel_9(sK1)
    | ~ v1_compts_1(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_182
    | ~ spl11_188 ),
    inference(resolution,[],[f2309,f1095])).

fof(f2309,plain,
    ( ! [X0] :
        ( ~ v10_waybel_0(sK4(sK1),X0)
        | r1_waybel_9(X0,sK4(sK1))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        | ~ l1_waybel_9(X0)
        | ~ v1_compts_1(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v8_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_waybel_0(sK4(sK1),X0) )
    | ~ spl11_182 ),
    inference(resolution,[],[f1195,f1061])).

fof(f1195,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0)
      | ~ l1_waybel_0(sK4(X0),X1)
      | r1_waybel_9(X1,sK4(X0))
      | ~ v5_pre_topc(k4_waybel_1(X1,sK3(X1)),X1,X1)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ v10_waybel_0(sK4(X0),X1) ) ),
    inference(subsumption_resolution,[],[f1194,f126])).

fof(f1194,plain,(
    ! [X0,X1] :
      ( ~ v10_waybel_0(sK4(X0),X1)
      | ~ l1_waybel_0(sK4(X0),X1)
      | r1_waybel_9(X1,sK4(X0))
      | v2_struct_0(sK4(X0))
      | ~ v5_pre_topc(k4_waybel_1(X1,sK3(X1)),X1,X1)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ sP0(X0) ) ),
    inference(subsumption_resolution,[],[f1193,f127])).

fof(f1193,plain,(
    ! [X0,X1] :
      ( ~ v10_waybel_0(sK4(X0),X1)
      | ~ l1_waybel_0(sK4(X0),X1)
      | r1_waybel_9(X1,sK4(X0))
      | ~ v4_orders_2(sK4(X0))
      | v2_struct_0(sK4(X0))
      | ~ v5_pre_topc(k4_waybel_1(X1,sK3(X1)),X1,X1)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f123,f128])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_9(X0,X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f3180,plain,
    ( spl11_96
    | spl11_452
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f3176,f232,f3178,f654])).

fof(f654,plain,
    ( spl11_96
  <=> v2_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_96])])).

fof(f3178,plain,
    ( spl11_452
  <=> ! [X1] :
        ( m1_subset_1(sK6(k4_waybel_1(sK8,X1)),k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)))
        | v1_xboole_0(k4_waybel_1(sK8,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_452])])).

fof(f232,plain,
    ( spl11_22
  <=> l1_waybel_9(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f3176,plain,
    ( ! [X1] :
        ( m1_subset_1(sK6(k4_waybel_1(sK8,X1)),k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)))
        | ~ m1_subset_1(X1,u1_struct_0(sK8))
        | v1_xboole_0(k4_waybel_1(sK8,X1))
        | v2_struct_0(sK8) )
    | ~ spl11_22 ),
    inference(resolution,[],[f3031,f233])).

fof(f233,plain,
    ( l1_waybel_9(sK8)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f232])).

fof(f3031,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_9(X0)
      | m1_subset_1(sK6(k4_waybel_1(X0,X1)),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(k4_waybel_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f1553,f116])).

fof(f116,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',dt_l1_waybel_9)).

fof(f1553,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK6(k4_waybel_1(X0,X1)),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(k4_waybel_1(X0,X1)) ) ),
    inference(resolution,[],[f568,f267])).

fof(f568,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_waybel_1(X1,X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | m1_subset_1(X2,k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f140,f144])).

fof(f140,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',dt_k4_waybel_1)).

fof(f3171,plain,
    ( ~ spl11_451
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_442 ),
    inference(avatar_split_clause,[],[f3150,f3121,f288,f278,f3169])).

fof(f3169,plain,
    ( spl11_451
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_451])])).

fof(f3150,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_442 ),
    inference(forward_demodulation,[],[f3146,f289])).

fof(f3146,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_442 ),
    inference(resolution,[],[f3122,f281])).

fof(f3164,plain,
    ( ~ spl11_449
    | ~ spl11_442 ),
    inference(avatar_split_clause,[],[f3148,f3121,f3162])).

fof(f3162,plain,
    ( spl11_449
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))),u1_waybel_0(sK7,sK2(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_449])])).

fof(f3148,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))),u1_waybel_0(sK7,sK2(sK7)))
    | ~ spl11_442 ),
    inference(resolution,[],[f3122,f135])).

fof(f3157,plain,
    ( spl11_446
    | ~ spl11_442 ),
    inference(avatar_split_clause,[],[f3147,f3121,f3155])).

fof(f3147,plain,
    ( m1_subset_1(u1_waybel_0(sK7,sK2(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))))
    | ~ spl11_442 ),
    inference(resolution,[],[f3122,f136])).

fof(f3145,plain,
    ( spl11_444
    | ~ spl11_440 ),
    inference(avatar_split_clause,[],[f3124,f3115,f3143])).

fof(f3143,plain,
    ( spl11_444
  <=> k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_444])])).

fof(f3115,plain,
    ( spl11_440
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_440])])).

fof(f3124,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7)))
    | ~ spl11_440 ),
    inference(resolution,[],[f3116,f117])).

fof(f3116,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))))
    | ~ spl11_440 ),
    inference(avatar_component_clause,[],[f3115])).

fof(f3123,plain,
    ( spl11_440
    | spl11_442
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f3109,f225,f3121,f3115])).

fof(f225,plain,
    ( spl11_20
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f3109,plain,
    ( r2_hidden(u1_waybel_0(sK7,sK2(sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK7)),u1_struct_0(sK7))))
    | ~ spl11_20 ),
    inference(resolution,[],[f2930,f226])).

fof(f226,plain,
    ( l1_pre_topc(sK7)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f225])).

fof(f2930,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | r2_hidden(u1_waybel_0(X1,sK2(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(X1)),u1_struct_0(X1))))
      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(X1)),u1_struct_0(X1)))) ) ),
    inference(resolution,[],[f544,f114])).

fof(f114,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',dt_l1_pre_topc)).

fof(f544,plain,(
    ! [X2] :
      ( ~ l1_struct_0(X2)
      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(X2)),u1_struct_0(X2))))
      | r2_hidden(u1_waybel_0(X2,sK2(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(X2)),u1_struct_0(X2)))) ) ),
    inference(resolution,[],[f542,f137])).

fof(f542,plain,(
    ! [X0] :
      ( m1_subset_1(u1_waybel_0(X0,sK2(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(X0)),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f541])).

fof(f541,plain,(
    ! [X0] :
      ( m1_subset_1(u1_waybel_0(X0,sK2(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(X0)),u1_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f141,f119])).

fof(f119,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
     => l1_waybel_0(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] : l1_waybel_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',existence_l1_waybel_0)).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',dt_u1_waybel_0)).

fof(f3105,plain,
    ( ~ spl11_439
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_430 ),
    inference(avatar_split_clause,[],[f3084,f3053,f288,f278,f3103])).

fof(f3103,plain,
    ( spl11_439
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_439])])).

fof(f3053,plain,
    ( spl11_430
  <=> r2_hidden(u1_waybel_0(sK10,sK2(sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_430])])).

fof(f3084,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_430 ),
    inference(forward_demodulation,[],[f3080,f289])).

fof(f3080,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_430 ),
    inference(resolution,[],[f3054,f281])).

fof(f3054,plain,
    ( r2_hidden(u1_waybel_0(sK10,sK2(sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))))
    | ~ spl11_430 ),
    inference(avatar_component_clause,[],[f3053])).

fof(f3098,plain,
    ( ~ spl11_437
    | ~ spl11_430 ),
    inference(avatar_split_clause,[],[f3082,f3053,f3096])).

fof(f3096,plain,
    ( spl11_437
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))),u1_waybel_0(sK10,sK2(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_437])])).

fof(f3082,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))),u1_waybel_0(sK10,sK2(sK10)))
    | ~ spl11_430 ),
    inference(resolution,[],[f3054,f135])).

fof(f3091,plain,
    ( spl11_434
    | ~ spl11_430 ),
    inference(avatar_split_clause,[],[f3081,f3053,f3089])).

fof(f3081,plain,
    ( m1_subset_1(u1_waybel_0(sK10,sK2(sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))))
    | ~ spl11_430 ),
    inference(resolution,[],[f3054,f136])).

fof(f3077,plain,
    ( spl11_432
    | ~ spl11_428 ),
    inference(avatar_split_clause,[],[f3056,f3047,f3075])).

fof(f3075,plain,
    ( spl11_432
  <=> k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_432])])).

fof(f3047,plain,
    ( spl11_428
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_428])])).

fof(f3056,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10)))
    | ~ spl11_428 ),
    inference(resolution,[],[f3048,f117])).

fof(f3048,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))))
    | ~ spl11_428 ),
    inference(avatar_component_clause,[],[f3047])).

fof(f3055,plain,
    ( spl11_428
    | spl11_430
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f3041,f246,f3053,f3047])).

fof(f246,plain,
    ( spl11_26
  <=> l1_orders_2(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f3041,plain,
    ( r2_hidden(u1_waybel_0(sK10,sK2(sK10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK10)),u1_struct_0(sK10))))
    | ~ spl11_26 ),
    inference(resolution,[],[f2929,f247])).

fof(f247,plain,
    ( l1_orders_2(sK10)
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f246])).

fof(f2929,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(u1_waybel_0(X0,sK2(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(X0)),u1_struct_0(X0))))
      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(X0)),u1_struct_0(X0)))) ) ),
    inference(resolution,[],[f544,f120])).

fof(f120,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',dt_l1_orders_2)).

fof(f3015,plain,
    ( ~ spl11_427
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_416 ),
    inference(avatar_split_clause,[],[f2964,f2951,f288,f278,f3013])).

fof(f3013,plain,
    ( spl11_427
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_427])])).

fof(f2951,plain,
    ( spl11_416
  <=> r2_hidden(u1_waybel_0(sK9,sK2(sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_416])])).

fof(f2964,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_416 ),
    inference(forward_demodulation,[],[f2960,f289])).

fof(f2960,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_416 ),
    inference(resolution,[],[f2952,f281])).

fof(f2952,plain,
    ( r2_hidden(u1_waybel_0(sK9,sK2(sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))))
    | ~ spl11_416 ),
    inference(avatar_component_clause,[],[f2951])).

fof(f3006,plain,
    ( ~ spl11_425
    | ~ spl11_416 ),
    inference(avatar_split_clause,[],[f2962,f2951,f3004])).

fof(f3004,plain,
    ( spl11_425
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))),u1_waybel_0(sK9,sK2(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_425])])).

fof(f2962,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))),u1_waybel_0(sK9,sK2(sK9)))
    | ~ spl11_416 ),
    inference(resolution,[],[f2952,f135])).

fof(f2994,plain,
    ( spl11_422
    | ~ spl11_418 ),
    inference(avatar_split_clause,[],[f2973,f2957,f2992])).

fof(f2992,plain,
    ( spl11_422
  <=> k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_422])])).

fof(f2957,plain,
    ( spl11_418
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_418])])).

fof(f2973,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)))
    | ~ spl11_418 ),
    inference(resolution,[],[f2958,f117])).

fof(f2958,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))))
    | ~ spl11_418 ),
    inference(avatar_component_clause,[],[f2957])).

fof(f2972,plain,
    ( spl11_420
    | ~ spl11_416 ),
    inference(avatar_split_clause,[],[f2961,f2951,f2970])).

fof(f2961,plain,
    ( m1_subset_1(u1_waybel_0(sK9,sK2(sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))))
    | ~ spl11_416 ),
    inference(resolution,[],[f2952,f136])).

fof(f2965,plain,
    ( ~ spl11_419
    | ~ spl11_416 ),
    inference(avatar_split_clause,[],[f2963,f2951,f2954])).

fof(f2954,plain,
    ( spl11_419
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_419])])).

fof(f2963,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))))
    | ~ spl11_416 ),
    inference(resolution,[],[f2952,f143])).

fof(f2959,plain,
    ( spl11_416
    | spl11_418
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f2935,f239,f2957,f2951])).

fof(f239,plain,
    ( spl11_24
  <=> l1_struct_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f2935,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))))
    | r2_hidden(u1_waybel_0(sK9,sK2(sK9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK9)),u1_struct_0(sK9))))
    | ~ spl11_24 ),
    inference(resolution,[],[f544,f240])).

fof(f240,plain,
    ( l1_struct_0(sK9)
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f239])).

fof(f2864,plain,
    ( ~ spl11_391
    | spl11_414
    | ~ spl11_354 ),
    inference(avatar_split_clause,[],[f2428,f2421,f2862,f2585])).

fof(f2585,plain,
    ( spl11_391
  <=> ~ l1_struct_0(sK2(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_391])])).

fof(f2862,plain,
    ( spl11_414
  <=> ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0))
        | ~ r2_hidden(X1,u1_waybel_0(sK2(sK8),sK2(sK2(sK8)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_414])])).

fof(f2421,plain,
    ( spl11_354
  <=> u1_struct_0(sK2(sK8)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_354])])).

fof(f2428,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0))
        | ~ l1_struct_0(sK2(sK8))
        | ~ r2_hidden(X1,u1_waybel_0(sK2(sK8),sK2(sK2(sK8)))) )
    | ~ spl11_354 ),
    inference(superposition,[],[f543,f2422])).

fof(f2422,plain,
    ( u1_struct_0(sK2(sK8)) = k1_xboole_0
    | ~ spl11_354 ),
    inference(avatar_component_clause,[],[f2421])).

fof(f543,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(sK2(X0)),u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ r2_hidden(X1,u1_waybel_0(X0,sK2(X0))) ) ),
    inference(resolution,[],[f542,f144])).

fof(f2860,plain,
    ( spl11_410
    | spl11_218
    | spl11_412
    | ~ spl11_196
    | ~ spl11_206 ),
    inference(avatar_split_clause,[],[f1236,f1186,f1143,f2858,f1254,f2852])).

fof(f2852,plain,
    ( spl11_410
  <=> v1_xboole_0(sK6(k1_zfmisc_1(u1_waybel_0(sK1,sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_410])])).

fof(f1254,plain,
    ( spl11_218
  <=> v1_xboole_0(u1_waybel_0(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_218])])).

fof(f2858,plain,
    ( spl11_412
  <=> m1_subset_1(sK6(sK6(k1_zfmisc_1(u1_waybel_0(sK1,sK4(sK1))))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_412])])).

fof(f1143,plain,
    ( spl11_196
  <=> m1_subset_1(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_196])])).

fof(f1186,plain,
    ( spl11_206
  <=> u1_struct_0(sK4(sK1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_206])])).

fof(f1236,plain,
    ( m1_subset_1(sK6(sK6(k1_zfmisc_1(u1_waybel_0(sK1,sK4(sK1))))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_waybel_0(sK1,sK4(sK1)))
    | v1_xboole_0(sK6(k1_zfmisc_1(u1_waybel_0(sK1,sK4(sK1)))))
    | ~ spl11_196
    | ~ spl11_206 ),
    inference(resolution,[],[f1196,f329])).

fof(f329,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK6(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(sK6(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f327,f137])).

fof(f327,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK6(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK6(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f325,f267])).

fof(f325,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK6(k1_zfmisc_1(X1)))
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f144,f134])).

fof(f1196,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK1,sK4(sK1)))
        | m1_subset_1(X0,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) )
    | ~ spl11_196
    | ~ spl11_206 ),
    inference(superposition,[],[f1146,f1187])).

fof(f1187,plain,
    ( u1_struct_0(sK4(sK1)) = k1_xboole_0
    | ~ spl11_206 ),
    inference(avatar_component_clause,[],[f1186])).

fof(f1146,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1)))
        | ~ r2_hidden(X0,u1_waybel_0(sK1,sK4(sK1))) )
    | ~ spl11_196 ),
    inference(resolution,[],[f1144,f144])).

fof(f1144,plain,
    ( m1_subset_1(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))))
    | ~ spl11_196 ),
    inference(avatar_component_clause,[],[f1143])).

fof(f2727,plain,
    ( ~ spl11_409
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_404 ),
    inference(avatar_split_clause,[],[f2720,f2691,f288,f278,f2725])).

fof(f2725,plain,
    ( spl11_409
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_409])])).

fof(f2691,plain,
    ( spl11_404
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_404])])).

fof(f2720,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_404 ),
    inference(forward_demodulation,[],[f2716,f289])).

fof(f2716,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_404 ),
    inference(resolution,[],[f2692,f281])).

fof(f2692,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))))
    | ~ spl11_404 ),
    inference(avatar_component_clause,[],[f2691])).

fof(f2715,plain,
    ( spl11_406
    | ~ spl11_402 ),
    inference(avatar_split_clause,[],[f2694,f2685,f2713])).

fof(f2713,plain,
    ( spl11_406
  <=> k1_xboole_0 = k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_406])])).

fof(f2685,plain,
    ( spl11_402
  <=> v1_xboole_0(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_402])])).

fof(f2694,plain,
    ( k1_xboole_0 = k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1)))
    | ~ spl11_402 ),
    inference(resolution,[],[f2686,f117])).

fof(f2686,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))))
    | ~ spl11_402 ),
    inference(avatar_component_clause,[],[f2685])).

fof(f2693,plain,
    ( spl11_402
    | spl11_404
    | ~ spl11_398 ),
    inference(avatar_split_clause,[],[f2670,f2660,f2691,f2685])).

fof(f2660,plain,
    ( spl11_398
  <=> k1_xboole_0 = sK6(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_398])])).

fof(f2670,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))))
    | v1_xboole_0(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))))
    | ~ spl11_398 ),
    inference(superposition,[],[f267,f2661])).

fof(f2661,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))))
    | ~ spl11_398 ),
    inference(avatar_component_clause,[],[f2660])).

fof(f2678,plain,
    ( spl11_400
    | ~ spl11_398 ),
    inference(avatar_split_clause,[],[f2671,f2660,f2676])).

fof(f2676,plain,
    ( spl11_400
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_400])])).

fof(f2671,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))))
    | ~ spl11_398 ),
    inference(superposition,[],[f134,f2661])).

fof(f2662,plain,
    ( spl11_398
    | ~ spl11_394 ),
    inference(avatar_split_clause,[],[f2641,f2632,f2660])).

fof(f2632,plain,
    ( spl11_394
  <=> v1_xboole_0(sK6(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_394])])).

fof(f2641,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))))
    | ~ spl11_394 ),
    inference(resolution,[],[f2633,f117])).

fof(f2633,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1)))))
    | ~ spl11_394 ),
    inference(avatar_component_clause,[],[f2632])).

fof(f2640,plain,
    ( spl11_394
    | spl11_156
    | spl11_396
    | ~ spl11_148 ),
    inference(avatar_split_clause,[],[f942,f904,f2638,f951,f2632])).

fof(f951,plain,
    ( spl11_156
  <=> v1_xboole_0(u1_waybel_0(sK1,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_156])])).

fof(f2638,plain,
    ( spl11_396
  <=> m1_subset_1(sK6(sK6(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_396])])).

fof(f904,plain,
    ( spl11_148
  <=> m1_subset_1(u1_waybel_0(sK1,sK2(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_148])])).

fof(f942,plain,
    ( m1_subset_1(sK6(sK6(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1))))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_waybel_0(sK1,sK2(sK1)))
    | v1_xboole_0(sK6(k1_zfmisc_1(u1_waybel_0(sK1,sK2(sK1)))))
    | ~ spl11_148 ),
    inference(resolution,[],[f930,f329])).

fof(f930,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK1,sK2(sK1)))
        | m1_subset_1(X0,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) )
    | ~ spl11_148 ),
    inference(resolution,[],[f905,f144])).

fof(f905,plain,
    ( m1_subset_1(u1_waybel_0(sK1,sK2(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_148 ),
    inference(avatar_component_clause,[],[f904])).

fof(f2596,plain,
    ( ~ spl11_361
    | spl11_391 ),
    inference(avatar_split_clause,[],[f2594,f2585,f2459])).

fof(f2459,plain,
    ( spl11_361
  <=> ~ l1_orders_2(sK2(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_361])])).

fof(f2594,plain,
    ( ~ l1_orders_2(sK2(sK8))
    | ~ spl11_391 ),
    inference(resolution,[],[f2586,f120])).

fof(f2586,plain,
    ( ~ l1_struct_0(sK2(sK8))
    | ~ spl11_391 ),
    inference(avatar_component_clause,[],[f2585])).

fof(f2593,plain,
    ( ~ spl11_391
    | spl11_392
    | ~ spl11_354 ),
    inference(avatar_split_clause,[],[f2430,f2421,f2591,f2585])).

fof(f2430,plain,
    ( m1_subset_1(u1_waybel_0(sK2(sK8),sK2(sK2(sK8))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK8))),k1_xboole_0)))
    | ~ l1_struct_0(sK2(sK8))
    | ~ spl11_354 ),
    inference(superposition,[],[f542,f2422])).

fof(f2579,plain,
    ( ~ spl11_389
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_382 ),
    inference(avatar_split_clause,[],[f2564,f2551,f288,f278,f2577])).

fof(f2577,plain,
    ( spl11_389
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_389])])).

fof(f2551,plain,
    ( spl11_382
  <=> r2_hidden(u1_waybel_0(sK8,sK2(sK8)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_382])])).

fof(f2564,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_382 ),
    inference(forward_demodulation,[],[f2560,f289])).

fof(f2560,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_382 ),
    inference(resolution,[],[f2552,f281])).

fof(f2552,plain,
    ( r2_hidden(u1_waybel_0(sK8,sK2(sK8)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))))
    | ~ spl11_382 ),
    inference(avatar_component_clause,[],[f2551])).

fof(f2572,plain,
    ( ~ spl11_387
    | ~ spl11_382 ),
    inference(avatar_split_clause,[],[f2562,f2551,f2570])).

fof(f2570,plain,
    ( spl11_387
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))),u1_waybel_0(sK8,sK2(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_387])])).

fof(f2562,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))),u1_waybel_0(sK8,sK2(sK8)))
    | ~ spl11_382 ),
    inference(resolution,[],[f2552,f135])).

fof(f2565,plain,
    ( ~ spl11_385
    | ~ spl11_382 ),
    inference(avatar_split_clause,[],[f2563,f2551,f2554])).

fof(f2554,plain,
    ( spl11_385
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_385])])).

fof(f2563,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))))
    | ~ spl11_382 ),
    inference(resolution,[],[f2552,f143])).

fof(f2559,plain,
    ( spl11_382
    | spl11_384
    | ~ spl11_358 ),
    inference(avatar_split_clause,[],[f2452,f2444,f2557,f2551])).

fof(f2557,plain,
    ( spl11_384
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_384])])).

fof(f2444,plain,
    ( spl11_358
  <=> m1_subset_1(u1_waybel_0(sK8,sK2(sK8)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_358])])).

fof(f2452,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))))
    | r2_hidden(u1_waybel_0(sK8,sK2(sK8)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))))
    | ~ spl11_358 ),
    inference(resolution,[],[f2445,f137])).

fof(f2445,plain,
    ( m1_subset_1(u1_waybel_0(sK8,sK2(sK8)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))))
    | ~ spl11_358 ),
    inference(avatar_component_clause,[],[f2444])).

fof(f2546,plain,
    ( spl11_352
    | ~ spl11_361
    | spl11_380
    | ~ spl11_354 ),
    inference(avatar_split_clause,[],[f2431,f2421,f2544,f2459,f2399])).

fof(f2399,plain,
    ( spl11_352
  <=> v2_struct_0(sK2(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_352])])).

fof(f2544,plain,
    ( spl11_380
  <=> ! [X3] :
        ( m1_subset_1(k1_waybel_2(sK2(sK8),X3),k1_xboole_0)
        | ~ l1_waybel_0(X3,sK2(sK8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_380])])).

fof(f2431,plain,
    ( ! [X3] :
        ( m1_subset_1(k1_waybel_2(sK2(sK8),X3),k1_xboole_0)
        | ~ l1_waybel_0(X3,sK2(sK8))
        | ~ l1_orders_2(sK2(sK8))
        | v2_struct_0(sK2(sK8)) )
    | ~ spl11_354 ),
    inference(superposition,[],[f139,f2422])).

fof(f139,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_waybel_2(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_waybel_2(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_waybel_2(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_waybel_2(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',dt_k1_waybel_2)).

fof(f2542,plain,
    ( ~ spl11_379
    | ~ spl11_372 ),
    inference(avatar_split_clause,[],[f2525,f2514,f2540])).

fof(f2540,plain,
    ( spl11_379
  <=> ~ r2_hidden(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)),sK6(u1_waybel_0(sK8,sK2(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_379])])).

fof(f2514,plain,
    ( spl11_372
  <=> r2_hidden(sK6(u1_waybel_0(sK8,sK2(sK8))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_372])])).

fof(f2525,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)),sK6(u1_waybel_0(sK8,sK2(sK8))))
    | ~ spl11_372 ),
    inference(resolution,[],[f2515,f135])).

fof(f2515,plain,
    ( r2_hidden(sK6(u1_waybel_0(sK8,sK2(sK8))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)))
    | ~ spl11_372 ),
    inference(avatar_component_clause,[],[f2514])).

fof(f2535,plain,
    ( ~ spl11_377
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_372 ),
    inference(avatar_split_clause,[],[f2527,f2514,f288,f278,f2533])).

fof(f2533,plain,
    ( spl11_377
  <=> ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_377])])).

fof(f2527,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_372 ),
    inference(forward_demodulation,[],[f2523,f289])).

fof(f2523,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_372 ),
    inference(resolution,[],[f2515,f281])).

fof(f2528,plain,
    ( ~ spl11_375
    | ~ spl11_372 ),
    inference(avatar_split_clause,[],[f2526,f2514,f2517])).

fof(f2517,plain,
    ( spl11_375
  <=> ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_375])])).

fof(f2526,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)))
    | ~ spl11_372 ),
    inference(resolution,[],[f2515,f143])).

fof(f2522,plain,
    ( spl11_372
    | spl11_374
    | ~ spl11_368 ),
    inference(avatar_split_clause,[],[f2509,f2484,f2520,f2514])).

fof(f2520,plain,
    ( spl11_374
  <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_374])])).

fof(f2484,plain,
    ( spl11_368
  <=> m1_subset_1(sK6(u1_waybel_0(sK8,sK2(sK8))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_368])])).

fof(f2509,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)))
    | r2_hidden(sK6(u1_waybel_0(sK8,sK2(sK8))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)))
    | ~ spl11_368 ),
    inference(resolution,[],[f2485,f137])).

fof(f2485,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK8,sK2(sK8))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)))
    | ~ spl11_368 ),
    inference(avatar_component_clause,[],[f2484])).

fof(f2508,plain,
    ( spl11_370
    | ~ spl11_366 ),
    inference(avatar_split_clause,[],[f2487,f2478,f2506])).

fof(f2506,plain,
    ( spl11_370
  <=> u1_waybel_0(sK8,sK2(sK8)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_370])])).

fof(f2478,plain,
    ( spl11_366
  <=> v1_xboole_0(u1_waybel_0(sK8,sK2(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_366])])).

fof(f2487,plain,
    ( u1_waybel_0(sK8,sK2(sK8)) = k1_xboole_0
    | ~ spl11_366 ),
    inference(resolution,[],[f2479,f117])).

fof(f2479,plain,
    ( v1_xboole_0(u1_waybel_0(sK8,sK2(sK8)))
    | ~ spl11_366 ),
    inference(avatar_component_clause,[],[f2478])).

fof(f2486,plain,
    ( spl11_366
    | spl11_368
    | ~ spl11_358 ),
    inference(avatar_split_clause,[],[f2453,f2444,f2484,f2478])).

fof(f2453,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK8,sK2(sK8))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)))
    | v1_xboole_0(u1_waybel_0(sK8,sK2(sK8)))
    | ~ spl11_358 ),
    inference(resolution,[],[f2451,f267])).

fof(f2451,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK8,sK2(sK8)))
        | m1_subset_1(X0,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))) )
    | ~ spl11_358 ),
    inference(resolution,[],[f2445,f144])).

fof(f2473,plain,
    ( ~ spl11_357
    | spl11_364
    | ~ spl11_354 ),
    inference(avatar_split_clause,[],[f2425,f2421,f2471,f2438])).

fof(f2438,plain,
    ( spl11_357
  <=> ~ l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_357])])).

fof(f2471,plain,
    ( spl11_364
  <=> ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)))
        | ~ r2_hidden(X0,u1_waybel_0(sK8,sK2(sK8))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_364])])).

fof(f2425,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8)))
        | ~ l1_struct_0(sK8)
        | ~ r2_hidden(X0,u1_waybel_0(sK8,sK2(sK8))) )
    | ~ spl11_354 ),
    inference(superposition,[],[f543,f2422])).

fof(f2469,plain,
    ( ~ spl11_356
    | spl11_361 ),
    inference(avatar_contradiction_clause,[],[f2468])).

fof(f2468,plain,
    ( $false
    | ~ spl11_356
    | ~ spl11_361 ),
    inference(subsumption_resolution,[],[f2466,f2436])).

fof(f2436,plain,
    ( l1_struct_0(sK8)
    | ~ spl11_356 ),
    inference(avatar_component_clause,[],[f2435])).

fof(f2435,plain,
    ( spl11_356
  <=> l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_356])])).

fof(f2466,plain,
    ( ~ l1_struct_0(sK8)
    | ~ spl11_361 ),
    inference(resolution,[],[f2460,f265])).

fof(f265,plain,(
    ! [X0] :
      ( l1_orders_2(sK2(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,(
    ! [X0] :
      ( l1_orders_2(sK2(X0))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f118,f119])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | l1_orders_2(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',dt_l1_waybel_0)).

fof(f2460,plain,
    ( ~ l1_orders_2(sK2(sK8))
    | ~ spl11_361 ),
    inference(avatar_component_clause,[],[f2459])).

fof(f2464,plain,
    ( spl11_352
    | ~ spl11_361
    | spl11_362
    | ~ spl11_272
    | ~ spl11_354 ),
    inference(avatar_split_clause,[],[f2433,f2421,f1497,f2462,f2459,f2399])).

fof(f2462,plain,
    ( spl11_362
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_xboole_0)
        | m1_subset_1(k4_waybel_1(sK2(sK8),X2),k1_zfmisc_1(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_362])])).

fof(f1497,plain,
    ( spl11_272
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_272])])).

fof(f2433,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_xboole_0)
        | m1_subset_1(k4_waybel_1(sK2(sK8),X2),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_orders_2(sK2(sK8))
        | v2_struct_0(sK2(sK8)) )
    | ~ spl11_272
    | ~ spl11_354 ),
    inference(forward_demodulation,[],[f2432,f2422])).

fof(f2432,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_waybel_1(sK2(sK8),X2),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X2,u1_struct_0(sK2(sK8)))
        | ~ l1_orders_2(sK2(sK8))
        | v2_struct_0(sK2(sK8)) )
    | ~ spl11_272
    | ~ spl11_354 ),
    inference(forward_demodulation,[],[f2429,f1498])).

fof(f1498,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl11_272 ),
    inference(avatar_component_clause,[],[f1497])).

fof(f2429,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_waybel_1(sK2(sK8),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK2(sK8)))
        | ~ l1_orders_2(sK2(sK8))
        | v2_struct_0(sK2(sK8)) )
    | ~ spl11_354 ),
    inference(superposition,[],[f140,f2422])).

fof(f2449,plain,
    ( ~ spl11_107
    | spl11_357 ),
    inference(avatar_split_clause,[],[f2447,f2438,f709])).

fof(f709,plain,
    ( spl11_107
  <=> ~ l1_orders_2(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_107])])).

fof(f2447,plain,
    ( ~ l1_orders_2(sK8)
    | ~ spl11_357 ),
    inference(resolution,[],[f2439,f120])).

fof(f2439,plain,
    ( ~ l1_struct_0(sK8)
    | ~ spl11_357 ),
    inference(avatar_component_clause,[],[f2438])).

fof(f2446,plain,
    ( ~ spl11_357
    | spl11_358
    | ~ spl11_354 ),
    inference(avatar_split_clause,[],[f2426,f2421,f2444,f2438])).

fof(f2426,plain,
    ( m1_subset_1(u1_waybel_0(sK8,sK2(sK8)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK8))))
    | ~ l1_struct_0(sK8)
    | ~ spl11_354 ),
    inference(superposition,[],[f542,f2422])).

fof(f2423,plain,
    ( spl11_354
    | ~ spl11_350 ),
    inference(avatar_split_clause,[],[f2402,f2393,f2421])).

fof(f2393,plain,
    ( spl11_350
  <=> v1_xboole_0(u1_struct_0(sK2(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_350])])).

fof(f2402,plain,
    ( u1_struct_0(sK2(sK8)) = k1_xboole_0
    | ~ spl11_350 ),
    inference(resolution,[],[f2394,f117])).

fof(f2394,plain,
    ( v1_xboole_0(u1_struct_0(sK2(sK8)))
    | ~ spl11_350 ),
    inference(avatar_component_clause,[],[f2393])).

fof(f2401,plain,
    ( spl11_348
    | spl11_350
    | spl11_352
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f851,f232,f2399,f2393,f2387])).

fof(f2387,plain,
    ( spl11_348
  <=> r2_hidden(k1_waybel_2(sK2(sK8),sK2(sK2(sK8))),u1_struct_0(sK2(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_348])])).

fof(f851,plain,
    ( v2_struct_0(sK2(sK8))
    | v1_xboole_0(u1_struct_0(sK2(sK8)))
    | r2_hidden(k1_waybel_2(sK2(sK8),sK2(sK2(sK8))),u1_struct_0(sK2(sK8)))
    | ~ spl11_22 ),
    inference(resolution,[],[f808,f233])).

fof(f808,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | v2_struct_0(sK2(X0))
      | v1_xboole_0(u1_struct_0(sK2(X0)))
      | r2_hidden(k1_waybel_2(sK2(X0),sK2(sK2(X0))),u1_struct_0(sK2(X0))) ) ),
    inference(resolution,[],[f750,f116])).

fof(f750,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(k1_waybel_2(sK2(X0),sK2(sK2(X0))),u1_struct_0(sK2(X0)))
      | v2_struct_0(sK2(X0))
      | v1_xboole_0(u1_struct_0(sK2(X0))) ) ),
    inference(resolution,[],[f574,f120])).

fof(f574,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | v1_xboole_0(u1_struct_0(sK2(X1)))
      | r2_hidden(k1_waybel_2(sK2(X1),sK2(sK2(X1))),u1_struct_0(sK2(X1)))
      | v2_struct_0(sK2(X1)) ) ),
    inference(resolution,[],[f571,f265])).

fof(f571,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r2_hidden(k1_waybel_2(X0,sK2(X0)),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f570,f120])).

fof(f570,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r2_hidden(k1_waybel_2(X0,sK2(X0)),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f347,f119])).

fof(f347,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,X1)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | r2_hidden(k1_waybel_2(X1,X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f139,f137])).

fof(f2350,plain,
    ( ~ spl11_347
    | ~ spl11_340 ),
    inference(avatar_split_clause,[],[f2333,f2322,f2348])).

fof(f2348,plain,
    ( spl11_347
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)),u1_waybel_0(sK2(sK1),sK2(sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_347])])).

fof(f2322,plain,
    ( spl11_340
  <=> r2_hidden(u1_waybel_0(sK2(sK1),sK2(sK2(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_340])])).

fof(f2333,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)),u1_waybel_0(sK2(sK1),sK2(sK2(sK1))))
    | ~ spl11_340 ),
    inference(resolution,[],[f2323,f135])).

fof(f2323,plain,
    ( r2_hidden(u1_waybel_0(sK2(sK1),sK2(sK2(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)))
    | ~ spl11_340 ),
    inference(avatar_component_clause,[],[f2322])).

fof(f2343,plain,
    ( ~ spl11_345
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_340 ),
    inference(avatar_split_clause,[],[f2335,f2322,f288,f278,f2341])).

fof(f2341,plain,
    ( spl11_345
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_345])])).

fof(f2335,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_340 ),
    inference(forward_demodulation,[],[f2331,f289])).

fof(f2331,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_340 ),
    inference(resolution,[],[f2323,f281])).

fof(f2336,plain,
    ( ~ spl11_343
    | ~ spl11_340 ),
    inference(avatar_split_clause,[],[f2334,f2322,f2325])).

fof(f2325,plain,
    ( spl11_343
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_343])])).

fof(f2334,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)))
    | ~ spl11_340 ),
    inference(resolution,[],[f2323,f143])).

fof(f2330,plain,
    ( spl11_340
    | spl11_342
    | ~ spl11_244 ),
    inference(avatar_split_clause,[],[f1386,f1378,f2328,f2322])).

fof(f2328,plain,
    ( spl11_342
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_342])])).

fof(f1378,plain,
    ( spl11_244
  <=> m1_subset_1(u1_waybel_0(sK2(sK1),sK2(sK2(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_244])])).

fof(f1386,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)))
    | r2_hidden(u1_waybel_0(sK2(sK1),sK2(sK2(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)))
    | ~ spl11_244 ),
    inference(resolution,[],[f1379,f137])).

fof(f1379,plain,
    ( m1_subset_1(u1_waybel_0(sK2(sK1),sK2(sK2(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)))
    | ~ spl11_244 ),
    inference(avatar_component_clause,[],[f1378])).

fof(f2316,plain,
    ( ~ spl11_339
    | ~ spl11_330 ),
    inference(avatar_split_clause,[],[f2291,f2280,f2314])).

fof(f2314,plain,
    ( spl11_339
  <=> ~ r2_hidden(u1_struct_0(sK2(sK2(sK1))),k1_waybel_2(sK2(sK2(sK1)),sK2(sK2(sK2(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_339])])).

fof(f2280,plain,
    ( spl11_330
  <=> r2_hidden(k1_waybel_2(sK2(sK2(sK1)),sK2(sK2(sK2(sK1)))),u1_struct_0(sK2(sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_330])])).

fof(f2291,plain,
    ( ~ r2_hidden(u1_struct_0(sK2(sK2(sK1))),k1_waybel_2(sK2(sK2(sK1)),sK2(sK2(sK2(sK1)))))
    | ~ spl11_330 ),
    inference(resolution,[],[f2281,f135])).

fof(f2281,plain,
    ( r2_hidden(k1_waybel_2(sK2(sK2(sK1)),sK2(sK2(sK2(sK1)))),u1_struct_0(sK2(sK2(sK1))))
    | ~ spl11_330 ),
    inference(avatar_component_clause,[],[f2280])).

fof(f2308,plain,
    ( spl11_336
    | ~ spl11_330 ),
    inference(avatar_split_clause,[],[f2290,f2280,f2306])).

fof(f2306,plain,
    ( spl11_336
  <=> m1_subset_1(k1_waybel_2(sK2(sK2(sK1)),sK2(sK2(sK2(sK1)))),u1_struct_0(sK2(sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_336])])).

fof(f2290,plain,
    ( m1_subset_1(k1_waybel_2(sK2(sK2(sK1)),sK2(sK2(sK2(sK1)))),u1_struct_0(sK2(sK2(sK1))))
    | ~ spl11_330 ),
    inference(resolution,[],[f2281,f136])).

fof(f2301,plain,
    ( ~ spl11_335
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_330 ),
    inference(avatar_split_clause,[],[f2293,f2280,f288,f278,f2299])).

fof(f2299,plain,
    ( spl11_335
  <=> ~ m1_subset_1(u1_struct_0(sK2(sK2(sK1))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_335])])).

fof(f2293,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2(sK2(sK1))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_330 ),
    inference(forward_demodulation,[],[f2289,f289])).

fof(f2289,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2(sK2(sK1))),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_330 ),
    inference(resolution,[],[f2281,f281])).

fof(f2294,plain,
    ( ~ spl11_333
    | ~ spl11_330 ),
    inference(avatar_split_clause,[],[f2292,f2280,f2283])).

fof(f2283,plain,
    ( spl11_333
  <=> ~ v1_xboole_0(u1_struct_0(sK2(sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_333])])).

fof(f2292,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2(sK2(sK1))))
    | ~ spl11_330 ),
    inference(resolution,[],[f2281,f143])).

fof(f2288,plain,
    ( spl11_328
    | spl11_330
    | spl11_332
    | ~ spl11_242 ),
    inference(avatar_split_clause,[],[f1384,f1369,f2286,f2280,f2274])).

fof(f2274,plain,
    ( spl11_328
  <=> v2_struct_0(sK2(sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_328])])).

fof(f2286,plain,
    ( spl11_332
  <=> v1_xboole_0(u1_struct_0(sK2(sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_332])])).

fof(f1369,plain,
    ( spl11_242
  <=> l1_struct_0(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_242])])).

fof(f1384,plain,
    ( v1_xboole_0(u1_struct_0(sK2(sK2(sK1))))
    | r2_hidden(k1_waybel_2(sK2(sK2(sK1)),sK2(sK2(sK2(sK1)))),u1_struct_0(sK2(sK2(sK1))))
    | v2_struct_0(sK2(sK2(sK1)))
    | ~ spl11_242 ),
    inference(resolution,[],[f1370,f574])).

fof(f1370,plain,
    ( l1_struct_0(sK2(sK1))
    | ~ spl11_242 ),
    inference(avatar_component_clause,[],[f1369])).

fof(f2269,plain,
    ( ~ spl11_327
    | ~ spl11_320 ),
    inference(avatar_split_clause,[],[f2252,f2241,f2267])).

fof(f2267,plain,
    ( spl11_327
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)),u1_waybel_0(sK4(sK1),sK2(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_327])])).

fof(f2241,plain,
    ( spl11_320
  <=> r2_hidden(u1_waybel_0(sK4(sK1),sK2(sK4(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_320])])).

fof(f2252,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)),u1_waybel_0(sK4(sK1),sK2(sK4(sK1))))
    | ~ spl11_320 ),
    inference(resolution,[],[f2242,f135])).

fof(f2242,plain,
    ( r2_hidden(u1_waybel_0(sK4(sK1),sK2(sK4(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)))
    | ~ spl11_320 ),
    inference(avatar_component_clause,[],[f2241])).

fof(f2262,plain,
    ( ~ spl11_325
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_320 ),
    inference(avatar_split_clause,[],[f2254,f2241,f288,f278,f2260])).

fof(f2260,plain,
    ( spl11_325
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_325])])).

fof(f2254,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_320 ),
    inference(forward_demodulation,[],[f2250,f289])).

fof(f2250,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_320 ),
    inference(resolution,[],[f2242,f281])).

fof(f2255,plain,
    ( ~ spl11_323
    | ~ spl11_320 ),
    inference(avatar_split_clause,[],[f2253,f2241,f2244])).

fof(f2244,plain,
    ( spl11_323
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_323])])).

fof(f2253,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)))
    | ~ spl11_320 ),
    inference(resolution,[],[f2242,f143])).

fof(f2249,plain,
    ( spl11_320
    | spl11_322
    | ~ spl11_230 ),
    inference(avatar_split_clause,[],[f1323,f1315,f2247,f2241])).

fof(f2247,plain,
    ( spl11_322
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_322])])).

fof(f1315,plain,
    ( spl11_230
  <=> m1_subset_1(u1_waybel_0(sK4(sK1),sK2(sK4(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_230])])).

fof(f1323,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)))
    | r2_hidden(u1_waybel_0(sK4(sK1),sK2(sK4(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)))
    | ~ spl11_230 ),
    inference(resolution,[],[f1316,f137])).

fof(f1316,plain,
    ( m1_subset_1(u1_waybel_0(sK4(sK1),sK2(sK4(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)))
    | ~ spl11_230 ),
    inference(avatar_component_clause,[],[f1315])).

fof(f2236,plain,
    ( spl11_314
    | spl11_316
    | spl11_318
    | ~ spl11_192 ),
    inference(avatar_split_clause,[],[f1129,f1126,f2234,f2228,f2222])).

fof(f2222,plain,
    ( spl11_314
  <=> v1_xboole_0(u1_struct_0(sK2(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_314])])).

fof(f2228,plain,
    ( spl11_316
  <=> v2_struct_0(sK2(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_316])])).

fof(f2234,plain,
    ( spl11_318
  <=> r2_hidden(k1_waybel_2(sK2(sK4(sK1)),sK2(sK2(sK4(sK1)))),u1_struct_0(sK2(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_318])])).

fof(f1126,plain,
    ( spl11_192
  <=> l1_orders_2(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_192])])).

fof(f1129,plain,
    ( r2_hidden(k1_waybel_2(sK2(sK4(sK1)),sK2(sK2(sK4(sK1)))),u1_struct_0(sK2(sK4(sK1))))
    | v2_struct_0(sK2(sK4(sK1)))
    | v1_xboole_0(u1_struct_0(sK2(sK4(sK1))))
    | ~ spl11_192 ),
    inference(resolution,[],[f1127,f750])).

fof(f1127,plain,
    ( l1_orders_2(sK4(sK1))
    | ~ spl11_192 ),
    inference(avatar_component_clause,[],[f1126])).

fof(f2189,plain,
    ( ~ spl11_313
    | ~ spl11_306 ),
    inference(avatar_split_clause,[],[f2171,f2160,f2187])).

fof(f2187,plain,
    ( spl11_313
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0),sK6(u1_waybel_0(sK2(sK1),sK2(sK2(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_313])])).

fof(f2160,plain,
    ( spl11_306
  <=> r2_hidden(sK6(u1_waybel_0(sK2(sK1),sK2(sK2(sK1)))),k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_306])])).

fof(f2171,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0),sK6(u1_waybel_0(sK2(sK1),sK2(sK2(sK1)))))
    | ~ spl11_306 ),
    inference(resolution,[],[f2161,f135])).

fof(f2161,plain,
    ( r2_hidden(sK6(u1_waybel_0(sK2(sK1),sK2(sK2(sK1)))),k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0))
    | ~ spl11_306 ),
    inference(avatar_component_clause,[],[f2160])).

fof(f2182,plain,
    ( ~ spl11_311
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_306 ),
    inference(avatar_split_clause,[],[f2173,f2160,f288,f278,f2180])).

fof(f2180,plain,
    ( spl11_311
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_311])])).

fof(f2173,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_306 ),
    inference(forward_demodulation,[],[f2169,f289])).

fof(f2169,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_306 ),
    inference(resolution,[],[f2161,f281])).

fof(f2174,plain,
    ( ~ spl11_309
    | ~ spl11_306 ),
    inference(avatar_split_clause,[],[f2172,f2160,f2163])).

fof(f2163,plain,
    ( spl11_309
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_309])])).

fof(f2172,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0))
    | ~ spl11_306 ),
    inference(resolution,[],[f2161,f143])).

fof(f2168,plain,
    ( spl11_306
    | spl11_308
    | ~ spl11_300 ),
    inference(avatar_split_clause,[],[f2151,f2126,f2166,f2160])).

fof(f2166,plain,
    ( spl11_308
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_308])])).

fof(f2126,plain,
    ( spl11_300
  <=> m1_subset_1(sK6(u1_waybel_0(sK2(sK1),sK2(sK2(sK1)))),k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_300])])).

fof(f2151,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0))
    | r2_hidden(sK6(u1_waybel_0(sK2(sK1),sK2(sK2(sK1)))),k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0))
    | ~ spl11_300 ),
    inference(resolution,[],[f2127,f137])).

fof(f2127,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK2(sK1),sK2(sK2(sK1)))),k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0))
    | ~ spl11_300 ),
    inference(avatar_component_clause,[],[f2126])).

fof(f2155,plain,
    ( spl11_268
    | spl11_304
    | ~ spl11_246 ),
    inference(avatar_split_clause,[],[f1404,f1391,f2153,f1480])).

fof(f1480,plain,
    ( spl11_268
  <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_268])])).

fof(f2153,plain,
    ( spl11_304
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | r2_hidden(sK6(k4_waybel_1(sK2(sK1),X0)),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
        | v1_xboole_0(k4_waybel_1(sK2(sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_304])])).

fof(f1391,plain,
    ( spl11_246
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_xboole_0)
        | m1_subset_1(k4_waybel_1(sK2(sK1),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_246])])).

fof(f1404,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | v1_xboole_0(k4_waybel_1(sK2(sK1),X0))
        | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
        | r2_hidden(sK6(k4_waybel_1(sK2(sK1),X0)),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) )
    | ~ spl11_246 ),
    inference(resolution,[],[f1402,f137])).

fof(f1402,plain,
    ( ! [X0] :
        ( m1_subset_1(sK6(k4_waybel_1(sK2(sK1),X0)),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
        | ~ m1_subset_1(X0,k1_xboole_0)
        | v1_xboole_0(k4_waybel_1(sK2(sK1),X0)) )
    | ~ spl11_246 ),
    inference(resolution,[],[f1394,f267])).

fof(f1394,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k4_waybel_1(sK2(sK1),X0))
        | m1_subset_1(X1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
        | ~ m1_subset_1(X0,k1_xboole_0) )
    | ~ spl11_246 ),
    inference(resolution,[],[f1392,f144])).

fof(f1392,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_waybel_1(sK2(sK1),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ m1_subset_1(X2,k1_xboole_0) )
    | ~ spl11_246 ),
    inference(avatar_component_clause,[],[f1391])).

fof(f2150,plain,
    ( spl11_302
    | ~ spl11_298 ),
    inference(avatar_split_clause,[],[f2129,f2120,f2148])).

fof(f2148,plain,
    ( spl11_302
  <=> u1_waybel_0(sK2(sK1),sK2(sK2(sK1))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_302])])).

fof(f2120,plain,
    ( spl11_298
  <=> v1_xboole_0(u1_waybel_0(sK2(sK1),sK2(sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_298])])).

fof(f2129,plain,
    ( u1_waybel_0(sK2(sK1),sK2(sK2(sK1))) = k1_xboole_0
    | ~ spl11_298 ),
    inference(resolution,[],[f2121,f117])).

fof(f2121,plain,
    ( v1_xboole_0(u1_waybel_0(sK2(sK1),sK2(sK2(sK1))))
    | ~ spl11_298 ),
    inference(avatar_component_clause,[],[f2120])).

fof(f2128,plain,
    ( spl11_298
    | spl11_300
    | ~ spl11_244 ),
    inference(avatar_split_clause,[],[f1387,f1378,f2126,f2120])).

fof(f1387,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK2(sK1),sK2(sK2(sK1)))),k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0))
    | v1_xboole_0(u1_waybel_0(sK2(sK1),sK2(sK2(sK1))))
    | ~ spl11_244 ),
    inference(resolution,[],[f1385,f267])).

fof(f1385,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK2(sK1),sK2(sK2(sK1))))
        | m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)) )
    | ~ spl11_244 ),
    inference(resolution,[],[f1379,f144])).

fof(f2115,plain,
    ( ~ spl11_297
    | ~ spl11_290 ),
    inference(avatar_split_clause,[],[f2098,f2087,f2113])).

fof(f2113,plain,
    ( spl11_297
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0),sK6(u1_waybel_0(sK4(sK1),sK2(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_297])])).

fof(f2087,plain,
    ( spl11_290
  <=> r2_hidden(sK6(u1_waybel_0(sK4(sK1),sK2(sK4(sK1)))),k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_290])])).

fof(f2098,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0),sK6(u1_waybel_0(sK4(sK1),sK2(sK4(sK1)))))
    | ~ spl11_290 ),
    inference(resolution,[],[f2088,f135])).

fof(f2088,plain,
    ( r2_hidden(sK6(u1_waybel_0(sK4(sK1),sK2(sK4(sK1)))),k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0))
    | ~ spl11_290 ),
    inference(avatar_component_clause,[],[f2087])).

fof(f2108,plain,
    ( ~ spl11_295
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_290 ),
    inference(avatar_split_clause,[],[f2100,f2087,f288,f278,f2106])).

fof(f2106,plain,
    ( spl11_295
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_295])])).

fof(f2100,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_290 ),
    inference(forward_demodulation,[],[f2096,f289])).

fof(f2096,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_290 ),
    inference(resolution,[],[f2088,f281])).

fof(f2101,plain,
    ( ~ spl11_293
    | ~ spl11_290 ),
    inference(avatar_split_clause,[],[f2099,f2087,f2090])).

fof(f2090,plain,
    ( spl11_293
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_293])])).

fof(f2099,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0))
    | ~ spl11_290 ),
    inference(resolution,[],[f2088,f143])).

fof(f2095,plain,
    ( spl11_290
    | spl11_292
    | ~ spl11_264 ),
    inference(avatar_split_clause,[],[f1475,f1458,f2093,f2087])).

fof(f2093,plain,
    ( spl11_292
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_292])])).

fof(f1458,plain,
    ( spl11_264
  <=> m1_subset_1(sK6(u1_waybel_0(sK4(sK1),sK2(sK4(sK1)))),k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_264])])).

fof(f1475,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0))
    | r2_hidden(sK6(u1_waybel_0(sK4(sK1),sK2(sK4(sK1)))),k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0))
    | ~ spl11_264 ),
    inference(resolution,[],[f1459,f137])).

fof(f1459,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK4(sK1),sK2(sK4(sK1)))),k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0))
    | ~ spl11_264 ),
    inference(avatar_component_clause,[],[f1458])).

fof(f1916,plain,
    ( ~ spl11_229
    | spl11_288
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_214
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(avatar_split_clause,[],[f1852,f1497,f1391,f1238,f288,f278,f1914,f1309])).

fof(f1309,plain,
    ( spl11_229
  <=> ~ l1_struct_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_229])])).

fof(f1914,plain,
    ( spl11_288
  <=> k4_waybel_1(sK2(sK1),k1_waybel_2(sK4(sK1),sK2(sK4(sK1)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_288])])).

fof(f1238,plain,
    ( spl11_214
  <=> ! [X3] :
        ( m1_subset_1(k1_waybel_2(sK4(sK1),X3),k1_xboole_0)
        | ~ l1_waybel_0(X3,sK4(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_214])])).

fof(f1852,plain,
    ( k4_waybel_1(sK2(sK1),k1_waybel_2(sK4(sK1),sK2(sK4(sK1)))) = k1_xboole_0
    | ~ l1_struct_0(sK4(sK1))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_214
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(resolution,[],[f1608,f119])).

fof(f1608,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(X1,sK4(sK1))
        | k4_waybel_1(sK2(sK1),k1_waybel_2(sK4(sK1),X1)) = k1_xboole_0 )
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_214
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(resolution,[],[f1535,f1239])).

fof(f1239,plain,
    ( ! [X3] :
        ( m1_subset_1(k1_waybel_2(sK4(sK1),X3),k1_xboole_0)
        | ~ l1_waybel_0(X3,sK4(sK1)) )
    | ~ spl11_214 ),
    inference(avatar_component_clause,[],[f1238])).

fof(f1535,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | k4_waybel_1(sK2(sK1),X0) = k1_xboole_0 )
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(forward_demodulation,[],[f1531,f289])).

fof(f1531,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | k4_waybel_1(sK2(sK1),X0) = sK6(k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(resolution,[],[f1520,f282])).

fof(f282,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK6(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl11_32 ),
    inference(resolution,[],[f279,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t8_boole)).

fof(f1520,plain,
    ( ! [X0] :
        ( v1_xboole_0(k4_waybel_1(sK2(sK1),X0))
        | ~ m1_subset_1(X0,k1_xboole_0) )
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(resolution,[],[f1506,f335])).

fof(f335,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(forward_demodulation,[],[f333,f289])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
        | v1_xboole_0(X0) )
    | ~ spl11_32 ),
    inference(resolution,[],[f281,f267])).

fof(f1506,plain,
    ( ! [X4] :
        ( m1_subset_1(k4_waybel_1(sK2(sK1),X4),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X4,k1_xboole_0) )
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(superposition,[],[f1392,f1498])).

fof(f1888,plain,
    ( ~ spl11_229
    | spl11_286
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_214
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(avatar_split_clause,[],[f1822,f1497,f1243,f1238,f288,f278,f1886,f1309])).

fof(f1886,plain,
    ( spl11_286
  <=> k4_waybel_1(sK4(sK1),k1_waybel_2(sK4(sK1),sK2(sK4(sK1)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_286])])).

fof(f1243,plain,
    ( spl11_216
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_xboole_0)
        | m1_subset_1(k4_waybel_1(sK4(sK1),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_216])])).

fof(f1822,plain,
    ( k4_waybel_1(sK4(sK1),k1_waybel_2(sK4(sK1),sK2(sK4(sK1)))) = k1_xboole_0
    | ~ l1_struct_0(sK4(sK1))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_214
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(resolution,[],[f1544,f119])).

fof(f1544,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(X1,sK4(sK1))
        | k4_waybel_1(sK4(sK1),k1_waybel_2(sK4(sK1),X1)) = k1_xboole_0 )
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_214
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(resolution,[],[f1528,f1239])).

fof(f1528,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | k4_waybel_1(sK4(sK1),X0) = k1_xboole_0 )
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(forward_demodulation,[],[f1524,f289])).

fof(f1524,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | k4_waybel_1(sK4(sK1),X0) = sK6(k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(resolution,[],[f1511,f282])).

fof(f1511,plain,
    ( ! [X0] :
        ( v1_xboole_0(k4_waybel_1(sK4(sK1),X0))
        | ~ m1_subset_1(X0,k1_xboole_0) )
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(resolution,[],[f1500,f335])).

fof(f1500,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_waybel_1(sK4(sK1),X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_xboole_0) )
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(superposition,[],[f1244,f1498])).

fof(f1244,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_waybel_1(sK4(sK1),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ m1_subset_1(X2,k1_xboole_0) )
    | ~ spl11_216 ),
    inference(avatar_component_clause,[],[f1243])).

fof(f1831,plain,
    ( spl11_284
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_172
    | ~ spl11_242
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(avatar_split_clause,[],[f1824,f1497,f1391,f1369,f1015,f288,f278,f1829])).

fof(f1829,plain,
    ( spl11_284
  <=> k4_waybel_1(sK2(sK1),k1_waybel_2(sK2(sK1),sK2(sK2(sK1)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_284])])).

fof(f1015,plain,
    ( spl11_172
  <=> ! [X3] :
        ( m1_subset_1(k1_waybel_2(sK2(sK1),X3),k1_xboole_0)
        | ~ l1_waybel_0(X3,sK2(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_172])])).

fof(f1824,plain,
    ( k4_waybel_1(sK2(sK1),k1_waybel_2(sK2(sK1),sK2(sK2(sK1)))) = k1_xboole_0
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_172
    | ~ spl11_242
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(subsumption_resolution,[],[f1823,f1370])).

fof(f1823,plain,
    ( k4_waybel_1(sK2(sK1),k1_waybel_2(sK2(sK1),sK2(sK2(sK1)))) = k1_xboole_0
    | ~ l1_struct_0(sK2(sK1))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_172
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(resolution,[],[f1607,f119])).

fof(f1607,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK2(sK1))
        | k4_waybel_1(sK2(sK1),k1_waybel_2(sK2(sK1),X0)) = k1_xboole_0 )
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_172
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(resolution,[],[f1535,f1016])).

fof(f1016,plain,
    ( ! [X3] :
        ( m1_subset_1(k1_waybel_2(sK2(sK1),X3),k1_xboole_0)
        | ~ l1_waybel_0(X3,sK2(sK1)) )
    | ~ spl11_172 ),
    inference(avatar_component_clause,[],[f1015])).

fof(f1800,plain,
    ( spl11_282
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_172
    | ~ spl11_216
    | ~ spl11_242
    | ~ spl11_272 ),
    inference(avatar_split_clause,[],[f1792,f1497,f1369,f1243,f1015,f288,f278,f1798])).

fof(f1798,plain,
    ( spl11_282
  <=> k4_waybel_1(sK4(sK1),k1_waybel_2(sK2(sK1),sK2(sK2(sK1)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_282])])).

fof(f1792,plain,
    ( k4_waybel_1(sK4(sK1),k1_waybel_2(sK2(sK1),sK2(sK2(sK1)))) = k1_xboole_0
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_172
    | ~ spl11_216
    | ~ spl11_242
    | ~ spl11_272 ),
    inference(subsumption_resolution,[],[f1791,f1370])).

fof(f1791,plain,
    ( k4_waybel_1(sK4(sK1),k1_waybel_2(sK2(sK1),sK2(sK2(sK1)))) = k1_xboole_0
    | ~ l1_struct_0(sK2(sK1))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_172
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(resolution,[],[f1543,f119])).

fof(f1543,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK2(sK1))
        | k4_waybel_1(sK4(sK1),k1_waybel_2(sK2(sK1),X0)) = k1_xboole_0 )
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_172
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(resolution,[],[f1528,f1016])).

fof(f1648,plain,
    ( spl11_280
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(avatar_split_clause,[],[f1610,f1497,f1391,f288,f278,f1646])).

fof(f1646,plain,
    ( spl11_280
  <=> k4_waybel_1(sK2(sK1),sK6(k1_xboole_0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_280])])).

fof(f1610,plain,
    ( k4_waybel_1(sK2(sK1),sK6(k1_xboole_0)) = k1_xboole_0
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(resolution,[],[f1535,f134])).

fof(f1623,plain,
    ( spl11_278
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_68
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(avatar_split_clause,[],[f1609,f1497,f1391,f515,f288,f278,f1621])).

fof(f1621,plain,
    ( spl11_278
  <=> k4_waybel_1(sK2(sK1),k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_278])])).

fof(f515,plain,
    ( spl11_68
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f1609,plain,
    ( k4_waybel_1(sK2(sK1),k1_xboole_0) = k1_xboole_0
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_68
    | ~ spl11_246
    | ~ spl11_272 ),
    inference(resolution,[],[f1535,f516])).

fof(f516,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl11_68 ),
    inference(avatar_component_clause,[],[f515])).

fof(f1587,plain,
    ( spl11_276
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(avatar_split_clause,[],[f1546,f1497,f1243,f288,f278,f1585])).

fof(f1585,plain,
    ( spl11_276
  <=> k4_waybel_1(sK4(sK1),sK6(k1_xboole_0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_276])])).

fof(f1546,plain,
    ( k4_waybel_1(sK4(sK1),sK6(k1_xboole_0)) = k1_xboole_0
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(resolution,[],[f1528,f134])).

fof(f1561,plain,
    ( spl11_274
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_68
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(avatar_split_clause,[],[f1545,f1497,f1243,f515,f288,f278,f1559])).

fof(f1559,plain,
    ( spl11_274
  <=> k4_waybel_1(sK4(sK1),k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_274])])).

fof(f1545,plain,
    ( k4_waybel_1(sK4(sK1),k1_xboole_0) = k1_xboole_0
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_68
    | ~ spl11_216
    | ~ spl11_272 ),
    inference(resolution,[],[f1528,f516])).

fof(f1499,plain,
    ( spl11_272
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_268 ),
    inference(avatar_split_clause,[],[f1490,f1480,f288,f278,f1497])).

fof(f1490,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_268 ),
    inference(forward_demodulation,[],[f1486,f289])).

fof(f1486,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_268 ),
    inference(resolution,[],[f1481,f282])).

fof(f1481,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl11_268 ),
    inference(avatar_component_clause,[],[f1480])).

fof(f1485,plain,
    ( spl11_268
    | spl11_270
    | ~ spl11_216 ),
    inference(avatar_split_clause,[],[f1389,f1243,f1483,f1480])).

fof(f1483,plain,
    ( spl11_270
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | r2_hidden(sK6(k4_waybel_1(sK4(sK1),X0)),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
        | v1_xboole_0(k4_waybel_1(sK4(sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_270])])).

fof(f1389,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | v1_xboole_0(k4_waybel_1(sK4(sK1),X0))
        | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
        | r2_hidden(sK6(k4_waybel_1(sK4(sK1),X0)),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) )
    | ~ spl11_216 ),
    inference(resolution,[],[f1248,f137])).

fof(f1248,plain,
    ( ! [X0] :
        ( m1_subset_1(sK6(k4_waybel_1(sK4(sK1),X0)),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
        | ~ m1_subset_1(X0,k1_xboole_0)
        | v1_xboole_0(k4_waybel_1(sK4(sK1),X0)) )
    | ~ spl11_216 ),
    inference(resolution,[],[f1246,f267])).

fof(f1246,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k4_waybel_1(sK4(sK1),X0))
        | m1_subset_1(X1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
        | ~ m1_subset_1(X0,k1_xboole_0) )
    | ~ spl11_216 ),
    inference(resolution,[],[f1244,f144])).

fof(f1474,plain,
    ( spl11_266
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_262 ),
    inference(avatar_split_clause,[],[f1465,f1452,f288,f278,f1472])).

fof(f1472,plain,
    ( spl11_266
  <=> u1_waybel_0(sK4(sK1),sK2(sK4(sK1))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_266])])).

fof(f1452,plain,
    ( spl11_262
  <=> v1_xboole_0(u1_waybel_0(sK4(sK1),sK2(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_262])])).

fof(f1465,plain,
    ( u1_waybel_0(sK4(sK1),sK2(sK4(sK1))) = k1_xboole_0
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_262 ),
    inference(forward_demodulation,[],[f1461,f289])).

fof(f1461,plain,
    ( u1_waybel_0(sK4(sK1),sK2(sK4(sK1))) = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_262 ),
    inference(resolution,[],[f1453,f282])).

fof(f1453,plain,
    ( v1_xboole_0(u1_waybel_0(sK4(sK1),sK2(sK4(sK1))))
    | ~ spl11_262 ),
    inference(avatar_component_clause,[],[f1452])).

fof(f1460,plain,
    ( spl11_262
    | spl11_264
    | ~ spl11_230 ),
    inference(avatar_split_clause,[],[f1327,f1315,f1458,f1452])).

fof(f1327,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK4(sK1),sK2(sK4(sK1)))),k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0))
    | v1_xboole_0(u1_waybel_0(sK4(sK1),sK2(sK4(sK1))))
    | ~ spl11_230 ),
    inference(resolution,[],[f1322,f267])).

fof(f1322,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK4(sK1),sK2(sK4(sK1))))
        | m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)) )
    | ~ spl11_230 ),
    inference(resolution,[],[f1316,f144])).

fof(f1446,plain,
    ( spl11_258
    | spl11_260
    | ~ spl11_196 ),
    inference(avatar_split_clause,[],[f1148,f1143,f1444,f1441])).

fof(f1441,plain,
    ( spl11_258
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_258])])).

fof(f1444,plain,
    ( spl11_260
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK1,sK4(sK1)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_260])])).

fof(f1148,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_waybel_0(sK1,sK4(sK1)))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))) )
    | ~ spl11_196 ),
    inference(resolution,[],[f1146,f137])).

fof(f1435,plain,
    ( spl11_254
    | spl11_256
    | ~ spl11_196 ),
    inference(avatar_split_clause,[],[f1147,f1143,f1433,f1427])).

fof(f1427,plain,
    ( spl11_254
  <=> r2_hidden(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_254])])).

fof(f1433,plain,
    ( spl11_256
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_256])])).

fof(f1147,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))))
    | r2_hidden(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))))
    | ~ spl11_196 ),
    inference(resolution,[],[f1144,f137])).

fof(f1422,plain,
    ( ~ spl11_243
    | spl11_252
    | ~ spl11_144 ),
    inference(avatar_split_clause,[],[f889,f882,f1420,f1372])).

fof(f1372,plain,
    ( spl11_243
  <=> ~ l1_struct_0(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_243])])).

fof(f1420,plain,
    ( spl11_252
  <=> ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0))
        | ~ r2_hidden(X1,u1_waybel_0(sK2(sK1),sK2(sK2(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_252])])).

fof(f882,plain,
    ( spl11_144
  <=> u1_struct_0(sK2(sK1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_144])])).

fof(f889,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0))
        | ~ l1_struct_0(sK2(sK1))
        | ~ r2_hidden(X1,u1_waybel_0(sK2(sK1),sK2(sK2(sK1)))) )
    | ~ spl11_144 ),
    inference(superposition,[],[f543,f883])).

fof(f883,plain,
    ( u1_struct_0(sK2(sK1)) = k1_xboole_0
    | ~ spl11_144 ),
    inference(avatar_component_clause,[],[f882])).

fof(f1418,plain,
    ( ~ spl11_229
    | spl11_250
    | ~ spl11_206 ),
    inference(avatar_split_clause,[],[f1199,f1186,f1416,f1309])).

fof(f1416,plain,
    ( spl11_250
  <=> ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0))
        | ~ r2_hidden(X1,u1_waybel_0(sK4(sK1),sK2(sK4(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_250])])).

fof(f1199,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0))
        | ~ l1_struct_0(sK4(sK1))
        | ~ r2_hidden(X1,u1_waybel_0(sK4(sK1),sK2(sK4(sK1)))) )
    | ~ spl11_206 ),
    inference(superposition,[],[f543,f1187])).

fof(f1411,plain,
    ( spl11_204
    | spl11_248
    | ~ spl11_192 ),
    inference(avatar_split_clause,[],[f1131,f1126,f1409,f1172])).

fof(f1409,plain,
    ( spl11_248
  <=> k1_waybel_2(sK4(sK1),sK2(sK4(sK1))) = k4_yellow_2(sK4(sK1),u1_waybel_0(sK4(sK1),sK2(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_248])])).

fof(f1131,plain,
    ( k1_waybel_2(sK4(sK1),sK2(sK4(sK1))) = k4_yellow_2(sK4(sK1),u1_waybel_0(sK4(sK1),sK2(sK4(sK1))))
    | v2_struct_0(sK4(sK1))
    | ~ spl11_192 ),
    inference(resolution,[],[f1127,f550])).

fof(f550,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k1_waybel_2(X0,sK2(X0)) = k4_yellow_2(X0,u1_waybel_0(X0,sK2(X0)))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f549,f120])).

fof(f549,plain,(
    ! [X0] :
      ( k1_waybel_2(X0,sK2(X0)) = k4_yellow_2(X0,u1_waybel_0(X0,sK2(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f121,f119])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => k1_waybel_2(X0,X1) = k4_yellow_2(X0,u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',d1_waybel_2)).

fof(f1393,plain,
    ( spl11_142
    | ~ spl11_171
    | spl11_246
    | ~ spl11_144 ),
    inference(avatar_split_clause,[],[f893,f882,f1391,f1012,f868])).

fof(f868,plain,
    ( spl11_142
  <=> v2_struct_0(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_142])])).

fof(f1012,plain,
    ( spl11_171
  <=> ~ l1_orders_2(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_171])])).

fof(f893,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_xboole_0)
        | m1_subset_1(k4_waybel_1(sK2(sK1),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ l1_orders_2(sK2(sK1))
        | v2_struct_0(sK2(sK1)) )
    | ~ spl11_144 ),
    inference(forward_demodulation,[],[f890,f883])).

fof(f890,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_waybel_1(sK2(sK1),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK2(sK1)))
        | ~ l1_orders_2(sK2(sK1))
        | v2_struct_0(sK2(sK1)) )
    | ~ spl11_144 ),
    inference(superposition,[],[f140,f883])).

fof(f1383,plain,
    ( ~ spl11_171
    | spl11_243 ),
    inference(avatar_split_clause,[],[f1381,f1372,f1012])).

fof(f1381,plain,
    ( ~ l1_orders_2(sK2(sK1))
    | ~ spl11_243 ),
    inference(resolution,[],[f1373,f120])).

fof(f1373,plain,
    ( ~ l1_struct_0(sK2(sK1))
    | ~ spl11_243 ),
    inference(avatar_component_clause,[],[f1372])).

fof(f1380,plain,
    ( ~ spl11_243
    | spl11_244
    | ~ spl11_144 ),
    inference(avatar_split_clause,[],[f891,f882,f1378,f1372])).

fof(f891,plain,
    ( m1_subset_1(u1_waybel_0(sK2(sK1),sK2(sK2(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK2(sK1))),k1_xboole_0)))
    | ~ l1_struct_0(sK2(sK1))
    | ~ spl11_144 ),
    inference(superposition,[],[f542,f883])).

fof(f1367,plain,
    ( spl11_238
    | ~ spl11_241
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_234 ),
    inference(avatar_split_clause,[],[f1357,f1336,f288,f278,f1365,f1359])).

fof(f1359,plain,
    ( spl11_238
  <=> ! [X0] : ~ m1_subset_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_238])])).

fof(f1365,plain,
    ( spl11_241
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_241])])).

fof(f1336,plain,
    ( spl11_234
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_xboole_0)
        | r2_hidden(k4_waybel_1(sK4(sK1),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_234])])).

fof(f1357,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_xboole_0) )
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_234 ),
    inference(forward_demodulation,[],[f1353,f289])).

fof(f1353,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl11_32
    | ~ spl11_234 ),
    inference(resolution,[],[f1337,f281])).

fof(f1337,plain,
    ( ! [X2] :
        ( r2_hidden(k4_waybel_1(sK4(sK1),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ m1_subset_1(X2,k1_xboole_0) )
    | ~ spl11_234 ),
    inference(avatar_component_clause,[],[f1336])).

fof(f1352,plain,
    ( spl11_236
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_232 ),
    inference(avatar_split_clause,[],[f1343,f1333,f288,f278,f1350])).

fof(f1350,plain,
    ( spl11_236
  <=> k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_236])])).

fof(f1333,plain,
    ( spl11_232
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_232])])).

fof(f1343,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_232 ),
    inference(forward_demodulation,[],[f1339,f289])).

fof(f1339,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_232 ),
    inference(resolution,[],[f1334,f282])).

fof(f1334,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl11_232 ),
    inference(avatar_component_clause,[],[f1333])).

fof(f1338,plain,
    ( spl11_232
    | spl11_234
    | ~ spl11_216 ),
    inference(avatar_split_clause,[],[f1247,f1243,f1336,f1333])).

fof(f1247,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_xboole_0)
        | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | r2_hidden(k4_waybel_1(sK4(sK1),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) )
    | ~ spl11_216 ),
    inference(resolution,[],[f1244,f137])).

fof(f1321,plain,
    ( ~ spl11_192
    | spl11_229 ),
    inference(avatar_contradiction_clause,[],[f1320])).

fof(f1320,plain,
    ( $false
    | ~ spl11_192
    | ~ spl11_229 ),
    inference(subsumption_resolution,[],[f1318,f1127])).

fof(f1318,plain,
    ( ~ l1_orders_2(sK4(sK1))
    | ~ spl11_229 ),
    inference(resolution,[],[f1310,f120])).

fof(f1310,plain,
    ( ~ l1_struct_0(sK4(sK1))
    | ~ spl11_229 ),
    inference(avatar_component_clause,[],[f1309])).

fof(f1317,plain,
    ( ~ spl11_229
    | spl11_230
    | ~ spl11_206 ),
    inference(avatar_split_clause,[],[f1201,f1186,f1315,f1309])).

fof(f1201,plain,
    ( m1_subset_1(u1_waybel_0(sK4(sK1),sK2(sK4(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2(sK4(sK1))),k1_xboole_0)))
    | ~ l1_struct_0(sK4(sK1))
    | ~ spl11_206 ),
    inference(superposition,[],[f542,f1187])).

fof(f1302,plain,
    ( spl11_226
    | ~ spl11_196
    | ~ spl11_206
    | ~ spl11_222 ),
    inference(avatar_split_clause,[],[f1283,f1274,f1186,f1143,f1300])).

fof(f1300,plain,
    ( spl11_226
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_226])])).

fof(f1274,plain,
    ( spl11_222
  <=> u1_waybel_0(sK1,sK4(sK1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_222])])).

fof(f1283,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_196
    | ~ spl11_206
    | ~ spl11_222 ),
    inference(forward_demodulation,[],[f1277,f1187])).

fof(f1277,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))))
    | ~ spl11_196
    | ~ spl11_222 ),
    inference(superposition,[],[f1144,f1275])).

fof(f1275,plain,
    ( u1_waybel_0(sK1,sK4(sK1)) = k1_xboole_0
    | ~ spl11_222 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f1290,plain,
    ( spl11_224
    | ~ spl11_210
    | ~ spl11_222 ),
    inference(avatar_split_clause,[],[f1280,f1274,f1220,f1288])).

fof(f1288,plain,
    ( spl11_224
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_224])])).

fof(f1220,plain,
    ( spl11_210
  <=> r2_hidden(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_210])])).

fof(f1280,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_210
    | ~ spl11_222 ),
    inference(superposition,[],[f1221,f1275])).

fof(f1221,plain,
    ( r2_hidden(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_210 ),
    inference(avatar_component_clause,[],[f1220])).

fof(f1276,plain,
    ( spl11_222
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_218 ),
    inference(avatar_split_clause,[],[f1267,f1254,f288,f278,f1274])).

fof(f1267,plain,
    ( u1_waybel_0(sK1,sK4(sK1)) = k1_xboole_0
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_218 ),
    inference(forward_demodulation,[],[f1263,f289])).

fof(f1263,plain,
    ( u1_waybel_0(sK1,sK4(sK1)) = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_218 ),
    inference(resolution,[],[f1255,f282])).

fof(f1255,plain,
    ( v1_xboole_0(u1_waybel_0(sK1,sK4(sK1)))
    | ~ spl11_218 ),
    inference(avatar_component_clause,[],[f1254])).

fof(f1262,plain,
    ( spl11_218
    | spl11_220
    | ~ spl11_196
    | ~ spl11_206 ),
    inference(avatar_split_clause,[],[f1235,f1186,f1143,f1260,f1254])).

fof(f1260,plain,
    ( spl11_220
  <=> m1_subset_1(sK6(u1_waybel_0(sK1,sK4(sK1))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_220])])).

fof(f1235,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK1,sK4(sK1))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_waybel_0(sK1,sK4(sK1)))
    | ~ spl11_196
    | ~ spl11_206 ),
    inference(resolution,[],[f1196,f267])).

fof(f1245,plain,
    ( spl11_204
    | spl11_216
    | ~ spl11_192
    | ~ spl11_206 ),
    inference(avatar_split_clause,[],[f1204,f1186,f1126,f1243,f1172])).

fof(f1204,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_xboole_0)
        | m1_subset_1(k4_waybel_1(sK4(sK1),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | v2_struct_0(sK4(sK1)) )
    | ~ spl11_192
    | ~ spl11_206 ),
    inference(forward_demodulation,[],[f1203,f1187])).

fof(f1203,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_waybel_1(sK4(sK1),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK4(sK1)))
        | v2_struct_0(sK4(sK1)) )
    | ~ spl11_192
    | ~ spl11_206 ),
    inference(subsumption_resolution,[],[f1200,f1127])).

fof(f1200,plain,
    ( ! [X2] :
        ( m1_subset_1(k4_waybel_1(sK4(sK1),X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK4(sK1)))
        | ~ l1_orders_2(sK4(sK1))
        | v2_struct_0(sK4(sK1)) )
    | ~ spl11_206 ),
    inference(superposition,[],[f140,f1187])).

fof(f1240,plain,
    ( spl11_204
    | spl11_214
    | ~ spl11_192
    | ~ spl11_206 ),
    inference(avatar_split_clause,[],[f1205,f1186,f1126,f1238,f1172])).

fof(f1205,plain,
    ( ! [X3] :
        ( m1_subset_1(k1_waybel_2(sK4(sK1),X3),k1_xboole_0)
        | ~ l1_waybel_0(X3,sK4(sK1))
        | v2_struct_0(sK4(sK1)) )
    | ~ spl11_192
    | ~ spl11_206 ),
    inference(subsumption_resolution,[],[f1202,f1127])).

fof(f1202,plain,
    ( ! [X3] :
        ( m1_subset_1(k1_waybel_2(sK4(sK1),X3),k1_xboole_0)
        | ~ l1_waybel_0(X3,sK4(sK1))
        | ~ l1_orders_2(sK4(sK1))
        | v2_struct_0(sK4(sK1)) )
    | ~ spl11_206 ),
    inference(superposition,[],[f139,f1187])).

fof(f1234,plain,
    ( ~ spl11_213
    | ~ spl11_210 ),
    inference(avatar_split_clause,[],[f1225,f1220,f1232])).

fof(f1232,plain,
    ( spl11_213
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))),u1_waybel_0(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_213])])).

fof(f1225,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))),u1_waybel_0(sK1,sK4(sK1)))
    | ~ spl11_210 ),
    inference(resolution,[],[f1221,f135])).

fof(f1222,plain,
    ( spl11_210
    | spl11_177
    | ~ spl11_208 ),
    inference(avatar_split_clause,[],[f1215,f1210,f1030,f1220])).

fof(f1030,plain,
    ( spl11_177
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_177])])).

fof(f1210,plain,
    ( spl11_208
  <=> m1_subset_1(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_208])])).

fof(f1215,plain,
    ( r2_hidden(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_177
    | ~ spl11_208 ),
    inference(subsumption_resolution,[],[f1214,f1031])).

fof(f1031,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_177 ),
    inference(avatar_component_clause,[],[f1030])).

fof(f1214,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | r2_hidden(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_208 ),
    inference(resolution,[],[f1211,f137])).

fof(f1211,plain,
    ( m1_subset_1(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_208 ),
    inference(avatar_component_clause,[],[f1210])).

fof(f1212,plain,
    ( spl11_208
    | ~ spl11_196
    | ~ spl11_206 ),
    inference(avatar_split_clause,[],[f1197,f1186,f1143,f1210])).

fof(f1197,plain,
    ( m1_subset_1(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_196
    | ~ spl11_206 ),
    inference(superposition,[],[f1144,f1187])).

fof(f1191,plain,
    ( ~ spl11_182
    | ~ spl11_204 ),
    inference(avatar_contradiction_clause,[],[f1190])).

fof(f1190,plain,
    ( $false
    | ~ spl11_182
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f1189,f1061])).

fof(f1189,plain,
    ( ~ sP0(sK1)
    | ~ spl11_204 ),
    inference(resolution,[],[f1173,f126])).

fof(f1173,plain,
    ( v2_struct_0(sK4(sK1))
    | ~ spl11_204 ),
    inference(avatar_component_clause,[],[f1172])).

fof(f1188,plain,
    ( spl11_206
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_202 ),
    inference(avatar_split_clause,[],[f1179,f1166,f288,f278,f1186])).

fof(f1166,plain,
    ( spl11_202
  <=> v1_xboole_0(u1_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_202])])).

fof(f1179,plain,
    ( u1_struct_0(sK4(sK1)) = k1_xboole_0
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_202 ),
    inference(forward_demodulation,[],[f1175,f289])).

fof(f1175,plain,
    ( u1_struct_0(sK4(sK1)) = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_202 ),
    inference(resolution,[],[f1167,f282])).

fof(f1167,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK1)))
    | ~ spl11_202 ),
    inference(avatar_component_clause,[],[f1166])).

fof(f1174,plain,
    ( spl11_200
    | spl11_202
    | spl11_204
    | ~ spl11_192 ),
    inference(avatar_split_clause,[],[f1130,f1126,f1172,f1166,f1160])).

fof(f1160,plain,
    ( spl11_200
  <=> r2_hidden(k1_waybel_2(sK4(sK1),sK2(sK4(sK1))),u1_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_200])])).

fof(f1130,plain,
    ( v2_struct_0(sK4(sK1))
    | v1_xboole_0(u1_struct_0(sK4(sK1)))
    | r2_hidden(k1_waybel_2(sK4(sK1),sK2(sK4(sK1))),u1_struct_0(sK4(sK1)))
    | ~ spl11_192 ),
    inference(resolution,[],[f1127,f571])).

fof(f1155,plain,
    ( spl11_84
    | ~ spl11_151
    | spl11_198
    | ~ spl11_190 ),
    inference(avatar_split_clause,[],[f1116,f1101,f1153,f913,f607])).

fof(f607,plain,
    ( spl11_84
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_84])])).

fof(f913,plain,
    ( spl11_151
  <=> ~ l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_151])])).

fof(f1153,plain,
    ( spl11_198
  <=> k1_waybel_2(sK1,sK4(sK1)) = k4_yellow_2(sK1,u1_waybel_0(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_198])])).

fof(f1116,plain,
    ( k1_waybel_2(sK1,sK4(sK1)) = k4_yellow_2(sK1,u1_waybel_0(sK1,sK4(sK1)))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_190 ),
    inference(resolution,[],[f1102,f121])).

fof(f1145,plain,
    ( spl11_196
    | ~ spl11_146
    | ~ spl11_190 ),
    inference(avatar_split_clause,[],[f1120,f1101,f895,f1143])).

fof(f895,plain,
    ( spl11_146
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_146])])).

fof(f1120,plain,
    ( m1_subset_1(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))))
    | ~ spl11_146
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1117,f896])).

fof(f896,plain,
    ( l1_struct_0(sK1)
    | ~ spl11_146 ),
    inference(avatar_component_clause,[],[f895])).

fof(f1117,plain,
    ( m1_subset_1(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ spl11_190 ),
    inference(resolution,[],[f1102,f141])).

fof(f1138,plain,
    ( spl11_194
    | spl11_84
    | ~ spl11_151
    | spl11_89
    | ~ spl11_190 ),
    inference(avatar_split_clause,[],[f1119,f1101,f616,f913,f607,f1136])).

fof(f1136,plain,
    ( spl11_194
  <=> r2_hidden(k1_waybel_2(sK1,sK4(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_194])])).

fof(f1119,plain,
    ( ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | r2_hidden(k1_waybel_2(sK1,sK4(sK1)),u1_struct_0(sK1))
    | ~ spl11_89
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1115,f617])).

fof(f1115,plain,
    ( ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(k1_waybel_2(sK1,sK4(sK1)),u1_struct_0(sK1))
    | ~ spl11_190 ),
    inference(resolution,[],[f1102,f347])).

fof(f1128,plain,
    ( spl11_192
    | ~ spl11_146
    | ~ spl11_190 ),
    inference(avatar_split_clause,[],[f1121,f1101,f895,f1126])).

fof(f1121,plain,
    ( l1_orders_2(sK4(sK1))
    | ~ spl11_146
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f1118,f896])).

fof(f1118,plain,
    ( l1_orders_2(sK4(sK1))
    | ~ l1_struct_0(sK1)
    | ~ spl11_190 ),
    inference(resolution,[],[f1102,f118])).

fof(f1103,plain,
    ( spl11_190
    | ~ spl11_182 ),
    inference(avatar_split_clause,[],[f1089,f1060,f1101])).

fof(f1089,plain,
    ( l1_waybel_0(sK4(sK1),sK1)
    | ~ spl11_182 ),
    inference(resolution,[],[f1061,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | l1_waybel_0(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f1096,plain,
    ( spl11_188
    | ~ spl11_182 ),
    inference(avatar_split_clause,[],[f1088,f1060,f1094])).

fof(f1088,plain,
    ( v10_waybel_0(sK4(sK1),sK1)
    | ~ spl11_182 ),
    inference(resolution,[],[f1061,f130])).

fof(f130,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v10_waybel_0(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f1087,plain,
    ( spl11_182
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | spl11_19
    | spl11_187 ),
    inference(avatar_split_clause,[],[f1086,f1074,f218,f211,f197,f190,f183,f176,f169,f162,f155,f1060])).

fof(f218,plain,
    ( spl11_19
  <=> ~ v2_waybel_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f1074,plain,
    ( spl11_187
  <=> ~ m1_subset_1(sK5(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_187])])).

fof(f1086,plain,
    ( sP0(sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_187 ),
    inference(subsumption_resolution,[],[f1085,f156])).

fof(f1085,plain,
    ( sP0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_187 ),
    inference(subsumption_resolution,[],[f1084,f163])).

fof(f1084,plain,
    ( sP0(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_187 ),
    inference(subsumption_resolution,[],[f1083,f170])).

fof(f1083,plain,
    ( sP0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_187 ),
    inference(subsumption_resolution,[],[f1082,f177])).

fof(f1082,plain,
    ( sP0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_187 ),
    inference(subsumption_resolution,[],[f1081,f184])).

fof(f1081,plain,
    ( sP0(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_187 ),
    inference(subsumption_resolution,[],[f1080,f191])).

fof(f1080,plain,
    ( sP0(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_187 ),
    inference(subsumption_resolution,[],[f1079,f198])).

fof(f1079,plain,
    ( sP0(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_16
    | ~ spl11_19
    | ~ spl11_187 ),
    inference(subsumption_resolution,[],[f1078,f212])).

fof(f1078,plain,
    ( sP0(sK1)
    | ~ l1_waybel_9(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_19
    | ~ spl11_187 ),
    inference(subsumption_resolution,[],[f1077,f219])).

fof(f219,plain,
    ( ~ v2_waybel_2(sK1)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f218])).

fof(f1077,plain,
    ( v2_waybel_2(sK1)
    | sP0(sK1)
    | ~ l1_waybel_9(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_187 ),
    inference(resolution,[],[f1075,f132])).

fof(f132,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),u1_struct_0(X0))
      | v2_waybel_2(X0)
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ( ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) )
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f77,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f58,f76])).

fof(f58,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( v2_waybel_2(X0)
      | ? [X1] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      | ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
          & ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( v10_waybel_0(X2,X0)
               => ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
                  & r1_waybel_9(X0,X2) ) ) ) )
       => v2_waybel_2(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
          & ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ( v10_waybel_0(X1,X0)
               => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                  & r1_waybel_9(X0,X1) ) ) ) )
       => v2_waybel_2(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t37_waybel_9)).

fof(f1075,plain,
    ( ~ m1_subset_1(sK5(sK1),u1_struct_0(sK1))
    | ~ spl11_187 ),
    inference(avatar_component_clause,[],[f1074])).

fof(f1076,plain,
    ( ~ spl11_187
    | spl11_185 ),
    inference(avatar_split_clause,[],[f1069,f1066,f1074])).

fof(f1066,plain,
    ( spl11_185
  <=> ~ v5_pre_topc(k4_waybel_1(sK1,sK5(sK1)),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_185])])).

fof(f1069,plain,
    ( ~ m1_subset_1(sK5(sK1),u1_struct_0(sK1))
    | ~ spl11_185 ),
    inference(resolution,[],[f1067,f110])).

fof(f1067,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,sK5(sK1)),sK1,sK1)
    | ~ spl11_185 ),
    inference(avatar_component_clause,[],[f1066])).

fof(f1068,plain,
    ( spl11_182
    | ~ spl11_185
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | spl11_19 ),
    inference(avatar_split_clause,[],[f940,f218,f211,f197,f190,f183,f176,f169,f162,f155,f1066,f1060])).

fof(f940,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,sK5(sK1)),sK1,sK1)
    | sP0(sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f939,f156])).

fof(f939,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,sK5(sK1)),sK1,sK1)
    | sP0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_2
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f938,f163])).

fof(f938,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,sK5(sK1)),sK1,sK1)
    | sP0(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f937,f170])).

fof(f937,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,sK5(sK1)),sK1,sK1)
    | sP0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f936,f177])).

fof(f936,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,sK5(sK1)),sK1,sK1)
    | sP0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f935,f184])).

fof(f935,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,sK5(sK1)),sK1,sK1)
    | sP0(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f934,f191])).

fof(f934,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,sK5(sK1)),sK1,sK1)
    | sP0(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f933,f219])).

fof(f933,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,sK5(sK1)),sK1,sK1)
    | sP0(sK1)
    | v2_waybel_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f932,f212])).

fof(f932,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK1,sK5(sK1)),sK1,sK1)
    | sP0(sK1)
    | ~ l1_waybel_9(sK1)
    | v2_waybel_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v8_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl11_12 ),
    inference(resolution,[],[f133,f198])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK5(X0)),X0,X0)
      | sP0(X0)
      | ~ l1_waybel_9(X0)
      | v2_waybel_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f1055,plain,
    ( ~ spl11_181
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_174 ),
    inference(avatar_split_clause,[],[f1040,f1027,f288,f278,f1053])).

fof(f1053,plain,
    ( spl11_181
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_181])])).

fof(f1027,plain,
    ( spl11_174
  <=> r2_hidden(u1_waybel_0(sK1,sK2(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_174])])).

fof(f1040,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_174 ),
    inference(forward_demodulation,[],[f1036,f289])).

fof(f1036,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_174 ),
    inference(resolution,[],[f1028,f281])).

fof(f1028,plain,
    ( r2_hidden(u1_waybel_0(sK1,sK2(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_174 ),
    inference(avatar_component_clause,[],[f1027])).

fof(f1048,plain,
    ( ~ spl11_179
    | ~ spl11_174 ),
    inference(avatar_split_clause,[],[f1038,f1027,f1046])).

fof(f1046,plain,
    ( spl11_179
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))),u1_waybel_0(sK1,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_179])])).

fof(f1038,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))),u1_waybel_0(sK1,sK2(sK1)))
    | ~ spl11_174 ),
    inference(resolution,[],[f1028,f135])).

fof(f1041,plain,
    ( ~ spl11_177
    | ~ spl11_174 ),
    inference(avatar_split_clause,[],[f1039,f1027,f1030])).

fof(f1039,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_174 ),
    inference(resolution,[],[f1028,f143])).

fof(f1035,plain,
    ( spl11_174
    | spl11_176
    | ~ spl11_148 ),
    inference(avatar_split_clause,[],[f931,f904,f1033,f1027])).

fof(f1033,plain,
    ( spl11_176
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_176])])).

fof(f931,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | r2_hidden(u1_waybel_0(sK1,sK2(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_148 ),
    inference(resolution,[],[f905,f137])).

fof(f1021,plain,
    ( ~ spl11_146
    | spl11_171 ),
    inference(avatar_contradiction_clause,[],[f1020])).

fof(f1020,plain,
    ( $false
    | ~ spl11_146
    | ~ spl11_171 ),
    inference(subsumption_resolution,[],[f1018,f896])).

fof(f1018,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl11_171 ),
    inference(resolution,[],[f1013,f265])).

fof(f1013,plain,
    ( ~ l1_orders_2(sK2(sK1))
    | ~ spl11_171 ),
    inference(avatar_component_clause,[],[f1012])).

fof(f1017,plain,
    ( spl11_142
    | ~ spl11_171
    | spl11_172
    | ~ spl11_144 ),
    inference(avatar_split_clause,[],[f892,f882,f1015,f1012,f868])).

fof(f892,plain,
    ( ! [X3] :
        ( m1_subset_1(k1_waybel_2(sK2(sK1),X3),k1_xboole_0)
        | ~ l1_waybel_0(X3,sK2(sK1))
        | ~ l1_orders_2(sK2(sK1))
        | v2_struct_0(sK2(sK1)) )
    | ~ spl11_144 ),
    inference(superposition,[],[f139,f883])).

fof(f1007,plain,
    ( ~ spl11_169
    | ~ spl11_162 ),
    inference(avatar_split_clause,[],[f990,f979,f1005])).

fof(f1005,plain,
    ( spl11_169
  <=> ~ r2_hidden(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),sK6(u1_waybel_0(sK1,sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_169])])).

fof(f979,plain,
    ( spl11_162
  <=> r2_hidden(sK6(u1_waybel_0(sK1,sK2(sK1))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_162])])).

fof(f990,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),sK6(u1_waybel_0(sK1,sK2(sK1))))
    | ~ spl11_162 ),
    inference(resolution,[],[f980,f135])).

fof(f980,plain,
    ( r2_hidden(sK6(u1_waybel_0(sK1,sK2(sK1))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl11_162 ),
    inference(avatar_component_clause,[],[f979])).

fof(f1000,plain,
    ( ~ spl11_167
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_162 ),
    inference(avatar_split_clause,[],[f992,f979,f288,f278,f998])).

fof(f998,plain,
    ( spl11_167
  <=> ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_167])])).

fof(f992,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_162 ),
    inference(forward_demodulation,[],[f988,f289])).

fof(f988,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_162 ),
    inference(resolution,[],[f980,f281])).

fof(f993,plain,
    ( ~ spl11_165
    | ~ spl11_162 ),
    inference(avatar_split_clause,[],[f991,f979,f982])).

fof(f982,plain,
    ( spl11_165
  <=> ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_165])])).

fof(f991,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl11_162 ),
    inference(resolution,[],[f980,f143])).

fof(f987,plain,
    ( spl11_162
    | spl11_164
    | ~ spl11_158 ),
    inference(avatar_split_clause,[],[f974,f957,f985,f979])).

fof(f985,plain,
    ( spl11_164
  <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_164])])).

fof(f957,plain,
    ( spl11_158
  <=> m1_subset_1(sK6(u1_waybel_0(sK1,sK2(sK1))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_158])])).

fof(f974,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | r2_hidden(sK6(u1_waybel_0(sK1,sK2(sK1))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl11_158 ),
    inference(resolution,[],[f958,f137])).

fof(f958,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK1,sK2(sK1))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl11_158 ),
    inference(avatar_component_clause,[],[f957])).

fof(f973,plain,
    ( spl11_160
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_156 ),
    inference(avatar_split_clause,[],[f964,f951,f288,f278,f971])).

fof(f971,plain,
    ( spl11_160
  <=> u1_waybel_0(sK1,sK2(sK1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_160])])).

fof(f964,plain,
    ( u1_waybel_0(sK1,sK2(sK1)) = k1_xboole_0
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_156 ),
    inference(forward_demodulation,[],[f960,f289])).

fof(f960,plain,
    ( u1_waybel_0(sK1,sK2(sK1)) = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_156 ),
    inference(resolution,[],[f952,f282])).

fof(f952,plain,
    ( v1_xboole_0(u1_waybel_0(sK1,sK2(sK1)))
    | ~ spl11_156 ),
    inference(avatar_component_clause,[],[f951])).

fof(f959,plain,
    ( spl11_156
    | spl11_158
    | ~ spl11_148 ),
    inference(avatar_split_clause,[],[f941,f904,f957,f951])).

fof(f941,plain,
    ( m1_subset_1(sK6(u1_waybel_0(sK1,sK2(sK1))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_waybel_0(sK1,sK2(sK1)))
    | ~ spl11_148 ),
    inference(resolution,[],[f930,f267])).

fof(f946,plain,
    ( ~ spl11_147
    | spl11_154
    | ~ spl11_144 ),
    inference(avatar_split_clause,[],[f886,f882,f944,f898])).

fof(f898,plain,
    ( spl11_147
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_147])])).

fof(f944,plain,
    ( spl11_154
  <=> ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
        | ~ r2_hidden(X0,u1_waybel_0(sK1,sK2(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_154])])).

fof(f886,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
        | ~ l1_struct_0(sK1)
        | ~ r2_hidden(X0,u1_waybel_0(sK1,sK2(sK1))) )
    | ~ spl11_144 ),
    inference(superposition,[],[f543,f883])).

fof(f929,plain,
    ( ~ spl11_16
    | spl11_153 ),
    inference(avatar_contradiction_clause,[],[f928])).

fof(f928,plain,
    ( $false
    | ~ spl11_16
    | ~ spl11_153 ),
    inference(subsumption_resolution,[],[f927,f212])).

fof(f927,plain,
    ( ~ l1_waybel_9(sK1)
    | ~ spl11_153 ),
    inference(resolution,[],[f921,f115])).

fof(f115,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f921,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl11_153 ),
    inference(avatar_component_clause,[],[f920])).

fof(f920,plain,
    ( spl11_153
  <=> ~ l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_153])])).

fof(f925,plain,
    ( ~ spl11_16
    | spl11_151 ),
    inference(avatar_contradiction_clause,[],[f924])).

fof(f924,plain,
    ( $false
    | ~ spl11_16
    | ~ spl11_151 ),
    inference(subsumption_resolution,[],[f923,f212])).

fof(f923,plain,
    ( ~ l1_waybel_9(sK1)
    | ~ spl11_151 ),
    inference(resolution,[],[f914,f116])).

fof(f914,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl11_151 ),
    inference(avatar_component_clause,[],[f913])).

fof(f922,plain,
    ( ~ spl11_153
    | spl11_147 ),
    inference(avatar_split_clause,[],[f908,f898,f920])).

fof(f908,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl11_147 ),
    inference(resolution,[],[f899,f114])).

fof(f899,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl11_147 ),
    inference(avatar_component_clause,[],[f898])).

fof(f915,plain,
    ( ~ spl11_151
    | spl11_147 ),
    inference(avatar_split_clause,[],[f907,f898,f913])).

fof(f907,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl11_147 ),
    inference(resolution,[],[f899,f120])).

fof(f906,plain,
    ( ~ spl11_147
    | spl11_148
    | ~ spl11_144 ),
    inference(avatar_split_clause,[],[f887,f882,f904,f898])).

fof(f887,plain,
    ( m1_subset_1(u1_waybel_0(sK1,sK2(sK1)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ spl11_144 ),
    inference(superposition,[],[f542,f883])).

fof(f884,plain,
    ( spl11_144
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_140 ),
    inference(avatar_split_clause,[],[f875,f862,f288,f278,f882])).

fof(f862,plain,
    ( spl11_140
  <=> v1_xboole_0(u1_struct_0(sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_140])])).

fof(f875,plain,
    ( u1_struct_0(sK2(sK1)) = k1_xboole_0
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_140 ),
    inference(forward_demodulation,[],[f871,f289])).

fof(f871,plain,
    ( u1_struct_0(sK2(sK1)) = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_140 ),
    inference(resolution,[],[f863,f282])).

fof(f863,plain,
    ( v1_xboole_0(u1_struct_0(sK2(sK1)))
    | ~ spl11_140 ),
    inference(avatar_component_clause,[],[f862])).

fof(f870,plain,
    ( spl11_138
    | spl11_140
    | spl11_142
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f850,f211,f868,f862,f856])).

fof(f856,plain,
    ( spl11_138
  <=> r2_hidden(k1_waybel_2(sK2(sK1),sK2(sK2(sK1))),u1_struct_0(sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_138])])).

fof(f850,plain,
    ( v2_struct_0(sK2(sK1))
    | v1_xboole_0(u1_struct_0(sK2(sK1)))
    | r2_hidden(k1_waybel_2(sK2(sK1),sK2(sK2(sK1))),u1_struct_0(sK2(sK1)))
    | ~ spl11_16 ),
    inference(resolution,[],[f808,f212])).

fof(f849,plain,
    ( spl11_132
    | spl11_134
    | spl11_136
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f829,f225,f847,f841,f835])).

fof(f835,plain,
    ( spl11_132
  <=> v1_xboole_0(u1_struct_0(sK2(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_132])])).

fof(f841,plain,
    ( spl11_134
  <=> v2_struct_0(sK2(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_134])])).

fof(f847,plain,
    ( spl11_136
  <=> r2_hidden(k1_waybel_2(sK2(sK7),sK2(sK2(sK7))),u1_struct_0(sK2(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_136])])).

fof(f829,plain,
    ( r2_hidden(k1_waybel_2(sK2(sK7),sK2(sK2(sK7))),u1_struct_0(sK2(sK7)))
    | v2_struct_0(sK2(sK7))
    | v1_xboole_0(u1_struct_0(sK2(sK7)))
    | ~ spl11_20 ),
    inference(resolution,[],[f751,f226])).

fof(f751,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | r2_hidden(k1_waybel_2(sK2(X1),sK2(sK2(X1))),u1_struct_0(sK2(X1)))
      | v2_struct_0(sK2(X1))
      | v1_xboole_0(u1_struct_0(sK2(X1))) ) ),
    inference(resolution,[],[f574,f114])).

fof(f828,plain,
    ( spl11_126
    | spl11_128
    | spl11_130
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f807,f246,f826,f820,f814])).

fof(f814,plain,
    ( spl11_126
  <=> v1_xboole_0(u1_struct_0(sK2(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_126])])).

fof(f820,plain,
    ( spl11_128
  <=> v2_struct_0(sK2(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_128])])).

fof(f826,plain,
    ( spl11_130
  <=> r2_hidden(k1_waybel_2(sK2(sK10),sK2(sK2(sK10))),u1_struct_0(sK2(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_130])])).

fof(f807,plain,
    ( r2_hidden(k1_waybel_2(sK2(sK10),sK2(sK2(sK10))),u1_struct_0(sK2(sK10)))
    | v2_struct_0(sK2(sK10))
    | v1_xboole_0(u1_struct_0(sK2(sK10)))
    | ~ spl11_26 ),
    inference(resolution,[],[f750,f247])).

fof(f798,plain,
    ( ~ spl11_125
    | ~ spl11_116 ),
    inference(avatar_split_clause,[],[f773,f762,f796])).

fof(f796,plain,
    ( spl11_125
  <=> ~ r2_hidden(u1_struct_0(sK2(sK9)),k1_waybel_2(sK2(sK9),sK2(sK2(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_125])])).

fof(f762,plain,
    ( spl11_116
  <=> r2_hidden(k1_waybel_2(sK2(sK9),sK2(sK2(sK9))),u1_struct_0(sK2(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_116])])).

fof(f773,plain,
    ( ~ r2_hidden(u1_struct_0(sK2(sK9)),k1_waybel_2(sK2(sK9),sK2(sK2(sK9))))
    | ~ spl11_116 ),
    inference(resolution,[],[f763,f135])).

fof(f763,plain,
    ( r2_hidden(k1_waybel_2(sK2(sK9),sK2(sK2(sK9))),u1_struct_0(sK2(sK9)))
    | ~ spl11_116 ),
    inference(avatar_component_clause,[],[f762])).

fof(f791,plain,
    ( spl11_122
    | ~ spl11_116 ),
    inference(avatar_split_clause,[],[f772,f762,f789])).

fof(f789,plain,
    ( spl11_122
  <=> m1_subset_1(k1_waybel_2(sK2(sK9),sK2(sK2(sK9))),u1_struct_0(sK2(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_122])])).

fof(f772,plain,
    ( m1_subset_1(k1_waybel_2(sK2(sK9),sK2(sK2(sK9))),u1_struct_0(sK2(sK9)))
    | ~ spl11_116 ),
    inference(resolution,[],[f763,f136])).

fof(f783,plain,
    ( ~ spl11_121
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_116 ),
    inference(avatar_split_clause,[],[f775,f762,f288,f278,f781])).

fof(f781,plain,
    ( spl11_121
  <=> ~ m1_subset_1(u1_struct_0(sK2(sK9)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_121])])).

fof(f775,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2(sK9)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_116 ),
    inference(forward_demodulation,[],[f771,f289])).

fof(f771,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2(sK9)),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_116 ),
    inference(resolution,[],[f763,f281])).

fof(f776,plain,
    ( ~ spl11_119
    | ~ spl11_116 ),
    inference(avatar_split_clause,[],[f774,f762,f765])).

fof(f765,plain,
    ( spl11_119
  <=> ~ v1_xboole_0(u1_struct_0(sK2(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_119])])).

fof(f774,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2(sK9)))
    | ~ spl11_116 ),
    inference(resolution,[],[f763,f143])).

fof(f770,plain,
    ( spl11_114
    | spl11_116
    | spl11_118
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f749,f239,f768,f762,f756])).

fof(f756,plain,
    ( spl11_114
  <=> v2_struct_0(sK2(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_114])])).

fof(f768,plain,
    ( spl11_118
  <=> v1_xboole_0(u1_struct_0(sK2(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_118])])).

fof(f749,plain,
    ( v1_xboole_0(u1_struct_0(sK2(sK9)))
    | r2_hidden(k1_waybel_2(sK2(sK9),sK2(sK2(sK9))),u1_struct_0(sK2(sK9)))
    | v2_struct_0(sK2(sK9))
    | ~ spl11_24 ),
    inference(resolution,[],[f574,f240])).

fof(f736,plain,
    ( ~ spl11_113
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_98 ),
    inference(avatar_split_clause,[],[f673,f660,f288,f278,f734])).

fof(f734,plain,
    ( spl11_113
  <=> ~ m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_113])])).

fof(f660,plain,
    ( spl11_98
  <=> r2_hidden(k1_waybel_2(sK8,sK2(sK8)),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_98])])).

fof(f673,plain,
    ( ~ m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_98 ),
    inference(forward_demodulation,[],[f669,f289])).

fof(f669,plain,
    ( ~ m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_98 ),
    inference(resolution,[],[f661,f281])).

fof(f661,plain,
    ( r2_hidden(k1_waybel_2(sK8,sK2(sK8)),u1_struct_0(sK8))
    | ~ spl11_98 ),
    inference(avatar_component_clause,[],[f660])).

fof(f729,plain,
    ( ~ spl11_111
    | ~ spl11_98 ),
    inference(avatar_split_clause,[],[f671,f660,f727])).

fof(f727,plain,
    ( spl11_111
  <=> ~ r2_hidden(u1_struct_0(sK8),k1_waybel_2(sK8,sK2(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_111])])).

fof(f671,plain,
    ( ~ r2_hidden(u1_struct_0(sK8),k1_waybel_2(sK8,sK2(sK8)))
    | ~ spl11_98 ),
    inference(resolution,[],[f661,f135])).

fof(f717,plain,
    ( ~ spl11_22
    | spl11_107 ),
    inference(avatar_contradiction_clause,[],[f716])).

fof(f716,plain,
    ( $false
    | ~ spl11_22
    | ~ spl11_107 ),
    inference(subsumption_resolution,[],[f715,f233])).

fof(f715,plain,
    ( ~ l1_waybel_9(sK8)
    | ~ spl11_107 ),
    inference(resolution,[],[f710,f116])).

fof(f710,plain,
    ( ~ l1_orders_2(sK8)
    | ~ spl11_107 ),
    inference(avatar_component_clause,[],[f709])).

fof(f714,plain,
    ( spl11_96
    | ~ spl11_107
    | spl11_108
    | ~ spl11_104 ),
    inference(avatar_split_clause,[],[f702,f696,f712,f709,f654])).

fof(f712,plain,
    ( spl11_108
  <=> ! [X1] :
        ( m1_subset_1(k1_waybel_2(sK8,X1),k1_xboole_0)
        | ~ l1_waybel_0(X1,sK8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_108])])).

fof(f696,plain,
    ( spl11_104
  <=> u1_struct_0(sK8) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_104])])).

fof(f702,plain,
    ( ! [X1] :
        ( m1_subset_1(k1_waybel_2(sK8,X1),k1_xboole_0)
        | ~ l1_waybel_0(X1,sK8)
        | ~ l1_orders_2(sK8)
        | v2_struct_0(sK8) )
    | ~ spl11_104 ),
    inference(superposition,[],[f139,f697])).

fof(f697,plain,
    ( u1_struct_0(sK8) = k1_xboole_0
    | ~ spl11_104 ),
    inference(avatar_component_clause,[],[f696])).

fof(f698,plain,
    ( spl11_104
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_100 ),
    inference(avatar_split_clause,[],[f689,f666,f288,f278,f696])).

fof(f666,plain,
    ( spl11_100
  <=> v1_xboole_0(u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_100])])).

fof(f689,plain,
    ( u1_struct_0(sK8) = k1_xboole_0
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_100 ),
    inference(forward_demodulation,[],[f685,f289])).

fof(f685,plain,
    ( u1_struct_0(sK8) = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_100 ),
    inference(resolution,[],[f667,f282])).

fof(f667,plain,
    ( v1_xboole_0(u1_struct_0(sK8))
    | ~ spl11_100 ),
    inference(avatar_component_clause,[],[f666])).

fof(f684,plain,
    ( spl11_102
    | ~ spl11_98 ),
    inference(avatar_split_clause,[],[f670,f660,f682])).

fof(f682,plain,
    ( spl11_102
  <=> m1_subset_1(k1_waybel_2(sK8,sK2(sK8)),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_102])])).

fof(f670,plain,
    ( m1_subset_1(k1_waybel_2(sK8,sK2(sK8)),u1_struct_0(sK8))
    | ~ spl11_98 ),
    inference(resolution,[],[f661,f136])).

fof(f674,plain,
    ( ~ spl11_101
    | ~ spl11_98 ),
    inference(avatar_split_clause,[],[f672,f660,f663])).

fof(f663,plain,
    ( spl11_101
  <=> ~ v1_xboole_0(u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_101])])).

fof(f672,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK8))
    | ~ spl11_98 ),
    inference(resolution,[],[f661,f143])).

fof(f668,plain,
    ( spl11_96
    | spl11_98
    | spl11_100
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f602,f232,f666,f660,f654])).

fof(f602,plain,
    ( v1_xboole_0(u1_struct_0(sK8))
    | r2_hidden(k1_waybel_2(sK8,sK2(sK8)),u1_struct_0(sK8))
    | v2_struct_0(sK8)
    | ~ spl11_22 ),
    inference(resolution,[],[f573,f233])).

fof(f573,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r2_hidden(k1_waybel_2(X0,sK2(X0)),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f571,f116])).

fof(f648,plain,
    ( ~ spl11_95
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_86 ),
    inference(avatar_split_clause,[],[f626,f613,f288,f278,f646])).

fof(f646,plain,
    ( spl11_95
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_95])])).

fof(f613,plain,
    ( spl11_86
  <=> r2_hidden(k1_waybel_2(sK1,sK2(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_86])])).

fof(f626,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_86 ),
    inference(forward_demodulation,[],[f622,f289])).

fof(f622,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_86 ),
    inference(resolution,[],[f614,f281])).

fof(f614,plain,
    ( r2_hidden(k1_waybel_2(sK1,sK2(sK1)),u1_struct_0(sK1))
    | ~ spl11_86 ),
    inference(avatar_component_clause,[],[f613])).

fof(f641,plain,
    ( ~ spl11_93
    | ~ spl11_86 ),
    inference(avatar_split_clause,[],[f624,f613,f639])).

fof(f639,plain,
    ( spl11_93
  <=> ~ r2_hidden(u1_struct_0(sK1),k1_waybel_2(sK1,sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_93])])).

fof(f624,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k1_waybel_2(sK1,sK2(sK1)))
    | ~ spl11_86 ),
    inference(resolution,[],[f614,f135])).

fof(f634,plain,
    ( spl11_90
    | ~ spl11_86 ),
    inference(avatar_split_clause,[],[f623,f613,f632])).

fof(f632,plain,
    ( spl11_90
  <=> m1_subset_1(k1_waybel_2(sK1,sK2(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).

fof(f623,plain,
    ( m1_subset_1(k1_waybel_2(sK1,sK2(sK1)),u1_struct_0(sK1))
    | ~ spl11_86 ),
    inference(resolution,[],[f614,f136])).

fof(f627,plain,
    ( ~ spl11_89
    | ~ spl11_86 ),
    inference(avatar_split_clause,[],[f625,f613,f616])).

fof(f625,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl11_86 ),
    inference(resolution,[],[f614,f143])).

fof(f621,plain,
    ( spl11_84
    | spl11_86
    | spl11_88
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f601,f211,f619,f613,f607])).

fof(f619,plain,
    ( spl11_88
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f601,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(k1_waybel_2(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl11_16 ),
    inference(resolution,[],[f573,f212])).

fof(f600,plain,
    ( spl11_82
    | ~ spl11_78 ),
    inference(avatar_split_clause,[],[f589,f579,f598])).

fof(f598,plain,
    ( spl11_82
  <=> m1_subset_1(k1_waybel_2(sK10,sK2(sK10)),u1_struct_0(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_82])])).

fof(f579,plain,
    ( spl11_78
  <=> r2_hidden(k1_waybel_2(sK10,sK2(sK10)),u1_struct_0(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_78])])).

fof(f589,plain,
    ( m1_subset_1(k1_waybel_2(sK10,sK2(sK10)),u1_struct_0(sK10))
    | ~ spl11_78 ),
    inference(resolution,[],[f580,f136])).

fof(f580,plain,
    ( r2_hidden(k1_waybel_2(sK10,sK2(sK10)),u1_struct_0(sK10))
    | ~ spl11_78 ),
    inference(avatar_component_clause,[],[f579])).

fof(f593,plain,
    ( ~ spl11_81
    | ~ spl11_78 ),
    inference(avatar_split_clause,[],[f591,f579,f582])).

fof(f582,plain,
    ( spl11_81
  <=> ~ v1_xboole_0(u1_struct_0(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_81])])).

fof(f591,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK10))
    | ~ spl11_78 ),
    inference(resolution,[],[f580,f143])).

fof(f587,plain,
    ( spl11_78
    | spl11_80
    | spl11_74
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f572,f246,f558,f585,f579])).

fof(f585,plain,
    ( spl11_80
  <=> v1_xboole_0(u1_struct_0(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_80])])).

fof(f558,plain,
    ( spl11_74
  <=> v2_struct_0(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).

fof(f572,plain,
    ( v2_struct_0(sK10)
    | v1_xboole_0(u1_struct_0(sK10))
    | r2_hidden(k1_waybel_2(sK10,sK2(sK10)),u1_struct_0(sK10))
    | ~ spl11_26 ),
    inference(resolution,[],[f571,f247])).

fof(f566,plain,
    ( spl11_74
    | spl11_76
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f551,f246,f564,f558])).

fof(f564,plain,
    ( spl11_76
  <=> k1_waybel_2(sK10,sK2(sK10)) = k4_yellow_2(sK10,u1_waybel_0(sK10,sK2(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_76])])).

fof(f551,plain,
    ( k1_waybel_2(sK10,sK2(sK10)) = k4_yellow_2(sK10,u1_waybel_0(sK10,sK2(sK10)))
    | v2_struct_0(sK10)
    | ~ spl11_26 ),
    inference(resolution,[],[f550,f247])).

fof(f540,plain,
    ( spl11_46
    | spl11_50
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f338,f288,f278,f388,f365])).

fof(f365,plain,
    ( spl11_46
  <=> v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f388,plain,
    ( spl11_50
  <=> v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f338,plain,
    ( v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_34 ),
    inference(resolution,[],[f335,f327])).

fof(f539,plain,
    ( spl11_66
    | spl11_46
    | ~ spl11_54 ),
    inference(avatar_split_clause,[],[f475,f418,f365,f486])).

fof(f486,plain,
    ( spl11_66
  <=> r2_hidden(k1_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f418,plain,
    ( spl11_54
  <=> m1_subset_1(k1_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f475,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | r2_hidden(k1_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_54 ),
    inference(resolution,[],[f419,f137])).

fof(f419,plain,
    ( m1_subset_1(k1_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_54 ),
    inference(avatar_component_clause,[],[f418])).

fof(f538,plain,
    ( spl11_64
    | spl11_62
    | ~ spl11_58 ),
    inference(avatar_split_clause,[],[f450,f446,f463,f469])).

fof(f469,plain,
    ( spl11_64
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).

fof(f463,plain,
    ( spl11_62
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_62])])).

fof(f446,plain,
    ( spl11_58
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f450,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl11_58 ),
    inference(resolution,[],[f447,f137])).

fof(f447,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl11_58 ),
    inference(avatar_component_clause,[],[f446])).

fof(f537,plain,
    ( ~ spl11_73
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_64 ),
    inference(avatar_split_clause,[],[f530,f469,f288,f278,f535])).

fof(f535,plain,
    ( spl11_73
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_73])])).

fof(f530,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_64 ),
    inference(forward_demodulation,[],[f526,f289])).

fof(f526,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_64 ),
    inference(resolution,[],[f470,f281])).

fof(f470,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl11_64 ),
    inference(avatar_component_clause,[],[f469])).

fof(f525,plain,
    ( spl11_70
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_62 ),
    inference(avatar_split_clause,[],[f494,f463,f288,f278,f523])).

fof(f523,plain,
    ( spl11_70
  <=> k1_xboole_0 = k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f494,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_62 ),
    inference(forward_demodulation,[],[f490,f289])).

fof(f490,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)) = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_62 ),
    inference(resolution,[],[f464,f282])).

fof(f464,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl11_62 ),
    inference(avatar_component_clause,[],[f463])).

fof(f517,plain,
    ( spl11_68
    | ~ spl11_48
    | ~ spl11_54 ),
    inference(avatar_split_clause,[],[f498,f418,f379,f515])).

fof(f379,plain,
    ( spl11_48
  <=> k1_xboole_0 = sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f498,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl11_48
    | ~ spl11_54 ),
    inference(superposition,[],[f419,f380])).

fof(f380,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f379])).

fof(f488,plain,
    ( spl11_66
    | spl11_47
    | ~ spl11_52 ),
    inference(avatar_split_clause,[],[f413,f402,f362,f486])).

fof(f362,plain,
    ( spl11_47
  <=> ~ v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).

fof(f402,plain,
    ( spl11_52
  <=> k1_xboole_0 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f413,plain,
    ( r2_hidden(k1_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_47
    | ~ spl11_52 ),
    inference(subsumption_resolution,[],[f411,f363])).

fof(f363,plain,
    ( ~ v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_47 ),
    inference(avatar_component_clause,[],[f362])).

fof(f411,plain,
    ( r2_hidden(k1_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_52 ),
    inference(superposition,[],[f267,f403])).

fof(f403,plain,
    ( k1_xboole_0 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f402])).

fof(f471,plain,
    ( spl11_62
    | spl11_64
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f428,f379,f469,f463])).

fof(f428,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl11_48 ),
    inference(superposition,[],[f267,f380])).

fof(f458,plain,
    ( ~ spl11_61
    | ~ spl11_48
    | spl11_53 ),
    inference(avatar_split_clause,[],[f451,f399,f379,f456])).

fof(f456,plain,
    ( spl11_61
  <=> k1_xboole_0 != sK6(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f399,plain,
    ( spl11_53
  <=> k1_xboole_0 != sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f451,plain,
    ( k1_xboole_0 != sK6(k1_xboole_0)
    | ~ spl11_48
    | ~ spl11_53 ),
    inference(superposition,[],[f400,f380])).

fof(f400,plain,
    ( k1_xboole_0 != sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_53 ),
    inference(avatar_component_clause,[],[f399])).

fof(f448,plain,
    ( spl11_58
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f429,f379,f446])).

fof(f429,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl11_48 ),
    inference(superposition,[],[f134,f380])).

fof(f441,plain,
    ( ~ spl11_57
    | ~ spl11_48
    | spl11_51 ),
    inference(avatar_split_clause,[],[f422,f385,f379,f439])).

fof(f439,plain,
    ( spl11_57
  <=> ~ v1_xboole_0(sK6(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_57])])).

fof(f385,plain,
    ( spl11_51
  <=> ~ v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f422,plain,
    ( ~ v1_xboole_0(sK6(k1_xboole_0))
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(superposition,[],[f386,f380])).

fof(f386,plain,
    ( ~ v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl11_51 ),
    inference(avatar_component_clause,[],[f385])).

fof(f420,plain,
    ( spl11_54
    | ~ spl11_52 ),
    inference(avatar_split_clause,[],[f412,f402,f418])).

fof(f412,plain,
    ( m1_subset_1(k1_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_52 ),
    inference(superposition,[],[f134,f403])).

fof(f404,plain,
    ( spl11_52
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_50 ),
    inference(avatar_split_clause,[],[f395,f388,f288,f278,f402])).

fof(f395,plain,
    ( k1_xboole_0 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_50 ),
    inference(forward_demodulation,[],[f391,f289])).

fof(f391,plain,
    ( sK6(k1_zfmisc_1(k1_xboole_0)) = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_50 ),
    inference(resolution,[],[f389,f282])).

fof(f389,plain,
    ( v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f388])).

fof(f390,plain,
    ( spl11_50
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f382,f359,f388])).

fof(f359,plain,
    ( spl11_44
  <=> ! [X1] : ~ r2_hidden(X1,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f382,plain,
    ( v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl11_44 ),
    inference(resolution,[],[f360,f267])).

fof(f360,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl11_44 ),
    inference(avatar_component_clause,[],[f359])).

fof(f381,plain,
    ( spl11_48
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f372,f365,f288,f278,f379])).

fof(f372,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_46 ),
    inference(forward_demodulation,[],[f368,f289])).

fof(f368,plain,
    ( sK6(k1_zfmisc_1(k1_xboole_0)) = sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl11_32
    | ~ spl11_46 ),
    inference(resolution,[],[f366,f282])).

fof(f366,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f365])).

fof(f367,plain,
    ( spl11_44
    | spl11_46
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f330,f253,f365,f359])).

fof(f253,plain,
    ( spl11_28
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f330,plain,
    ( ! [X1] :
        ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
        | ~ r2_hidden(X1,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) )
    | ~ spl11_28 ),
    inference(resolution,[],[f327,f271])).

fof(f271,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl11_28 ),
    inference(resolution,[],[f145,f254])).

fof(f254,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f253])).

fof(f346,plain,
    ( ~ spl11_43
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f336,f318,f288,f278,f344])).

fof(f344,plain,
    ( spl11_43
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).

fof(f318,plain,
    ( spl11_40
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f336,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32
    | ~ spl11_34
    | ~ spl11_40 ),
    inference(forward_demodulation,[],[f334,f289])).

fof(f334,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl11_32
    | ~ spl11_40 ),
    inference(resolution,[],[f281,f319])).

fof(f319,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_40 ),
    inference(avatar_component_clause,[],[f318])).

fof(f324,plain,
    ( ~ spl11_39
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f323,f318,f309])).

fof(f309,plain,
    ( spl11_39
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).

fof(f323,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_40 ),
    inference(resolution,[],[f319,f143])).

fof(f320,plain,
    ( spl11_38
    | spl11_40
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f294,f288,f318,f312])).

fof(f312,plain,
    ( spl11_38
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f294,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_34 ),
    inference(superposition,[],[f267,f289])).

fof(f303,plain,
    ( spl11_36
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f295,f288,f301])).

fof(f301,plain,
    ( spl11_36
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f295,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_34 ),
    inference(superposition,[],[f134,f289])).

fof(f290,plain,
    ( spl11_34
    | ~ spl11_32 ),
    inference(avatar_split_clause,[],[f283,f278,f288])).

fof(f283,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_32 ),
    inference(resolution,[],[f279,f117])).

fof(f280,plain,
    ( spl11_32
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f273,f253,f278])).

fof(f273,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl11_28 ),
    inference(resolution,[],[f272,f267])).

fof(f272,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl11_28 ),
    inference(resolution,[],[f271,f134])).

fof(f262,plain,(
    spl11_30 ),
    inference(avatar_split_clause,[],[f113,f260])).

fof(f260,plain,
    ( spl11_30
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f113,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',d2_xboole_0)).

fof(f255,plain,(
    spl11_28 ),
    inference(avatar_split_clause,[],[f150,f253])).

fof(f150,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f112,f113])).

fof(f112,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',dt_o_0_0_xboole_0)).

fof(f248,plain,(
    spl11_26 ),
    inference(avatar_split_clause,[],[f149,f246])).

fof(f149,plain,(
    l1_orders_2(sK10) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    l1_orders_2(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f22,f99])).

fof(f99,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK10) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',existence_l1_orders_2)).

fof(f241,plain,(
    spl11_24 ),
    inference(avatar_split_clause,[],[f148,f239])).

fof(f148,plain,(
    l1_struct_0(sK9) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    l1_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f24,f97])).

fof(f97,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK9) ),
    introduced(choice_axiom,[])).

fof(f24,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',existence_l1_struct_0)).

fof(f234,plain,(
    spl11_22 ),
    inference(avatar_split_clause,[],[f147,f232])).

fof(f147,plain,(
    l1_waybel_9(sK8) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    l1_waybel_9(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f26,f95])).

fof(f95,plain,
    ( ? [X0] : l1_waybel_9(X0)
   => l1_waybel_9(sK8) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ? [X0] : l1_waybel_9(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',existence_l1_waybel_9)).

fof(f227,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f146,f225])).

fof(f146,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    l1_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f93])).

fof(f93,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK7) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',existence_l1_pre_topc)).

fof(f220,plain,(
    ~ spl11_19 ),
    inference(avatar_split_clause,[],[f111,f218])).

fof(f111,plain,(
    ~ v2_waybel_2(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f213,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f109,f211])).

fof(f109,plain,(
    l1_waybel_9(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f206,plain,(
    spl11_14 ),
    inference(avatar_split_clause,[],[f108,f204])).

fof(f108,plain,(
    v1_compts_1(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f199,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f107,f197])).

fof(f107,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f192,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f106,f190])).

fof(f106,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f185,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f105,f183])).

fof(f105,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f178,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f104,f176])).

fof(f104,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f171,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f103,f169])).

fof(f103,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f164,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f102,f162])).

fof(f102,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

fof(f157,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f101,f155])).

fof(f101,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).
%------------------------------------------------------------------------------
